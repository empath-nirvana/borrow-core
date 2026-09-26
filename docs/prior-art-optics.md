# Prior art: borrows as optics, and what optics are a manifestation of

This is a literature survey for issue #27 ("Experiment: borrows as optics with a lifetime-scoped
residual"). It records what other work establishes. It decides nothing. It does not repeat
`docs/prior-art-memory-model.md` (Q7: Aeneas backward functions, prophecies, Focus) or
`docs/prior-art-borrow-splitting.md` (laws L1–L5, RustBelt LftL-bor-split, Leaf, Marshall–Orchard,
Pure Borrow as a splitting precedent). Where it goes deeper on the same source, it says so.

**The hypothesis under test.** A borrow is a linear optic whose residual is held by the lender
for a lifetime:

| Row | Claim |
|---|---|
| H1 lens | `A ≅ V ⊗ (V ⊸ A)`: the borrower gets the focus `V`, the lender keeps the residual until `'a` ends |
| H2 mixed | `Imm` is a mixed optic whose focus is in a persistent (`!`) mode |
| H3 product | a family borrow is a product of lenses |
| H4 composition | reborrowing is optic composition |
| H5 prism | borrowing a variant payload is a prism |
| H6 traversal | `IterMut` / `split_at_mut` is a traversal |
| H7 time/scope | the residual is held for a bounded period (a lifetime) |
| H8 non-memory | handlers, arenas and locks are lenses onto resources other than memory |

After the user's scope update, the survey also asks what optics would be **one instance of**.
Two candidate layers are surveyed: a *spatial* one (residuation: `⊗ ⊣ ⊸`, `∗ ⊣ −∗`) and a
*temporal* one (well-bracketed protocols: sessions, acquire/release, prophecies). Adjoint logic
and polarity are weighed as a possible home for both.

**Citation conventions.** `[CONF]` and `[TR]` are Wagner et al. (2025) and its technical report.
Every claim about another work cites a section, definition, rule or figure from a full text that
was read, unless it is marked *(unverified)*. Remarks marked *(ours)* are this survey's reading,
not something a source prints. Sources are listed at the end.

---

## 0. Summary

**The short answer.**

- **Every optic shape in the hypothesis exists in the literature in a linear, non-cartesian
  form.** The linear lens `S → [A′,S′] ⊗ A`, products, composition, prisms, linear traversals and
  linear affine traversals are all printed with sections (§1).
- **What BoLo prints is already the lens with a wand for a residual, guarded by a lifetime.**
  `[TR]` 6.65 (Mut Frame) and 6.66 (Anti Frame) have exactly the shape of RustBelt's LftL-borrow
  and LftL-bor-acc. The residual is a magic wand under `[α]` (§4).
- **Nothing connects optics to lifetimes or borrowing.** No source ties an optic's residual to a
  lifetime, a lender, or a scope. No source frames `&T` as a mixed optic. No source states lens
  laws for borrows. Two sources call backward functions or `&mut` translations "lenses", both
  informally: Aeneas, and Ullrich's thesis (Electrolysis).
- **The residual held for a lifetime is printed, but in separation-logic and linear-types
  vocabulary, not optic vocabulary.** Instances: RustBelt's inheritance `[†κ] ⇛ ▷P`; Pure Borrow's
  `Lend α a ⊸ End α → a`; Aeneas's region abstractions, which its authors call "a form of magic
  wands"; RefinedRust's place context `ρ[blocked'a T]`.
- **For the deeper abstraction, the literature points to "residuation split in time".** RustBelt
  says LftL-borrow "splits ownership in time". Saffrich–Nishida–Thiemann's *ordered* partial
  monoid is the one printed algebra where a residual carries a temporal order. The adjoint and
  session-types family (Balzer–Pfenning acquire/release) supplies the protocol reading. It does
  not fit BoLo's static, lender-frozen, sequential setting without changes (§6).

---

## 1. Optics in monoidal and linear settings

### 1.1 Riley, *Categories of Optics* (arXiv 1809.00738)

- **Def 2.0.1.** An optic is `∫^{M} C(S, M⊗A) × C(M⊗A′, S′)` over any symmetric monoidal
  category (SMC). It need not be cartesian. Riley calls `M` the **residual**: "a kind of 'scratch
  space'; information from S that we need to remember to construct S′". The coend means "we
  cannot inspect this temporary information".
  - H1: this is the lens with an existential residual.
  - H7: this is the closest optic-side wording to "the lender holds something", but it gives no
    bound on when the residual is used.
- **Prop 2.0.3 (composition).** The composite of `⟨l|r⟩` and `⟨l′|r′⟩` is
  `⟨l;(M·l′) | (M·r′);r⟩`, so the residual of a composite is `M ⊗ M′`: residuals stack.
  Prop 3.0.8: lawful optics are closed under composition. This bears on H4.
- **Thm 2.0.12 (product).** Optic is symmetric monoidal, with
  `(S,S′)⊗(T,T′) = (S⊗T, S′⊗T′)`. Prop 3.0.9: `⊗` preserves lawfulness. This bears on H3.
- **Prop 2.0.4.** With finite products, optics are equivalent to Get/Put. The proof uses the
  diagonal. Remark 4.1.2: the closed structure on Lens "cannot be extended to non-cartesian closed
  categories".
- **§2.1 (Defs 2.1.4, 2.1.9; Thm 2.1.12).** Optic is the free *teleological* category. It "freely
  adds counit morphisms", which join a forward part to a backward part through "a 'formal
  counit' that traces out the object M". This is the only structural hint of "discharged later"
  (H7). Lifetimes do not appear.
- **§3, Def 3.0.2 (lawfulness in general).** An optic is lawful when `outside(p) = id` and
  `once(p) = twice(p)`. Riley rejects "constant complement" because it is not invariant under the
  coend (§3 intro).
- **§4.4, Thm 4.4.1 (coalgebraic optics).** If `−·A` has a right adjoint `R_A`, then
  `Optic ≅ C(S, (R_{A′}S′)·A)`. The canonical representative uses the **counit** of that
  adjunction. A lawful optic is a coalgebra for the comonad `X ↦ (R_A X)·A`.
- **§4.8 (linear lenses).**
  - Riley: "If C is closed monoidal but not necessarily cartesian, … linear lenses …
    `Optic⊗((S,S′),(A,A′)) ≅ C(S, C(A′,S′) ⊗ A)`."
  - Riley: "We cannot possibly use the three Put/Get style lens laws in this setting as we lack
    projections."
  - **Prop 4.8.1** replaces them with laws on `Unzip : S → [A′,S′] ⊗ A`:
    - (Rezip) `ev ∘ Unzip = id_S`
    - (ZipZip) `(coev ⊗ A) ∘ Unzip = ((Unzip ∘ −) ⊗ A) ∘ Unzip`
  - Riley notes that this rederives Gibbons–Johnson §3.2 and that "cartesianness was not
    required". **This is the linear costate-coalgebra account, and the formal home of H1.**
- **Def 4.2.1 (prism).** Optic for `⊔`, `≅ C(S, S′⊔A) × C(A′,S′)`. The residual is the complement
  summand and does not depend on the tag (H5).
- **Def 4.6.3 (traversal).** Defined in **Set** only, for the action of Traversable functors.
  §4.10 gives affine traversals for cartesian closed categories with coproducts only. **Riley
  defines no linear traversal** (H6).
- **§6.1, Def 6.1.1 (mixed optics).** `∫^{M} C_L(S, M·A) × C_R(M·A′, S′)`. Riley: "It is not so
  clear what notion of lawfulness is appropriate in this setting." This bears on H2.

### 1.2 Clarke, Elkins, Gibbons, Loregian, Milewski, Pillmore, Román, *Profunctor Optics, a Categorical Update* (arXiv 2001.07488; Compositionality 2024)

- **§2, Def 2.1 (mixed optics).** A monoidal category `M` acts on `C` and on `D`, and an optic is
  `∫^{M} C(S, M ▷ A) ⊗ D(M ▷ B, T)`. The construction is V-enriched, so no cartesian base is
  needed. Fig. 6 tabulates adapter, lens, monoidal lens, algebraic lens, monadic lens, linear
  lens, prism, coalgebraic prism, grate, glass, affine traversal, traversal, kaleidoscope, setter
  and fold.
- **Def 3.3 / Prop 3.4 (monoidal lens).** `CCom(US, A) × C(US⊗B, T)`: the *view is a
  commutative-comonoid homomorphism*. The focus is read in the copyable part, and the update is
  linear. **This is the nearest printed object to H2** ("`Imm` as a mixed optic whose focus is in
  a persistent mode"). Spivak, arXiv 1908.02202, Def 2.9 is the same idea: lenses in an SMC whose
  get part is a comonoid morphism.
- **§3.1.5, Def 3.14 / Prop 3.15 (linear lens).** `C(S, [B,T] • A)`, "we do not need to require
  our enriching category to be cartesian". The proof uses the adjunction `(−⊗B) ⊣ [B,−]` and
  then Coyoneda.
- **Def 3.16 / Prop 3.17 (prism).** Remark 3.18 covers prisms in an SMC.
- **§3.2, Def 3.20 / Prop 3.22 (traversal).** `C(S, ∫^{n} Aⁿ ⊗ [Bⁿ, T])` in a symmetric monoidal
  closed category with countable coproducts. **This is a genuinely linear traversal** (H6): the
  focus is `n` separate `A`s together with a residual that takes back `n` `B`s. On length
  preservation the paper says "This restriction can be also encoded into the type when dependent
  types are available."
- **Def 3.24 / Prop 3.25 (affine traversal).** `C(S, T + A⊗[B,T])`: a linear lens composed with a
  linear prism. This is the shape of borrowing a variant's field (H5 ∘ H1).
- **Defs 3.33–3.34.** Getters, reviews and folds are degenerate mixed optics.
- **Kaleidoscopes** (Remark 3.28) "cannot be composed with lenses".
- **§4 (representation).** Optic is the Kleisli category of the Pastro–Street promonad (§4.3).
  Thm 4.14 is the profunctor representation over Tambara modules.
- **Prop 5.2.** The van Laarhoven form of the linear lens:
  `∫_{F} V(A, FB) ⊗ V(S, FT)`.
- **§5.2–§5.3.** Lawfulness of mixed optics is left open.

### 1.3 Dependent optics: the residual depends on the position

- **Vertechi, *Dependent Optics* (arXiv 2204.09547, ACT 2022).**
  - Def 1: the residual is a 1-cell `f ∈ B(A,B)` over a base. Mixed optics are the case
    `B = BM` (Prop 1).
  - **§3.3: dependent prisms over cospans.** This is the most direct printed framework in which
    a prism's residual can depend on the tag. That matters for H5 because a payload borrow must
    remember *which* variant it came from.
- **Braithwaite, Capucci, Gavranović, Hedges, Rischel, *Fibre Optics* (arXiv 2112.11145).** §3–4:
  residuals live in fibres. The paper aims at "a general mathematical theory of optics with
  'linear' dependent types".
- **Niu & Spivak, *Polynomial Functors* (arXiv 2312.00990).**
  - Def 3.1: a dependent lens `p → q`, whose backward part depends on the forward position.
  - §3.2 reads "dependent lenses as interaction protocols". Ch. 4 reads dynamical systems as
    lenses, so a lens is one step of an interaction over time. This is the only printed
    optic-as-protocol reading found (H7).

### 1.4 Optics, time and scope

- **Capucci, Gavranović, Hedges, Rischel, *Towards Foundations of Categorical Cybernetics*
  (arXiv 2105.06332).** §3, Def 8: the residual is "the intermediate state M", saved by the
  forward pass and consumed once by the backward pass.
- **Capucci, Gavranović, Malik, Rios, Weinberger (arXiv 2403.16388, MFPS 2024).**
  - §1: fibrations induce "a natural 'arrow of time'".
  - §3.3, Def 3.4: the residual is "explicitly 'written' in the forward part and 'read' in the
    backward part".
- **Hedges, *Coherence for lenses and open games* (arXiv 1704.02230).** §5, Def 5.1 introduces
  teleological categories. §1: "co-states … in the monoidal category of lenses turn out to be
  continuations".
- **O'Connor (arXiv 1103.2841), §2.2; Gibbons & Johnson (BX 2012), §3.2.** Lenses are coalgebras
  for the store (costate) comonad. Both are cartesian. The linear version is Riley Prop 4.8.1.
- **Abou-Saleh, Cheney, Gibbons, McKinna, Stevens, *Reflections on Monadic Lenses* (arXiv
  1601.02484).** Def 2.1. Cartesian throughout.
- **Not found.** No "temporal optics", no lenses indexed by worlds or stages, and no optic whose
  residual must be used within a bound. Linearity gives "exactly once" (Riley §4.8). A lifetime
  bound has no counterpart in this literature.

### 1.5 Linear optics in code

- **linear-base, `Control.Optics.Linear`** (Haskell).
  - `lens :: (s %1-> (a, b %1-> t)) -> Lens s t a b`: Riley §4.8's form.
  - A Prism is `Strong Either Void`, and `traversal` is the linear Applicative form.
  - **`setSwap :: … -> s %1-> b %1-> (a, t)`** has the shape of our `withswap` and of
    `mem::replace`.
  - `get` goes through a non-linear path, so a linear get alone is not available.
- **Milewski, "Linear Lenses in Haskell"** (blog, 2024): "a linear lens … leaves you with the
  obligation to consume both the setter `b %1-> t` and the focus `a`. You can't just extract `a`
  alone." *(Read through a fetch summary.)*
- **Bernardy et al., *Linear Haskell* (POPL 2018).** No lenses. §7.2 proposes a borrow
  multiplicity with `borrow :: (T →β Unrestricted a) →β Unrestricted a`, "making the life-time
  manifest in the structure of the program". This is a CPS borrow close to `withbor`.
- Idris 2 QTT lenses: no source located *(unverified)*.

---

## 2. Borrows explicitly framed as lenses

| Source | What is printed | Rows |
|---|---|---|
| **Ullrich**, *Simple Verification of Rust Programs via Functional Purification* (MSc thesis, KIT 2016), §6.1–6.4 | "a mutable reference … can [be] represented by lenses". It has `lens.comp`, "one lens per projection, then compose", and a partial `lens.index`. Dereferencing a `&mut` composes lenses, "also known as 'reborrowing'". No laws. | **H1, H4** stated as a design; the only source found that does so |
| **Aeneas**, Ho & Protzenko, ICFP 2022, §2 | "akin to lenses … except we propagate the output back to possibly-many inputs"; `list_nth_mut` "get"s and "put"s | H1 (informal) |
| Aeneas, §4.1 | region abstractions "are a form of magic wands"; ending one runs the backward function | **H7** in wand vocabulary |
| Aeneas, §4.1 | "forbid changing the enum variant of o, while its value or one of its fields is borrowed" | H5 (tag frozen in the lender) |
| Aeneas library, GitHub `main` (read 2026-09-26) | `list_nth_mut : Result (T × (T → CList T))`, whose residual closure captures the constructor and the tail (the one-hole context). `split_at_mut`'s back concatenates only when lengths are preserved. `IterMut` is `opaque`, with a hand-written back. | H1 in costate form; H5 as an affine traversal (fails forward on the wrong variant); H6 hand-modelled with a shape law |
| Aeneas, Ho, Fromherz, Protzenko, ICFP 2024, §5.2 | loop fixpoints over region abstractions; the accumulated residual of a reborrow chain | H4, H7 |
| Fromherz, UQAM slides (2025) | slide "Forward and backward functions behave like lenses" | H1 (informal) |
| **RustHorn** (Matsushita, Tsukada, Kobayashi; ESOP 2020, full version) | §1.2: `&mut` as `⟨a, a∘⟩` (current, final). §3.4, Ex. 4: subdivision `xs∘ = [x∘|xs∘′]`. App. B: `match *x` at a sum sets `x := ⟨inj_i x*, inj_i x∘⟩`, the same tag at the end. §5: Electrolysis is "static tracking of addresses based on lenses". | H1 via prophecy; **H5: the final value keeps the tag** |
| **RustHornBelt** (PLDI 2022) | §2.3: `⌊IterMut⌋ = List(⌊T⌋×⌊T⌋)`, "an elementwise split … the length … is guaranteed to stay constant" | **H6 with a shape law** |
| **RefinedRust** (Gäher et al., PLDI 2024) | §5.2–5.3, Fig. 11 `chk-mut-bor`: "ρ[·] … a place type context … with a hole". The lender holds `fill(ρ[·], blocked'a T)`. §2.3: `get_unchecked_mut` resolves the lender to `<[i:=*γ_i]> xs`. | **H1 + H7**: the lender holds the one-hole context blocked for `'a`. The most literal printed form. |
| **RustBelt** (POPL 2018), rule F-case-bor and `option_as_mut` | borrow of a sum → borrow of the payload; the tag is not writable | H5 (no write-back law) |
| **Hylo** (language tour, "Subscripts"); **Racordon et al.** (JOT 2022), §3 | subscripts `yield` a projection, and code after `yield` runs when it ends; `inout` is copy-in/copy-out | H1 + H7 as a coroutine |
| **Swift SE-0474** "Yielding accessors" | a yield-once coroutine. "Exclusive access … extends for the duration of the accessor's execution, including its suspension." The yield-once rule makes the resumption linear. | **H1 + H7**: the residual is the suspended coroutine |
| **Marshall & Orchard** (OOPSLA 2024), rule `with&`, §5.1 | `withBorrow`, with laws `withBorrow id ≡ id` and `withBorrow (f∘g) ≡ withBorrow f ∘ withBorrow g` | **the setter/"over" laws for a borrow**: the nearest thing to lens laws |
| **lens-rs** crate (guide) | `view_mut -> &mut`, `preview_mut -> Option<&mut>`, `traverse_mut -> Vec<&mut>` | H1, H5, H6 in code; the residual is held implicitly by rustc |
| Rust field projections (project goal 2025h2; RFC PR #3735, not read in full); Matsakis, "View types" (2021) | projections `C<T> → C<F>`, with enum projection as future work; view types are restricted borrows of the whole | none in optic terms |
| **Lorenzen, Leijen, Swierstra, Lindley** (PLDI 2024), §2.2, §3.2 | zippers as one-hole contexts. Minamide's hole calculus: "x points to the top … h … to the hole", and the context is affine. | H1: the residual as a one-hole context |

**Not found.**

- Lens laws (GetPut, PutGet, PutPut, or Riley's Rezip/ZipZip) stated for borrows.
- `&T` framed as a mixed optic.
- A family borrow framed as a product of lenses.
- `IterMut` framed as a traversal in optic vocabulary.
- An arena, lock or handler framed as a lens.

---

## 3. Separation logic: the residual as a wand

- **RustBelt lifetime logic.** Jung, PhD thesis 2020, ch. 11, Fig. 11.1, p. 142.
  - **LftL-borrow:** `▷P ⇛ &κ_full P ∗ ([†κ] ⇛ ▷P)`.
    - The thesis calls it "really the core rule". It splits `P` into a full borrow and an
      **inheritance**: "keep ownership of the inheritance for ourselves".
    - The POPL paper, §5.1: it "splits ownership in time"; the `∗` is "disjointness in time".
    - **This is H1 + H7 verbatim:** the lender keeps a residual that fires when `κ` is dead.
  - **LftL-bor-acc** (derived, Fig. 11.1):
    `&κ P ∗ [κ]_q −∗ |⇛ ▷P ∗ (▷P −∗ |⇛ &κ P ∗ [κ]_q)`.
    - This is **a get with a put-back wand**.
    - The put-back is mandatory, because the lifetime token must come back.
  - **LftL-bor-acc-strong** (Fig. 11.8, p. 155): the caller may put back a different `Q`, given
    `▷(▷Q ∗ [†κ′] ⇛ ▷P)`. This is a **type-changing lens** whose conversion may assume the
    lifetime is dead.
  - **LftL-reborrow:** `κ′ ⊑ κ ∗ &κ P ⇛ &κ′ P ∗ ([†κ′] ⇛ &κ P)`. The same shape one level up; the
    residual is the outer borrow (H4).
- **Iris accessors.** Jung thesis §5.6, pp. 70–72.
  - `inv-acc`: `inv P ⊢ |⇛ ▷P ∗ (▷P −∗ |⇛ True)`.
  - The general pattern is `∃x. P₁ ∗ (∀y. P₂ −∗ Q₂)`: a polymorphic `(s,t,a,b)` lens. The
    symmetric accessor `Q ∝ P` is the monomorphic lens.
  - The thesis calls accessors "a design pattern" and proves no general theory of them.
- **Hobor & Villard, *The Ramifications of Sharing in Data Structures* (POPL 2013).**
  - §3.3, rule **RAMIFY:** from `{P} c {Q}` and `R ⊢ P ∗ (Q −∗ R′)`, conclude `{R} c {R′}`.
  - **This is a type-changing lens in pure SL: focus `P`, residual `Q −∗ R′`.**
  - Thm 8.1: RAMIFY and FRAME are inter-derivable. Lemma 8.1: `P ∗ (Q −∗ R′)` is the weakest
    precondition.
  - Nothing about lifetimes.
- **Charguéraud.**
  - ICFP 2020 pearl, §7.3, Lemma 7.6 (ramified frame).
  - CPP 2016, §1 and §5.3: `peek`'s spec returns `x ⇝ R X ⋆ (x ⇝ R X −⋆ p ⇝ Queue…)`, a lens get
    with a wand residual. Charguéraud records the limitation that the queue is unusable until the
    wand is applied. In effect this is a borrow with no lifetime.
- **Cao, Wang, Hobor, Appel, *Magic Wand as Frame* (arXiv 1909.08789), §2.4.** WANDQ-FRAME-VER is
  residual composition and WANDQ-FRAME-HOR is the tensor of residuals, i.e. H4 and H3 at the
  level of wands.
- **Leaf** (Hance et al., OOPSLA 2023).
  - §7 defines the guard as a quantification over focus-plus-residual decompositions:
    `P ⤔̂ Q ≜ … ∀R. (P ∗ (P −∗ Own ∗ R)) −∗ ◇(Q ∗ (Q −∗ Own ∗ R))`.
  - §7 notes that `A ⊢ P` "does not in general imply A can separate into P ∗ (P −∗ A)", and
    proves Split-Own for the case where it can. **This pins down when the lens decomposition
    `P ⊣⊢ Q ∗ (Q −∗ P)` is available at all.**
- **Wadler, *Linear Types Can Change the World!* (1990), §4, rule `let!`.**
  - A scoped read-only borrow of `x : T`. The side condition "U safe for T" stops the view from
    escaping, and hyperstrict evaluation of the body is required.
  - §6: "Girard's Linear Logic contains nothing like the 'let!' construct. Is there a nice
    theoretical justification for this construct?"
  - Odersky's *Observers* (ESOP 1992) was checked from the abstract only *(unverified)*.
- **Spiwack et al., *Linearly Qualified Types* (ICFP 2022).**
  - §4.2.1 `lendMut`: a CPS borrow returning the capability.
  - §4.2.2 `split`/`join`: `Slices n l r` is a residual constraint that behaves like
    `RW l ∗ RW r −∗ RW n` (H3, H6 for arrays).
- **Pure Borrow** (Matsushita & Ishii, 2026), §3.1–3.2.
  - `borrow :: a ⊸ (Mut α a, Lend α a)` and `reclaim :: Lend α a ⊸ End α → a`: **the residual as
    a first-class linear value**, dischargeable only with a dead-lifetime token.
  - `reborrowing :: Mut α a ⊸ (∀β. Mut (β∧α) a ⊸ BO (β∧α) r) ⊸ BO α (r, Mut α a)` is close to
    BoLo's third `withbor` axiom.
  - The related work says "first-class lenders are quite underexplored" and cites Wagner et al.

---

## 4. The magic-wand connection, where the optic view meets BoLo

**BoLo already prints the lens-with-wand.** BoLo's logic has the wand (`[TR]` def. 5.36:
`P₁ –⋆ P₂ (ρ) ≜ ∀ρ₁,ρ₂. P₁(ρ₁) ⇒ ρ ● ρ₁ = ρ₂ ⇒ P₂(ρ₂)`, `Fig16.BoLo.wand`). The three frame rules
of `[TR]` §6.3 (`Paper/S6_3_FrameAndAntiFrame/Lemmas.lean`, all `[as printed]`) are:

    6.64 Imm Frame   ℓ ↦ v ⋆ P̂(v) ⋆ (Иα. Imm α P̂ –⋆ wp(e){[α](ℓ ↦ v –⋆ P̂(v) –⋆ Q̂)})  ⊨ wp(e){Q̂}
    6.65 Mut Frame   ℓ ↦ v ⋆ P̂(v) ⋆ (Иα. Mut α P̂ –⋆ wp(e){[α] ∀v′. ℓ ↦ v′ –⋆ P̂(v′) –⋆ Q̂}) ⊨ wp(e){Q̂}
    6.66 Anti Frame  ℓ ↦ Mut α P̂ ⋆ (∀v. ℓ ↦ v –⋆ P̂(v) –⋆ wp(e){∃v. ℓ ↦ v ⋆ P̂(v) ⋆ (ℓ ↦ Mut α P̂ –⋆ Q̂)}) ⊨ wp(e){Q̂}

Reading these as optics *(ours)*:

- **6.65 is a lens split with a lifetime-guarded residual.**
  - The owner `ℓ ↦ v ⋆ P̂(v)` is split into a focus `Mut α P̂` and a residual.
  - The residual is `∀v′. ℓ ↦ v′ –⋆ P̂(v′) –⋆ Q̂`: "give me back the cell at any `v′` satisfying
    `P̂`".
  - The residual is available only under `[α]`, i.e. once `α` is over. That is the `V ⊸ A` of H1,
    in the form `Q –∗ P`, with the time bound of H7 carried by `[α]` and the fresh-name
    quantifier `Иα`.
  - This is RustBelt's `▷P ⇛ &κ P ∗ ([†κ] ⇛ ▷P)` in BoLo's terms. It is also Pure Borrow's
    `Lend α a`, except that the lend is not a value: it is the postcondition's wand.
- **6.64 is the same with `Imm`.**
  - The residual `ℓ ↦ v –⋆ P̂(v) –⋆ Q̂` is at the **same** `v`. No update can happen, so the put
    is the identity.
  - That makes 6.64 a getter (Clarke et al. Def 3.33) whose focus is copyable (`copy`,
    `forget`). It is the "monoidal lens with the view in the comonoid part" of Clarke Def 3.3,
    read in time. This bears on H2.
- **6.66 is an accessor: open, use, close.**
  - It opens a `Mut α` borrow to `ℓ ↦ v ⋆ P̂(v)` and requires closing with
    `∃v. ℓ ↦ v ⋆ P̂(v) ⋆ (ℓ ↦ Mut α P̂ –⋆ Q̂)`.
  - That is LftL-bor-acc, or Iris's symmetric accessor. It is also what `withswap` exposes at the
    term level:
    `withswap : Mut @a A ⊸ (A ⊸ A ⊗ B) ⊸ Mut @a A ⊗ B`.
  - That type is the van Laarhoven linear lens (Clarke Prop 5.2) at the one functor `F = − ⊗ B`,
    and it matches linear-base's `setSwap`.

**Where the term level differs from the optic form** *(ours)*.

- `withbor : Ref A ⊸ (∀'x ⊏ @b. Mut 'x A ⊸ ['x] B) ⊸ Ref A ⊗ B` never hands the residual to
  anyone. The combinator's frame keeps it. In the typed world it is a frame record `FrameRec`
  (`Core/FrameRecords.lean`: location, value, payload resource, type).
- So BoLo is in **continuation-passing, or "closed", form**. The existential residual `M` of
  Riley's Def 2.0.1 is hidden by the rank-2 lifetime quantifier `∀'x`, not by a coend.
- The costate form `S → [V,S] ⊗ V` is not a BoLo type. It would need `Lend 'x A` as a first-class
  type, as in Pure Borrow.
- The existing literature prefers the CPS form exactly where leak freedom matters. Rust's scoped
  threads went from a guard (unsound, "leakpocalypse") to a closure-scoped API (RFC 3151).

**Consequence for the experiment** *(ours)*. The optic abstraction can be stated over what `Core`
already has, without a new type:

- the continuation form (`withbor`);
- the accessor form (`withswap`, i.e. 6.66);
- the three frame rules as the semantic lens laws.

A first-class residual type would be a model change, and is not needed to test H1–H4.

---

## 5. Prisms and traversals under linearity (H5, H6)

- **Linear prisms exist.** Clarke Def 3.16 and Remark 3.18. The residual does not remember the
  tag. The dependent version (Vertechi §3.3) makes the tag part of the base.
- **Borrowing a payload keeps the tag in the lender in every source read.**
  - RustBelt F-case-bor.
  - Aeneas §4.1: "forbid changing the enum variant".
  - RustHorn App. B: `inj_i` on the final value.
  - The Aeneas library's residual closure `fun t => CCons t tl`.
  - In optic terms the lender's residual is `V ⊸ inj_i V`, the prism's `review`. The payload
    borrow is therefore a *prism used as a lens after a successful match*: an affine traversal
    (Clarke Def 3.24) with the tag fixed on the way back.
- **Linear traversals exist.**
  - Clarke Def 3.20 / Prop 3.22 in any symmetric monoidal closed category with countable
    coproducts.
  - In code: linear-base.
  - Borrowing sources add a **shape law** that the traversal form does not have: RustHornBelt
    §2.3 (length constant), Aeneas `split_at_mut` (lengths preserved). Clarke §3.2 notes this
    needs dependent types.
- **Where BoLo stands** *(ours; from the repository, not the literature)*.
  - **Read-only side.** `Imm̲` distributes over `⊕` and `⊗`, and `Imm̲` at `μ` is structural
    (`VTy.immReborrow`, `Core/Types.lean`).
    - So a read-only prism (preview) is `withload` + `case`.
    - A read-only traversal (fold) is `foldImm` (`Core/FoldImm.lean`), a typing rule under
      `fundamentalC`.
    - H2's read-only optics are therefore already present.
  - **Modify-style traversal.** Copy-in/copy-out over `withswap` exists: `Core/MapMut.lean`,
    and `foldReuse` in place.
  - **Mut prism at a fresh lifetime, boxed payload** (`Mut @a (Ref A ⊕ Ref B)`).
    - The route: `withswap` out the sum, `case`, `withbor` the payload's `Ref` inside the swap
      function, rebuild `inl`/`inr`.
    - This looks derivable from existing rules, like the fresh-lifetime L3 route in
      `prior-art-borrow-splitting.md` §5.2. It has **not been typed or run**.
  - **Mut prism for an unboxed payload.** Needs the payload to be a place. `SPEC.md` §5 lists
    "variants in place" as open.
  - **Same-lifetime payload views.** A same-lifetime `Imm` projection through a pointer is
    refuted at the typed world (`experiments/Projection`, `no_view_at_tag`). Same-lifetime prisms
    would meet the same tag discipline. I have not derived this and have not verified that any
    obstruction to a same-lifetime prism is real.
  - **Traversal handing out many `Mut 'x` at once.** For statically shaped blocks this is
    `withborS` (a product). For dynamic length it is L2 / `split_at_mut`, a stretch goal
    (`docs/decisions.md` 5).

---

## 6. Candidate underlying abstraction

The user's scope update asks what optics, read as borrows, are a manifestation of. Each candidate
is below, with what the literature supports and what is speculation.

### 6.1 Optics alone

- **For.**
  - Every row H1–H6 has a linear, printed optic.
  - Composition and product come with lawfulness preservation (Riley Props 3.0.8, 3.0.9).
  - Optics are already used for non-memory things: games, learners, Bayesian inference (Riley
    §6.4; categorical cybernetics §4–6). That weakly supports H8 as "a residual is a
    continuation, not a cell".
- **Against.**
  - Optics have no notion of *when* the residual is used (§1.4 "Not found").
  - Mixed optics, the natural home of `Imm`, have no settled lawfulness (Riley §6.1; Clarke
    §5.2–5.3).
  - Optics say nothing about leak freedom.
  - The optic form is the external view of a borrow. It does not explain why the lender is
    frozen.
- **Verdict.** Optics are an adequate *interface* but not the explanation.

### 6.2 Residuation alone (spatial)

- **For.**
  - A linear lens is a factorisation of `S` through evaluation `V ⊗ (V ⊸ S) → S`. Riley §4.4 and
    §4.8 say this with the counit named: Rezip is `ev ∘ Unzip = id`.
  - In separation logic the same thing is `P ⊢ Q ∗ (Q −∗ P')`: RAMIFY (Hobor–Villard §3.3),
    inter-derivable with FRAME (Thm 8.1).
  - `∗ ⊣ −∗` is a residuated pair on the resource monoid (Calcagno–O'Hearn–Yang, Def 2; BI).
  - Leaf §7 characterises when the decomposition exists.
  - So H1, H3 (tensor of wands, Cao et al. HOR) and H4 (composition of wands, VER) are all
    residuation facts.
- **Against.**
  - Residuation is timeless. `P ∗ (P −∗ A)` does not say the lender cannot touch `A` until the
    wand is applied. Charguéraud (CPP 2016) records the resulting problem: the structure is
    frozen with no way to say for how long.
  - Residuation alone does not give H7.

### 6.3 Residuation plus a well-bracketed protocol (spatial + temporal)

**The supporting literature.**

- **RustBelt, POPL 2018, §5.1:** LftL-borrow "splits ownership in time". The residual
  `[†κ] ⇛ P` is residuation guarded by a lifetime's death.
- **BoLo 6.65:** the same, with `[α]` as the guard (§4 above).
- **Pure Borrow §3.1:** the guard as a linear type, `Lend α a ⊸ End α → a`.
- **Saffrich, Nishida, Thiemann, *Law and Order for Typestate with Borrowing* (OOPSLA 2024).**
  - §1: `split : Handle[m₀] ⊸ Handle[m₁] ⊙ Handle[m₂]` with `m₁·m₂ ⊆ m₀`. The product `⊙` is
    **ordered**: "the borrow bh is processed to the end before resuming operations on h".
  - §2.1, Def 2.1: an ordered partial monoid.
  - The admissible `m₂` is a Lambek-style residual (`m₂ ≤ m₁\m₀`, *ours*; the paper does not say
    "residual").
  - Instances include "the classic borrow" and a read-only reborrow.
  - **This is the one printed algebra where the residual carries a temporal order.**
  - The follow-up, Saffrich, Spaderna, Thiemann, Vasconcelos, *Borrowing from Session Types*
    (OOPSLA 2025), uses ordered linear typing for session channels, per its abstract
    *(sections unverified)*.
- **Dreyer, Neis, Birkedal (ICFP 2010), §5–§5.1.**
  - Well-bracketed control justifies "private transitions".
  - The motivating example is the `withbor` shape: a local is set around a callback and
    restored, and "whenever x is set to 0, it will eventually be set to 1 — no matter what the
    callback does".
  - **This is the semantic content of lexical lifetimes.** It holds only because control is
    well-bracketed (no `call/cc`).
- **Prophecies as the temporal dual.**
  - RustHorn §1.2 and RustHornBelt §2.2: `&mut` = (current, final), with the frozen lender
    `†α` reading the final value back.
  - No source calls the prophecy the dual of the lender's residual. *(ours)*: a prophecy is the
    residual's *output* named in advance; the wand is the residual's *input* awaited. They are
    two views of one exchange.
- **Session types.**
  - Caires–Pfenning (CONCUR 2010), §3, Def 3.1: `A ⊗ B` sends then continues, `A ⊸ B` receives
    then continues.
  - Wadler, CP (JFP 2014), §3.
  - So `V ⊗ (V ⊸ 1)` reads "send `V`, receive `V` back, end". **No paper prints a borrow as this
    session type.**

**Verdict** *(speculation)*. This is the strongest candidate the literature supports:

- a **residuated** resource structure (the lens, spatially);
- **ordered in time** by a well-founded, well-bracketed discipline (the lifetime);
- with optics as the external, stateless view of one bracketed exchange.

### 6.4 Adjoint logic, polarity and sessions as the home

The coordinator's citations were checked, and all exist as given:

- **Pruiksma & Pfenning, *A Message-Passing Interpretation of Adjoint Logic*.** PLACES 2019,
  EPTCS 291:60–79 (arXiv 1904.01290); journal version JLAMP 120 (2021).
  - §2: modes carry structural properties (W, C), and shifts `↑`/`↓` change mode.
  - In the multicut semantics, weakening is cancellation and contraction is multicast.
  - §4: session fidelity, deadlock freedom and "leaves no garbage", a leak-freedom corollary of
    the same structure.
- **Balzer & Pfenning, *Manifest Sharing with Session Types*, PACMPL 1 (ICFP 2017).** Read
  against TR CMU-CS-17-106R, whose numbering may differ.
  - §3.1–3.2: acquire `↑ˢₗ` and release `↓ˢₗ` are adjoint shifts between a shared layer and a
    linear layer.
  - §3.3: **equi-synchronizing**, "any release restores the session to the same type at which a
    preceding acquire occurred". This is the analogue of `withbor` returning `Ref A`.
- **Balzer, Toninho & Pfenning, *Manifest Deadlock-Freedom for Shared Session Types*.** ESOP 2019,
  LNCS 11423.
  - §3: *worlds* with a partial order, and each process has a range of worlds it may acquire.
  - §5.2, Thm 5.6: progress.
  - Structurally this parallels lifetime stratification: a well-founded order that keeps
    acquisitions nested. It serves a different purpose, deadlock rather than outlives.
- **Cut-as-tree and deadlock freedom.**
  - Caires–Pfenning Thm 5.8 (global progress).
  - Wadler CP, where cut elimination gives deadlock freedom.
  - **Jacobs, Balzer, Krebbers, *Connectivity Graphs* (POPL 2022), §3.1, Thm 3.2.** The final
    state is `h = ∅ ∧ ∀i. eᵢ = ()`, so **one theorem gives both deadlock freedom and memory-leak
    freedom**, from acyclicity.
  - Jacobs & Balzer, *Higher-Order Leak and Deadlock Free Locks* (POPL 2023), §4, Thm 4.1: the
    same for locks. §1 shows Rust mutexes leaking.
  - *(ours)*: BoLo's adequacy, "run to `()` with empty memory", has the same form as Jacobs et
    al.'s `final`. Their acyclicity plays the role of BoLo's nested lifetimes plus linearity.
- **Sessions in a memory setting.**
  - Pruiksma & Pfenning, *Back to Futures* (JFP 2022), §3–4: the same logic with write-once
    shared-memory cells.
  - Rocha & Caires, *Propositions-as-Types and Shared State* (ICFP 2021): mutable cells in a
    session calculus *(abstract only)*.
  - Caires, *CLASS* (PLACES 2025): cells follow `(take;put)*;drop`, and a shared `take` acquires
    a mutex released by `put`.
  - The CLASS protocol is the lens protocol as a session *(ours)*. CLASS's `share` "is not a
    static scoping construct".
  - Chen, Balzer, Toninho, *Ferrite* (ECOOP 2022): shared sessions embedded in Rust. It does not
    model sessions as Rust borrows.

**Weighing the proposed framing.** The framing is: "adjoint logic read as communication. Resources
are exchanged along polarized connectives; borrowing is acquire/release mode shifts; lifetimes are
the well-founded ordering keeping exchanges well-bracketed; optics are the external view of one
exchange."

**Where it fits.**

- Under polarity, `V ⊗ (V ⊸ A)` is "lend, then take back".
- Equi-synchronization is "returned at the same type".
- Worlds are a well-founded order on acquisitions.
- Jacobs et al. and Pruiksma–Pfenning derive leak freedom from the same tree or acyclicity
  invariant that gives deadlock freedom.
- Optics as "the external view of one exchange" matches Niu–Spivak's "dependent lenses as
  interaction protocols" (§3.2).

**Where it does not fit** (all from the sources above):

1. **Exclusion.** Shared-mode exclusion is *dynamic*: other clients block. BoLo's is *static*:
   the lender is frozen for `α`. In Balzer–Pfenning the shared channel "is still available to the
   continuation".
2. **Scope.** Acquire is not lexically scoped. Neither is CLASS's `share`.
3. **Read sharing.** `Imm` sharing is a *contraction mode* (σ ⊇ {C}) in adjoint terms, not an
   acquire. So `Imm` and `Mut` would be two different adjoint phenomena, a mode and a shift.
   *(ours)*
4. **Purpose of the order.** Worlds order acquisitions against deadlock. Lifetimes order
   *validity* through outlives, which is a different obligation.
5. **Setting.** These are process calculi. BoLo is a sequential calculus with a memory model. The
   bridge (Back to Futures, CLASS) gives write-once or protocol-typed cells, not a
   sequential mutable borrow with a frozen lender.

**Verdict** *(speculation)*.

- Adjoint logic is a credible *organising frame* for the modes: owned, `Imm` as a contraction
  mode, `!` as the fully structural mode, and shifts between them. BoLo's `!T` (`SPEC.md` §2) is
  already one such mode.
- It is not by itself the borrow. The borrow is the *temporal* part: a residual indexed by a
  lifetime, which an adjoint mode does not express.
- The better-supported synthesis: **residuation (the spatial split) + a well-bracketed temporal
  order (the lifetime) = a borrow**. Optics are its stateless external view, and adjoint modes
  classify what the focus may do while lent: copy (`Imm`), not copy (`Mut`), or anything (`!`).
- The literature does not state this synthesis. Its pieces are RustBelt §5.1,
  Saffrich–Nishida–Thiemann's ordered monoid, Dreyer–Neis–Birkedal §5, and Balzer–Pfenning §3.

### 6.5 Unification with handlers, locks, regions, iterators, async (H8)

- **Closest found.**
  - Jacobs–Balzer: locks and channels under one leak-and-deadlock theorem.
  - Saffrich et al.: borrowing, typestate and sessions under one ordered monoid.
  - Brachthäuser et al., *Effects, Capabilities, and Boxes* (OOPSLA 2022): second-class effect
    capabilities, with a `region` rule in the scoped-state extension (Fig. 4). This is scoped
    like a borrow, without a residual.
  - Swift SE-0474: an accessor as a yield-once coroutine, which is async-shaped.
- **Not found.**
  - Effect handlers as optics.
  - One abstraction covering borrows, handlers, iterators and async.
  - Staging as a scoped capability or lens. Refined environment classifiers (Kiselyov, Kameyama,
    Sudo, APLAS 2016) are analogous to lifetime inclusion *(unverified)*.
  - A formal account of scoped threads with borrows.
- *(ours)*: a deep effect handler is a residual-holding frame. The handler holds the
  continuation, as the lender holds the wand. `docs/decisions.md` 15 already makes a shallow
  handler one observation of codata. Whether the lens protocol and the handler protocol are the
  same bracket is untested.

---

## 7. Status table

| Row | Best prior art | Status |
|---|---|---|
| H1 lens `A ≅ V ⊗ (V ⊸ A)` | Riley §4.8, Prop 4.8.1; Clarke Def 3.14; RustBelt LftL-borrow / bor-acc; **BoLo `[TR]` 6.65, 6.66**; Ullrich §6.1 | **established**: the linear lens is printed, and BoLo's own frame rules have the shape |
| H2 `Imm` as mixed optic, focus persistent | Clarke Def 3.3 (view in comonoids), Def 2.1 (mixed); Spivak Def 2.9; BoLo 6.64 (identity put); Wadler `let!` | **plausible**: the objects exist; lawfulness of mixed optics is open (Riley §6.1, Clarke §5.3); nobody frames `&T` this way |
| H3 family borrow = product | Riley Thm 2.0.12, Prop 3.0.9; Cao et al. WANDQ-FRAME-HOR; Spiwack §4.2.2 `Slices` | **plausible**: the product exists in the optic and wand literature; not stated for borrows. In Core the family borrow is *derived* by nesting (composition plus `⊑`), not as a primitive product |
| H4 reborrow = composition | Riley Prop 2.0.3 (residual `M⊗M′`), 3.0.8; RustBelt LftL-reborrow; Ullrich §6.1 ("reborrowing"); Cao et al. VER | **established informally** (Ullrich, RustBelt); no law stated for borrows |
| H5 variant payload = prism | Clarke Def 3.16, 3.24 (affine traversal); Vertechi §3.3 (dependent prism); RustBelt F-case-bor; RustHorn App. B; Aeneas §4.1 | **plausible, refined**: every source keeps the tag in the lender, so the borrow is prism-then-lens with the tag fixed (an affine traversal), not a bare prism |
| H6 `IterMut` / `split_at_mut` = traversal | Clarke Def 3.20 / Prop 3.22 (linear traversal); RustHornBelt §2.3; Aeneas `split_at_mut`, `IterMut` (hand model) | **plausible**: linear traversals exist; borrowing adds a shape (length) law that plain traversals lack |
| H7 residual held for a lifetime | RustBelt §5.1 ("splits ownership in time"); BoLo 6.65 `[α]`; Pure Borrow `Lend α a`; RefinedRust `blocked'a`; SE-0474; Dreyer–Neis–Birkedal §5 | **established in SL and linear-types vocabulary; open in optic vocabulary** (no temporal optics found) |
| H8 non-memory resources as lenses | Riley §6.4 and cybernetics (non-memory optics); Jacobs–Balzer (locks); Balzer–Pfenning (acquire/release); CLASS `(take;put)*` | **open**: no source frames handlers, arenas or locks as lenses |

No row is contradicted by what was read.

---

## 8. What would be novel, and what already exists

**Already exists.**

- The linear lens, prism, traversal and affine traversal, with laws for the lens
  (Riley, Clarke et al.).
- The residual held for a lifetime, in separation logic (RustBelt), as a linear type
  (Pure Borrow) and as a place context (RefinedRust).
- Backward functions and costate-form translations of `&mut` (Aeneas).
- Borrow-as-lens as an informal design (Ullrich 2016; Aeneas).
- The functor laws of a scoped borrow (Marshall–Orchard §5.1).
- Well-bracketing as the reason local invariants survive a callback (Dreyer–Neis–Birkedal).
- One theorem for leak and deadlock freedom in session and lock calculi (Jacobs et al.).

**Would be new, if the hypothesis holds.** None of the following was found:

1. A borrow abstraction stated as a linear optic with the residual indexed by a lifetime, with
   lawfulness (Riley's Rezip/ZipZip or the modify laws) proved for it.
2. `Imm` given lawfulness as a mixed optic. This would also be a data point on a question the
   optics literature leaves open.
3. Payload borrows and traversals as instances of the same interface, with the tag and shape
   laws that borrowing needs.
4. All of it inside a calculus with a mechanised **leak-freedom** adequacy theorem, with the
   instances *derived* from existing typing rules (so `fundamentalC` covers them).
5. A statement that BoLo's frame rules 6.64–6.66 *are* the optic laws at the logic level. This is
   our reading and is unverified.

**Would not be new.** Calling a mutable borrow a lens, calling the lender's residual a wand, or
calling reborrowing composition. Each has a printed precedent above.

---

## 9. Recommended Lean experiment: "lift without breaking the FP"

The literature points to one formulation. State the optic in the **continuation (CPS) form**
BoLo already uses, not the costate form, and use the **modify/accessor** laws, not Get/Put.
The reasons:

- Riley §4.8: no Get/Put without projections.
- Milewski: "can't extract `a` alone".
- Marshall–Orchard §5.1 gives the modify laws for a borrow.
- 6.66 and `withswap` are the accessor form.
- A costate form would need a first-class `Lend` type, which is a model change.

**Stage 1. An interface over `Core`, no new rules** (`experiments/Optics/`).

```
structure MutLens (S V : VTy) where
  -- continuation form, lifetime-polymorphic: a derived CDerives term of type
  --   S ⊸ (∀'x ⊏ @b. Mut 'x V ⊸ ['x] T) ⊸ S ⊗ T          for every T (with T ⊐ side conditions)
  run    : ∀ T, CDerives … (lensTy S V T)
  -- accessor form, derived from `run` + `withswap`:
  --   Mut @a S ⊸ (V ⊸ V ⊗ T) ⊸ Mut @a S ⊗ T
  over   : ∀ a T, CDerives … (overTy a S V T)
```

Instances, each a closed `CDerives` derivation, so `fundamentalC` applies unchanged:

- `withbor` at `S = Ref V` (identity lens);
- the third `withbor` axiom at `S = Mut @a V` (reborrow);
- `withborF2` and `withborS` (products);
- `compose : MutLens S U → MutLens U V → MutLens S V`, built by nesting `run` and shortening
  with `⊑Mut`, the way `withborF2` is built.

**Laws, stated as observational equalities of `Steps`**: the same final value and the same empty
memory, not as typing facts.

- **identity:** `over (λv. (v, ())) ≡ id` (Marshall–Orchard &unit);
- **composition:** `over f ∘ over g ≡ over (f ∘ g)` (Marshall–Orchard &assoc);
- **Rezip:** borrowing and returning without writing leaves `S` unchanged (Riley Prop 4.8.1).

These are statements about the machine, so they cannot disturb the Fundamental Property.

**Stage 2. `Imm` as a getter** (H2).

- `ImmGetter S V` in the same continuation form, over `withload`.
- The law is that the put is the identity: the lender's `Ref` comes back with the same value,
  which is 6.64's `ℓ ↦ v` at the same `v`.
- Check that `copy` makes it a comonoid-valued view (Clarke Def 3.3).

**Stage 3. The decisive test** (H5, then H6).

- **Prism, fresh lifetime, boxed payload.** Derive
  `Mut @a (Ref A ⊕ Ref B) ⊸ (∀'x. Mut 'x A ⊸ ['x] T) ⊸ Mut @a (Ref A ⊕ Ref B) ⊗ (T ⊕ 1)`
  from `withswap` + `case` + `withbor`.
  - If it types with no new rule, the interface is doing work.
  - The law to state is the RustHorn/Aeneas one: the tag after equals the tag before.
- **Traversal, list.**
  - Derive the copy-in/copy-out traversal from `MapMut`/`foldReuse` as an `over` for a list.
  - Then ask whether a *borrow-form* traversal (handing out every `Mut 'x` at once) reduces to
    `withborS`. For a static shape it should. For a dynamic length it needs L2, which is known to
    be open.
- **If the prism needs something new**, that is issue #27's "missing piece". Following §3 of
  `CLAUDE`'s standing practice, the first question is whether a printed object (6.64–6.66, `Imm̲`
  at `⊕`) was left untranscribed, before any new rule is proposed.

**Stage 4 (optional, logic level).** State 6.65 and 6.66 as an `Optic` record at the BoLo level
(`P̂` a predicate, `[α]` the guard) and prove that composition of two 6.65 splits is a 6.65 split
at the meet lifetime. This is the LftL-reborrow shape. It would test "the frame rules are the
lens laws" at the level where the wand lives, without touching the typed world.

**Not recommended yet:**

- A first-class `Lend 'a A` type (Pure Borrow's costate form). It changes the model.
- A session-typed reading (§6.4). There is no sequential precedent to transcribe.

---

## 10. Not read, or not verified

- Galatos, Jipsen, Kowalski, Ono (2007): chapter and section numbers. The residuation law was
  checked in Jipsen–Galatos tutorial slides.
- O'Hearn & Pym (1999) and Pym, O'Hearn, Yang (2004): section numbers (broken PDF encoding).
- Rocha & Caires, ICFP 2021; Saffrich et al., *Borrowing from Session Types*, OOPSLA 2025;
  Kokke, *Rusty Variation*: abstracts only.
- Odersky, *Observers for Linear Types* (ESOP 1992): abstract only.
- Views (Dinsdale-Young et al., POPL 2013): not read in full.
- Toninho–Caires–Pfenning (FoSSaCS 2012, ESOP 2013), Caires–Pfenning–Toninho (MSCS 2016):
  section numbers.
- Game-semantics well-bracketing (Abramsky–McCusker; Laird; Honda–Yoshida): section numbers.
- Idris 2 QTT lenses; Jaskelioff & O'Connor (JFP 2015): not located or not read.
- Milewski's blog post: read through a fetch summary.
- Rust RFC PR #3735 (Field Projections v2): PR page only. *View Types in Rust* (SPLASH 2025): 403.
- The BoCa derivations in §5 and §9 (the fresh-lifetime Mut prism; the lens interface) have not
  been typed or run.

---

## Sources

- Riley. *Categories of Optics*. arXiv:1809.00738, 2018. https://arxiv.org/abs/1809.00738
- Clarke, Elkins, Gibbons, Loregian, Milewski, Pillmore, Román. *Profunctor Optics, a Categorical
  Update*. Compositionality 6(1), 2024. https://arxiv.org/abs/2001.07488
- Vertechi. *Dependent Optics*. ACT 2022, EPTCS 380. https://arxiv.org/abs/2204.09547
- Braithwaite, Capucci, Gavranović, Hedges, Rischel. *Fibre Optics*. arXiv:2112.11145.
- Spivak. *Generalized Lens Categories via functors C^op → Cat*. arXiv:1908.02202.
- Niu, Spivak. *Polynomial Functors: A Mathematical Theory of Interaction*. arXiv:2312.00990.
- Capucci. *Seeing Double through Dependent Optics*. arXiv:2204.10708.
- Capucci, Gavranović, Hedges, Rischel. *Towards Foundations of Categorical Cybernetics*.
  arXiv:2105.06332.
- Capucci, Gavranović, Malik, Rios, Weinberger. *On a Fibrational Construction for Optics, Lenses,
  and Dialectica Categories*. MFPS 2024. arXiv:2403.16388.
- Hedges. *Coherence for Lenses and Open Games*. arXiv:1704.02230.
- Abou-Saleh, Cheney, Gibbons, McKinna, Stevens. *Reflections on Monadic Lenses*.
  arXiv:1601.02484.
- O'Connor. *Functor is to Lens as Applicative is to Biplate*. arXiv:1103.2841.
- Gibbons, Johnson. *Relating Algebraic and Coalgebraic Descriptions of Lenses*. ECEASST 49, 2012.
  http://www.cs.ox.ac.uk/jeremy.gibbons/publications/colens.pdf
- tweag. *linear-base*, `Control.Optics.Linear`. https://github.com/tweag/linear-base
- Milewski. *Linear Lenses in Haskell*. 2024.
  https://bartoszmilewski.com/2024/02/07/linear-lenses-in-haskell/
- Bernardy, Boespflug, Newton, Peyton Jones, Spiwack. *Linear Haskell*. POPL 2018.
  https://arxiv.org/abs/1710.09756
- Ho, Protzenko. *Aeneas: Rust Verification by Functional Translation*. ICFP 2022.
  https://arxiv.org/abs/2206.07185
- Ho, Fromherz, Protzenko. *Sound Borrow-Checking for Rust via Symbolic Semantics*. ICFP 2024.
  https://arxiv.org/abs/2404.02680
- Fromherz. *Aeneas* (colloquium slides), UQAM, 2025.
  https://llm.uqam.ca/en/colloquium/2025-04-30-aymeric-fromherz-aneas/aeneas-uqam-apr2025.en.pdf
- Aeneas repository (Lean backend and tests), GitHub `main`, read 2026-09-26.
  https://github.com/AeneasVerif/aeneas
- Ullrich. *Simple Verification of Rust Programs via Functional Purification*. MSc thesis, KIT,
  2016. https://github.com/Kha/masters-thesis/raw/master/main.pdf
- Matsushita, Tsukada, Kobayashi. *RustHorn*. ESOP 2020 / TOPLAS 2021.
  https://arxiv.org/abs/2002.09002
- Matsushita, Denis, Jourdan, Dreyer. *RustHornBelt*. PLDI 2022.
  https://people.mpi-sws.org/~dreyer/papers/rusthornbelt/paper.pdf
- Gäher, Sammler, Jung, Krebbers, Dreyer. *RefinedRust*. PLDI 2024.
  https://plv.mpi-sws.org/refinedrust/paper-refinedrust.pdf
- Jung, Jourdan, Krebbers, Dreyer. *RustBelt*. POPL 2018.
  https://people.mpi-sws.org/~dreyer/papers/rustbelt/paper.pdf
- Jung. *Understanding and Evolving the Rust Programming Language*. PhD thesis, 2020.
  https://research.ralfj.de/phd/thesis-screen.pdf
- Weiss, Gierczak, Patterson, Ahmed. *Oxide*. https://arxiv.org/abs/1903.00982
- Racordon, Shabalin, Zheng, Abrahams, Saeta. *Implementation Strategies for Mutable Value
  Semantics*. JOT 21(2), 2022. https://www.jot.fm/issues/issue_2022_02/article2.pdf
- Hylo language tour, *Subscripts*. https://docs.hylo-lang.org/language-tour/subscripts
- Swift Evolution SE-0474, *Yielding accessors*.
  https://github.com/swiftlang/swift-evolution/blob/main/proposals/0474-yielding-accessors.md
- Rust project goal 2025h2, *Field projections*.
  https://rust-lang.github.io/rust-project-goals/2025h2/field-projections.html
- Matsakis. *View types for Rust*. 2021.
  https://smallcultfollowing.com/babysteps/blog/2021/11/05/view-types/
- lens-rs. https://github.com/TOETOE55/lens-rs
- Lorenzen, Leijen, Swierstra. *FP²: Fully in-Place Functional Programming*. ICFP 2023.
- Lorenzen, Leijen, Swierstra, Lindley. *The Functional Essence of Imperative Binary Search
  Trees*. PLDI 2024.
- Marshall, Orchard. *Functional Ownership through Fractional Uniqueness*. OOPSLA 2024.
  https://arxiv.org/abs/2310.18166
- Matsushita, Ishii. *Pure Borrow: Linear Haskell Meets Rust-Style Borrowing*. PLDI 2026.
  https://arxiv.org/abs/2604.15290
- Spiwack, Kiss, Bernardy, Wu, Eisenberg. *Linearly Qualified Types*. ICFP 2022.
  https://arxiv.org/abs/2103.06127
- Hobor, Villard. *The Ramifications of Sharing in Data Structures*. POPL 2013.
  https://jvillard.net/pub/ramification-HVpopl13.pdf
- Charguéraud. *Separation Logic for Sequential Programs*. ICFP 2020.
  https://www.chargueraud.org/research/2020/seq_seplogic/seq_seplogic.pdf
- Charguéraud. *Higher-Order Representation Predicates in Separation Logic*. CPP 2016.
  https://www.chargueraud.org/research/2015/horepr/horepr.pdf
- Cao, Wang, Hobor, Appel. *Proof Pearl: Magic Wand as Frame*. arXiv:1909.08789.
- Hance, Howell, Padon, Parno. *Leaf*. OOPSLA 2023. https://arxiv.org/abs/2309.04851
- Wadler. *Linear Types Can Change the World!* 1990.
  https://homepages.inf.ed.ac.uk/wadler/papers/linear/linear.ps
- Odersky. *Observers for Linear Types*. ESOP 1992.
- Brachthäuser, Schuster, Lee, Boruch-Gruszecki. *Effects, Capabilities, and Boxes*. OOPSLA 2022.
  https://se.informatik.uni-tuebingen.de/publications/brachthaeuser22effects.pdf
- Galatos, Jipsen, Kowalski, Ono. *Residuated Lattices*. Elsevier, 2007.
- O'Hearn, Pym. *The Logic of Bunched Implications*. BSL 5(2), 1999.
- Calcagno, O'Hearn, Yang. *Local Action and Abstract Separation Logic*. LICS 2007.
  http://www.cs.ox.ac.uk/people/hongseok.yang/paper/asl.pdf
- Licata, Shulman, Riley. *A Fibrational Framework for Substructural and Modal Logics*.
  FSCD 2017.
- Saffrich, Nishida, Thiemann. *Law and Order for Typestate with Borrowing*. OOPSLA 2024.
  https://arxiv.org/abs/2408.14031
- Saffrich, Spaderna, Thiemann, Vasconcelos. *Borrowing from Session Types*. OOPSLA 2025.
  doi:10.1145/3763173
- Caires, Pfenning. *Session Types as Intuitionistic Linear Propositions*. CONCUR 2010.
  https://www.cs.cmu.edu/~fp/papers/concur10.pdf
- Wadler. *Propositions as Sessions*. JFP 24(2–3), 2014.
- Balzer, Pfenning. *Manifest Sharing with Session Types*. ICFP 2017.
  https://www.cs.cmu.edu/~fp/papers/CMU-CS-17-106R.pdf
- Balzer, Toninho, Pfenning. *Manifest Deadlock-Freedom for Shared Session Types*. ESOP 2019.
- Pruiksma, Pfenning. *A Message-Passing Interpretation of Adjoint Logic*. PLACES 2019, EPTCS 291;
  JLAMP 120, 2021. https://arxiv.org/abs/1904.01290
- Pruiksma, Chargin, Pfenning, Reed. *Adjoint Logic*. Manuscript, 2018.
  https://www.cs.cmu.edu/~fp/papers/adjoint18b.pdf
- Pruiksma, Pfenning. *Back to Futures*. JFP 32, 2022. https://arxiv.org/abs/2002.04607
- Rocha, Caires. *Propositions-as-Types and Shared State*. ICFP 2021. doi:10.1145/3473584
- Caires. *Thread and Memory-Safe Programming with CLASS*. PLACES 2025.
  https://arxiv.org/abs/2505.20848
- Chen, Balzer, Toninho. *Ferrite*. ECOOP 2022.
- Jacobs, Balzer, Krebbers. *Connectivity Graphs*. POPL 2022.
- Jacobs, Balzer. *Higher-Order Leak and Deadlock Free Locks*. POPL 2023.
- Dreyer, Neis, Birkedal. *The Impact of Higher-Order State and Control Effects on Local
  Relational Reasoning*. ICFP 2010.
- Rust RFC 3151, *Scoped threads*. https://rust-lang.github.io/rfcs/3151-scoped-threads.html
