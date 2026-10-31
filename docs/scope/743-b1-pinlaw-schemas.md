# Scope: #743 B1 — `PinLaw` as two schemas

Step B1 of #743's build plan, which the user approved on 2026-10-30. This is a scoping note and
changes no code. The build is phase 2, after review.

**Kernel target.** `Core/PinLaw.lean`. `PinLaw` is restated as two asserted schemas:

- `LendFrame`, the relaxed `withborUV` lend's compatibility lemma over a `LendForm`;
- `LoopFrame`, the per-observation lend's compatibility lemma.

`PinStop` and `PinLoop` stay as definitions and become theorems derived from the schemas.
`fundamentalC_pin`, `adequacyC_pin`, `adequacyD_pin` and `adequacyD_pin_safe` keep their
statements. Their hypothesis is still `PinLaw`, and `PinLaw` is now made of the two schemas.

**Decided, not reopened** (user, 2026-10-30: "The assumptions are fine, I don't want to reopen
the research question we spent weeks on already"):

- `PinLaw` is two asserted schemas, uniform in depth and in holder.
- The single-principle line (`LifeNatural`) and the stack-indexed-relation line are closed. No
  statement here mentions, assumes or carries `LifeNatural`.

**Sources read.**

- Spike: `spike-743-r5`, `experiments/Spike743/Spike743/Round5.lean` (`LendFrameN`, `LoopFrameN`,
  `fundamentalC_of_framesN`, `pinLaw_of_frames`, `errEscape_of_frame`). Also `Natural.lean` on
  `spike-743-natural2` and `spike-743-r5` (`LendForm`, `RowOf`), and reports rounds 3, 4, 5 and P3.
- `#750`'s spike: `spike-cancel-resume`, `Core/PinLaw.lean`.
- On main: SPEC §29, `docs/async-capabilities.md` §4 and §6, `Core/PinLaw.lean`,
  `Core/PinDerives.lean`, `Core/PinFundamental.lean`, `scripts/pin/*.tmpl.lean`,
  `scripts/gen-pin.py`, `Frontend/Check/Program.lean`, `TTied.lean`, `TDerives.lean`,
  `Backend/Driver.lean`, `scripts/AxiomCheck.lean`, `scripts/check-corpus.sh`, `scripts/ci-local.sh`.
- `docs/unsafe.md` is **not on main**. It is on `unsafe-spec` (62cf3435). The per-site decision
  of 2026-10-15 (option D: sites instantiate the schema) is read from there.

---

## 1. The two schemas

### 1.1 Option (a) or (b): **(a)**

The choice is whether `LendFrame` is stated over main's forms and row only (a), or over every
planned form now (b): `ref` mut/imm, `hold` and `fam`.

**Chosen: (a).** `LendForm` has one constructor, `ref`, which is R1: `lendR`, `Ref T` lent as
`Mut 'x T`. The row premise is `Row.ResumeO`, which is `lendR`'s premise exactly. B2 adds the
other constructors together with their rules, and widens the row.

The reasons:

1. **(b) does not spare B2 a statement change.** B2's row is `Row.ResumeOE` / `Row.ResumeOCE`
   (round 5). It is built on `OpSig.LendO`, and `OpSig.LendO` reads `OpSig.awaitB`, which comes
   with #750's rules (`Core/EffRules.lean` on `spike-cancel-resume`; it is not on main). B1 must
   not assume #750, so under either option B1's row is `Row.ResumeO` and B2 changes
   `LendFrame`'s row premise. Option (b) would only move part of B2's widening, the forms, ahead
   of the rules that use it.
2. **Under (a) the restatement keeps the assertion's content.** At its one form, `LendFrame` is
   `PinStop` with one more premise: the callback's `SemC`, which `fundamentalC_pin` supplies.
   `LoopFrame` is `PinLoop` with the steps' `SemC`/`SemV` added. So `PinLaw ↔ PinStop ∧ PinLoop`
   holds, and B1 proves it (`pinLaw_iff`, §2.4). Under (b) that equivalence fails. B1 would then
   strengthen the hypothesis of every theorem using `PinLaw`, by cases that no rule on main
   emits, no program on main uses, and the falsifier cannot exercise.
3. **Standing decision.** "Keep the assertion as small and precise as possible and try to break
   it with programs" (#743, 2026-10-29; `async-pinlaw-decision`: tested by programs, not
   proved). Under (b), the `hold`, `fam` and `imm` cases would be asserted with no program able
   to test them until B2.
4. **The decided shape is unaffected.** The schema is uniform in depth and holder under both
   options, since `LendFrame` names neither. "LendFrame (ref/hold/fam)" is the shape the plan
   reaches at B2, once each form has its rule.

**Statement changes each option forces on later steps.**

| step | under (a), chosen | under (b) |
|---|---|---|
| B1 | `PinLaw`'s definition only; content unchanged (`pinLaw_iff`) | `PinLaw`'s definition, and its content strengthened by `ref imm`, `hold` and `fam`, with no rule for them; adds `lendView`, `LendSide` and a `tk` index now |
| #750 (own unit, either order with B1) | `lendR`'s row and `LendFrame`'s row premise `Row.ResumeO` → `Row.ResumeOC`; `PinLaw` gains `fin : PinFin` | the same |
| B2 | `LendForm`: `ref` becomes `ref k` (`lendView k`, `LendSide k`, adding `lendRI`), plus `hold k y` and `fam`; a `tk` index and `RowOf` (`ResumeOE` at `true`, `ResumeO` at `false`) replace the fixed row; `pinLaw_iff` is retired, because B2 widens the assertion, and its retirement is that widening, made visible; `PinLaw.stop` follows #750's row (`ResumeOCE`, through `.toE`) | the `tk` index and `RowOf` are widened (`ResumeOE`); the `ResumeOCE` row change is the same; no constructor is added |
| B3 | a `LendForm` case for a view (`withbor3U`/`withloadU` relaxed) | the same |

In both columns B2 changes `LendFrame`'s statement. What (b) saves B2 is the constructor
additions. It pays for that with an assertion on main that nothing tests.

### 1.2 `LendForm` and `RowOf` on main

```lean
/-- The lend forms of the relaxed `withborUV` lend: the place's type `P`, the view `V` the
callback is typed at, the answer `B`, and the callback's lifetime context `Δb`. `ref` is R1
(`lendR`): `Ref T` lent as `Mut 'x T`, with `withbor2U`'s witness on `T`. -/
inductive LendForm (Δ : LifeCtx) (x : LifeVar) (b : Lifetime.Life) :
    VTy → VTy → VTy → LifeCtx → Prop
  | ref {T B : VTy} : ¬ VFree x T → (∃ b', Δ.Defines b' ∧ VOutlivesLe Δ b' T) →
      LendForm Δ x b (.ref T) (.mut (.var x) T) B (Δ.extend x b)
```

- The indices are the spike's (`P V B Δb`), without `tk`.
- `B` is an index because B2's `hold` and `fam` constrain the answer at the form (`¬ VFree y B`,
  and that `B` outlives). `ref` leaves it free.
- `ref` carries exactly `lendR`'s two premises on `T` (`hT`, `hside`), which `PinStop` takes
  today.

**`RowOf` on main: not introduced.** With one form there is one row, and `LendFrame` states it
directly as `Row.ResumeO S x`, which is `lendR`'s premise word for word. `RowOf tk` belongs to B2,
where forms admit different rows. A one-branch `RowOf` now would be a definition with an
argument it ignores. This is OQ-B1-2.

### 1.3 `LendFrame`

This is `Round5.LendFrameN` at main's forms, with `RowOf tk S x` read as `Row.ResumeO S x` and the
`tk` binder dropped. Every other premise, and the conclusion, are `LendFrameN`'s as written.

```lean
/-- **LendFrame.** The relaxed `withborUV` lend's compatibility lemma at every `LendForm`: a lend
whose callback `M` is typed in `CDerivesP` at a resuming row with the view `V` in its context,
and is in the relation there, is in the kernel's relation at `F_Σ (P ⊗ B)`. It mentions no depth
and no holder: a lend nested in `M` is part of `M`'s derivation. -/
def LendFrame : Prop :=
  ∀ (Δ : LifeCtx) (x : LifeVar) (b : Lifetime.Life) (P V B : VTy) (Δb : LifeCtx)
    (d M : Expr) (S : Row),
    LendForm Δ x b P V B Δb →
    Δ.Defines b → Δ.find? x = none → b.mentions x = false →
    (∀ y u, Δ.find? y = some u → u.mentions x = false) →
    ¬ VFree x B → NoThunkT B → Row.ResumeO S x →
    closedAt 1 M = true → closedAt 0 (lendCb M).1 = true → closedAt 0 d = true →
    SemV (ℍ := ℍ) Δ [] d (.lolli P .unit) →
    CDerivesP Δb [⟨V, true⟩] M (.comp (CTy.effOf S (.box (.var x) B))) →
    SemC (ℍ := ℍ) Δb [⟨V, true⟩] M (CTy.effOf S (.box (.var x) B)) →
    SemC (ℍ := ℍ) Δ [⟨P, true⟩]
      (.app (.app (.val (withborUV d)) (.var 0)) (.val (lendCb M)))
      (CTy.effOf S (.tensor P B))
```

### 1.4 `LoopFrame`

This is `Round5.LoopFrameN`, word for word.

```lean
/-- **LoopFrame.** The per-observation `imm` lend's compatibility lemma: the lend of `r : Ref A`
whose steps `N`, `K` and first state `s₀` are typed in `CDerivesP` and in the relation, the
state at a type `S` that may mention the lend's lifetime, is in the kernel's relation at
`U(Loop (Ref A ⊗ B) (Ref A ⊗ R))`. -/
def LoopFrame : Prop :=
  ∀ (Δ : LifeCtx) (x : LifeVar) (A S B R : VTy) (N K s0 : Expr),
    Δ.find? x = none → Δ.meetOfDom.mentions x = false →
    (∀ y u, Δ.find? y = some u → u.mentions x = false) →
    ¬ VFree x A → ¬ VFree x B → ¬ VFree x R → NoThunkT B → NoThunkT R → VScoped Δ A →
    closedAt 1 N = true → closedAt 1 K = true → closedAt 0 s0 = true →
    CDerivesP (Δ.extend x Δ.meetOfDom) [⟨.tensor (.imm (.var x) A) S, true⟩] N
      (.comp (.ret (.sum B S))) →
    CDerivesP (Δ.extend x Δ.meetOfDom) [⟨.tensor (.imm (.var x) A) S, true⟩] K (.comp (.ret R)) →
    CDerivesP (Δ.extend x Δ.meetOfDom) [] s0 (.val S) →
    SemC (ℍ := ℍ) (Δ.extend x Δ.meetOfDom) [⟨.tensor (.imm (.var x) A) S, true⟩] N
      (.ret (.sum B S)) →
    SemC (ℍ := ℍ) (Δ.extend x Δ.meetOfDom) [⟨.tensor (.imm (.var x) A) S, true⟩] K (.ret R) →
    SemV (ℍ := ℍ) (Δ.extend x Δ.meetOfDom) [] s0 S →
    SemC (ℍ := ℍ) Δ [⟨.ref A, true⟩] (lendLoopApp A B R N K s0)
      (CTy.loop (.tensor (.ref A) B) (.tensor (.ref A) R))
```

### 1.5 `PinLaw`

```lean
/-- **PinLaw**: the one named assumption, two schemas. Each is stated over `CDerivesP`
derivations only. -/
structure PinLaw : Prop where
  /-- The relaxed lend, at every `LendForm`, is in the relation. -/
  lendFrame : LendFrame (ℍ := ℍ)
  /-- The per-observation lend over a loop whose state holds the borrow is in the relation. -/
  loopFrame : LoopFrame (ℍ := ℍ)
```

- `PinStop` and `PinLoop` stay in `Core/PinLaw.lean` as `def … : Prop`, unchanged. They are now
  the statements of two theorems (§2), no longer fields.
- The field names are `lendFrame`/`loopFrame`, not `stop`/`loop`, so that `PinLaw.stop` and
  `PinLaw.loop` can be the derived theorems (§2) and keep their types: every existing mention of
  `hPin.stop : PinStop` still names a declaration of that type.
- `pinAwaitSig`, `pinYieldSig`, `pinRaiseSig`, `resumeO_await_yield` and `not_resumeO_raise` are
  unchanged.

---

## 2. The derivations

Each theorem below is in `scripts/pin/PinFundamental.tmpl.lean`, which generates
`Core/PinFundamental.lean`. `PinStop` and `PinLoop` give only the callback's (steps')
`CDerivesP` derivation, while the schemas also need its `SemC`. So deriving them needs
`fundamentalC_pin`, and they come after it. This is the spike's order: `stop_of_frames` and
`loop_of_frames` call `fundamentalC_of_framesN`.

### 2.1 `fundamentalC_pin`, from the schemas, by the same induction

The statement is unchanged:

```lean
theorem fundamentalC_pin (hPin : PinLaw (ℍ := ℍ)) {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr}
    {j : Jdg} (h : CDerivesP Δ Γ e j) : SemJ (ℍ := ℍ) Δ Γ e j
```

It keeps the same induction. The generated `--@CORE_CASES@` and `nilDead` are untouched. Two
hand-written cases change, and both now use the induction hypotheses they discard today:

```lean
  | lendR hb hx hbx hΔx hT hB hBn hside hS hM1 hcb hdc _ hM ihd ihM =>
      exact hPin.lendFrame _ _ _ _ _ _ _ _ _ _ (.ref hT hside)
        hb hx hbx hΔx hB hBn hS hM1 hcb hdc ihd hM ihM
  | lendLoopR hx hbx hΔx hA hB hR hBn hRn hsc hN1 hK1 hs0c hN hK hs0 ihN ihK ihs0 =>
      exact hPin.loopFrame _ _ _ _ _ _ _ _ _ hx hbx hΔx hA hB hR hBn hRn hsc hN1 hK1 hs0c
        hN hK hs0 ihN ihK ihs0
```

This is `fundamentalC_of_framesN`'s `lendR` and `lendLoopR` cases at main's rules. `ihM`/`ihN`
are `SemJ … (.comp _)`, which reduces to `SemC`, and `ihs0` reduces to `SemV`. If `exact` does
not accept them as they are, `by simpa [SemJ] using ihM` does, as in the spike. Depth enters only
here: a lend nested in `M` is a case of `M`'s derivation, and `ihM` covers it.

### 2.2 `PinStop` from `LendFrame`: `PinLaw.stop`

```lean
/-- R1's compatibility lemma, from `LendFrame` at `ref`. -/
theorem PinLaw.stop (hPin : PinLaw (ℍ := ℍ)) : PinStop (ℍ := ℍ) :=
  fun _ _ _ _ _ _ _ _ hb hx hbx hΔx hT hB hBn hside hS hM1 hcb hdc hd hM =>
    hPin.lendFrame _ _ _ _ _ _ _ _ _ _ (.ref hT hside) hb hx hbx hΔx hB hBn hS hM1 hcb hdc hd hM
      (fundamentalC_pin hPin hM)
```

### 2.3 `PinLoop` from `LoopFrame`: `PinLaw.loop`

```lean
/-- R2's compatibility lemma, from `LoopFrame`. -/
theorem PinLaw.loop (hPin : PinLaw (ℍ := ℍ)) : PinLoop (ℍ := ℍ) :=
  fun _ _ _ _ _ _ _ _ _ hx hbx hΔx hA hB hR hBn hRn hsc hN1 hK1 hs0c hN hK hs0 =>
    hPin.loopFrame _ _ _ _ _ _ _ _ _ hx hbx hΔx hA hB hR hBn hRn hsc hN1 hK1 hs0c hN hK hs0
      (fundamentalC_pin hPin hN) (fundamentalC_pin hPin hK) (fundamentalC_pin hPin hs0)
```

### 2.4 The content is unchanged: `PinLaw.of_stop_loop`, `pinLaw_iff`

```lean
/-- The schemas from the two compatibility lemmas: at `ref`, `LendFrame` is `PinStop` with the
callback's `SemC` unused, and `LoopFrame` is `PinLoop` with the steps' unused. -/
theorem PinLaw.of_stop_loop (hS : PinStop (ℍ := ℍ)) (hL : PinLoop (ℍ := ℍ)) : PinLaw (ℍ := ℍ)

/-- `PinLaw`, as two schemas, says what `PinStop` and `PinLoop` together say. -/
theorem pinLaw_iff : PinLaw (ℍ := ℍ) ↔ PinStop (ℍ := ℍ) ∧ PinLoop (ℍ := ℍ) :=
  ⟨fun h => ⟨h.stop, h.loop⟩, fun h => PinLaw.of_stop_loop h.1 h.2⟩
```

`PinLaw.of_stop_loop` is `cases` on the `LendForm` premise, then `hS` at its fields; `loopFrame`
is `hL` with the last three premises dropped. This is the accounting for §6: the hypothesis's
definition changes and its content does not. B2 retires both theorems when it adds forms
(§1.1).

### 2.5 Names

| theorem | statement | status |
|---|---|---|
| `fundamentalC_pin` | unchanged | re-proved, the same induction |
| `adequacyC_pin`, `adequacyD_pin`, `adequacyD_pin_safe` | unchanged | proofs unchanged (they call `fundamentalC_pin`) |
| `CDerivesP.ofC` | unchanged | unchanged (generated) |
| `PinLaw.stop` | `PinLaw → PinStop` | new, PROVED |
| `PinLaw.loop` | `PinLaw → PinLoop` | new, PROVED |
| `PinLaw.of_stop_loop`, `pinLaw_iff` | as above | new, PROVED |
| `LendFrame`, `LoopFrame` | §1 | ASSERTED (fields of `PinLaw`) |
| `checked_sem_pin`, `checked_runs_pin`, `checkProgram_soundP` | unchanged | unchanged |

---

## 3. What reports change

The per-site reporting stays per site. Each R1 or R2 site the checker emits is reported where it
is today, and is now an instance of the schema for its rule shape.

| site | today | new text | reason |
|---|---|---|---|
| `Frontend/Check/Program.lean`, `Pins.assurance` (`bcc check`) | `assurance: PinLaw (R1 at 22:11, 34:11)` | **unchanged** | It names the hypothesis (still `PinLaw`) and the rule used at each site (still R1/R2). The schema each rule instantiates is `bcc trusted`'s line. The docstring at :97 and the comment at :307 are unchanged. |
| `Frontend/Check/Program.lean`, `checked_sem_pin`, `checked_runs_pin`, imports | `hPin : PinLaw` | **unchanged** | Statements and proofs go through `fundamentalC_pin`/`adequacyC_pin`, which are unchanged. |
| `Backend/Driver.lean`, `typingReport` (`bcc trusted`) | `  R1 at 12:3: PinLaw.stop` / `  R2 at …: PinLaw.loop` | `  R1 at 12:3: LendFrame at ref (PinLaw.lendFrame)` / `  R2 at …: LoopFrame (PinLaw.loopFrame)` | SPEC §29 says the line gives "the field of `PinLaw` it rests on". The fields are now the schemas, and R1 is the `ref` form. The header line (`typing: PinLaw (Core/PinLaw.lean), the hypothesis of fundamentalC_pin and adequacyD_pin: N sites`) and the docstring are unchanged. |
| `scripts/AxiomCheck.lean`, §29 block | `ofC`, `fundamentalC_pin`, adequacy, rows, checker | add `#print axioms` for `PinLaw.stop`, `PinLaw.loop`, `PinLaw.of_stop_loop`, `pinLaw_iff` | It lists every theorem SPEC names, and §29 will name these. |
| SPEC §29 *Typing*, bullet on `[nil-dead]` (:5153) | "so `PinLaw.stop`'s premise ranges over those derivations too" | "so `LendFrame`'s premise ranges over those derivations too" | The assertion's premise is now the schema's. |
| SPEC §29, R2 bullet (:5156) | "with its compatibility lemma `PinLaw.loop`" | "an instance of `LoopFrame`; `PinLaw.loop` derives its compatibility lemma" | `PinLaw.loop` is now a theorem. |
| SPEC §29, **`PinLaw`** paragraph (:5165–5175) | "a `structure … : Prop` of two fields, the compatibility lemmas of R1 (`PinStop`) and R2 (`PinLoop`)" | "a `structure … : Prop` of two schemas: `LendFrame`, the relaxed `withborUV` lend's compatibility lemma at every `LendForm` (R1 is the form `ref`), and `LoopFrame`, the per-observation lend's (R2). Each takes the callback's (steps') `CDerivesP` derivation and its `SemC`, and mentions no depth or holder. `PinStop` and `PinLoop` are derived (`PinLaw.stop`, `PinLaw.loop`), and `pinLaw_iff` shows the two schemas say what they say together." The rest of the paragraph has "`PinStop`'s premise" → "`LendFrame`'s premise". | It describes the new definition. |
| SPEC §29, *The checker's derivation and the assurance report* (:5214) | "each site with the field of `PinLaw` it rests on" | "each site with the schema of `PinLaw` it instantiates (`LendFrame` at its form, or `LoopFrame`)" | It matches `typingReport`. |
| SPEC §29 *Theorems* (:5225–5236) | three lines; "with `hPin.stop` at `lendR`, `hPin.loop` at `lendLoopR`" | add `PinLaw.stop : PinLaw → PinStop`, `PinLaw.loop : PinLaw → PinLoop`, `pinLaw_iff`; "with `hPin.lendFrame` at `lendR` (form `ref`) and `hPin.loopFrame` at `lendLoopR`, each at the induction hypothesis of its callback (steps)" | It describes the new induction. |
| SPEC §29 *Open* (:5265–5266) | "Shrinking `PinLaw` (U8)." / "What `PinStop` ranges over" | "Shrinking `PinLaw` (U8)." / "What `LendFrame` ranges over" | The assertion's name. |
| SPEC *Status* (:9922–9924) | `Core/PinLaw.lean` (`PinStop`, `PinLoop`, `PinLaw`) | `Core/PinLaw.lean` (`LendForm`, `LendFrame`, `LoopFrame`, `PinLaw`, `PinStop`, `PinLoop`); the `PinFundamental` list adds `PinLaw.stop`, `PinLaw.loop`, `PinLaw.of_stop_loop`, `pinLaw_iff` | It is the inventory. |
| SPEC *Changelog* | — | a new entry at the next version: "§29 (#743, B1): `PinLaw` as two schemas, `LendFrame` over `LendForm` (`ref`) and `LoopFrame`; `PinStop`, `PinLoop` derived; `pinLaw_iff`. No change to `CDerivesP`, the relation, the machine, the checker's acceptance, the statements of `fundamentalC_pin` and adequacy, the `bcc check` line, or a program's output or count." | Every SPEC change gets an entry. |
| `docs/async-capabilities.md` §0 (:35–39) | "stated as the compatibility lemmas of R1 (`PinStop`) and R2 (`PinLoop`) themselves" | "stated as two schemas, the compatibility lemmas of the relaxed lend at each lend form (`LendFrame`; R1 is `ref`) and of the per-observation lend (`LoopFrame`; R2); `PinStop` and `PinLoop` are derived from them" | It describes the definition. |
| `docs/async-capabilities.md` §3.3 (:234, :255) | "Its compatibility lemma is `PinLaw.stop` (§4)." / "… `PinLaw.loop`, ASSERTED (§4.3)." | "Its compatibility lemma is `PinLaw.stop`, derived from `LendFrame` at `ref` (§4)." / "… `PinLaw.loop`, derived from `LoopFrame`, ASSERTED (§4.3)." | The lemma is now derived. ASSERTED stays, because the schema is asserted. |
| `docs/async-capabilities.md` §3 table (:305) | "R1 (`PinLaw.stop`)" | **unchanged** | `PinLaw.stop` still names R1's lemma. |
| `docs/async-capabilities.md` §4.1 | the `PinStop`/`PinLoop`/`structure` block, in `PDerives` | `LendForm`, `LendFrame`, `LoopFrame` and `PinLaw` as in §1, then `PinStop`/`PinLoop` stated as what is derived; "Each field is the compatibility lemma of its rule" → "Each schema is the compatibility lemma of one rule shape, at the rule's own premises plus the callback's relation" | It shows the statement. |
| `docs/async-capabilities.md` §4.2 table | `fundamentalC_pin … plus hPin.stop and hPin.loop` | "… plus `hPin.lendFrame` and `hPin.loopFrame`"; add rows `PinLaw.stop`, `PinLaw.loop`, `pinLaw_iff`, PROVED | It lists the theorems. |
| `docs/async-capabilities.md` §4.3 headings | **`PinStop`.** / **`PinLoop`.** | **`LendFrame` (at `ref`: `PinStop`).** / **`LoopFrame` (`PinLoop`).** The evidence and falsifier text is unchanged. | The evidence is unchanged and is about the same lemmas (`pinLaw_iff`). |
| `docs/async-capabilities.md` §8, OQ-1 (:577–580), OQ-2 (:585) | "adding them to `PinStop`'s row … (a) grows `PinLaw`" / "Each would add one field to `PinLaw`." | "widening `LendFrame`'s row … (a) grows `PinLaw`" / "Each would add one `LendForm` case, widening `LendFrame`, not a field." | It follows the decided shape. |
| `docs/internals/proved.md` (:159–164) | "covered under `PinLaw`, a hypothesis stated in Lean (`Core/PinLaw.lean`) and not yet proved" | "covered under `PinLaw`, two schemas stated in Lean (`Core/PinLaw.lean`: `LendFrame`, a relaxed lend's compatibility lemma, and `LoopFrame`, the per-observation lend's) and not yet proved" | It describes the definition. The `assurance:` text it quotes is unchanged. |
| `Core/README.md` (:281–286) | "`PinLaw` (`PinLaw.lean`) is R1's and R2's compatibility lemmas, a hypothesis" | "`PinLaw` (`PinLaw.lean`) is two schemas, `LendFrame` over the lend forms (R1 is `ref`) and `LoopFrame` (R2), a hypothesis; `PinLaw.stop` and `PinLaw.loop` derive R1's and R2's compatibility lemmas in `PinFundamental.lean`" | It describes the definition. |
| `Frontend/README.md` (:212–215) | `assurance: PinLaw (R1 at L:C, …)` | **unchanged** | The `bcc check` line is unchanged. |
| `Core/PinLaw.lean` module docstring | "asserts the compatibility lemmas of the two relaxed rules" | the two schemas, `LendForm`'s one form, and that `PinStop`/`PinLoop` are derived in `PinFundamental.lean` | It is the file being changed. |
| `scripts/pin/PinFundamental.tmpl.lean` docstring (:9–11) and `Core/PinFundamental.lean` (generated) | "R1's case is `PinLaw.stop`; R2's is `PinLaw.loop`" | "R1's case is `PinLaw.lendFrame` at `ref`, R2's `PinLaw.loopFrame`, each at the induction hypothesis of its callback (steps)"; plus bullets for `PinLaw.stop`, `PinLaw.loop`, `pinLaw_iff` | It is the file being changed. |
| `scripts/pin/CDerivesP.tmpl.lean` (:24–25) and `Core/PinDerives.lean` | "The soundness of R1 and R2 is `PinLaw`" | **unchanged** | Still true. |
| `scripts/pin/TDerives.tmpl.lean`, `Frontend/Check/TTied.lean`, `TDerives.lean` | "`PinLaw`'s theorems" | **unchanged** | They name the hypothesis only. |
| corpus comments `-- assurance: PinLaw (R1 at …)` (10 files) | — | **unchanged** | The output is unchanged. |
| `corpus/async-r1-nested.bc:4` | "so `PinLaw.stop`'s premise is the outer body's derivation" | **unchanged** | Still true: `PinLaw.stop : PinLaw → PinStop`, and `PinStop`'s premise is that derivation. Changing a corpus file for a comment would only add a corpus diff. |
| `docs/kernel-usage.md`, `effect-lowering.md`, `expressiveness.md`, `compiler.md`, `ergonomics.md`, `Home.md`, `docs/research/*`, `lib/async.bc`, `experiments/LetMutState` | name `PinLaw` as a whole | **unchanged** | The hypothesis's name is unchanged. |
| **Goldens / expected files** | — | **none change** | `corpus/trusted/*.txt` all print `typing: unconditional` (none uses R1/R2). `check-corpus.sh` never diffs the `assurance:` line (only `-- expect:`, `-- now:`, `reports/*.txt` effect lines and `trusted/*.txt`). No `*.expected` file contains `PinLaw`. `docs/kernel-usage/decls.tsv` lists derived rules and forms; `LendForm` (an inductive `Prop`) and the new theorems (concluding `PinStop`, `PinLoop`, `↔`) are neither. |

---

## 4. NOT-do list

- No new relaxed rule, and no new `LendForm` case: that is B2 (and B3 for views).
- No `LifeNatural`, as a premise, a definition, a comment's route or a docstring's "why".
- No stack-indexed relation, and no proof attempt at either schema.
- No change to the statements of `fundamentalC`, `fundamentalC_pin`, `adequacyC_pin`,
  `adequacyD_pin`, `adequacyD_pin_safe`, `CDerivesP.ofC`, `checked_sem_pin`, `checked_runs_pin`.
- No change to the falsifier (`docs/async-capabilities.md` §6, `scripts/falsify.sh`).
- No change to the row conditions: `Row.ResumeO` and `NoThunkT` stay as they are, and no
  `ResumeOT`/`ResumeOC`/`ResumeOE`/`ResumeOCE`/`OpSig.LendO`/`OpSig.EscapeO` is added.
- No `PinFin`, `[await-c]` or `awaitB`: these are #750's, landing as their own unit.
- No change to `CDerivesP`'s rules or `scripts/pin/CDerivesP.tmpl.lean`'s rules.
- No elaborator or checker change: `Frontend/` Lean is untouched.
- Nothing in Backend2's `Lint` or `stackK` files (#746 step 4). Touching them is a STOP.
- No merge or cherry-pick from `spike-743-r5`, `spike-743-natural2` or `spike-cancel-resume`. The
  schemas are retyped from §1.
- No push, no PR, no GitHub comment.

## 5. Tempting shortcuts and the STOP each raises

| shortcut | why it is tempting | STOP |
|---|---|---|
| Keep `stop : PinStop` and `loop : PinLoop` as fields beside the schemas | the existing code and docs compile unchanged | STOP: that is four assertions, not two. `PinStop`/`PinLoop` must be theorems. |
| State `LendForm` with `hold`/`fam`/`ref imm` "for later" | B2 gets additive constructors | STOP unless the reviewer picks (b). Then each such case is listed as asserted with no rule, in SPEC and in the docstring, and `pinLaw_iff` is dropped with that recorded. |
| Add `tk`/`RowOf` with both branches `ResumeO` | B2 then only edits `RowOf`'s body | STOP: it is an index the code ignores. Raise it under OQ-B1-2. |
| Prove `PinStop` from `LendFrame` some other way (inline a second induction, or a `fundamentalC_of_frames` beside `fundamentalC_pin`) | it decouples the files | STOP: the spike's route is `fundamentalC_pin`'s induction with the frames' cases, then the fields from it. One induction. |
| Put `PinLaw.stop`/`loop` in `Core/PinFundamental.lean` by hand | it avoids the template | STOP: that file is generated, and `gen-pin.py --check` fails. They go in the template. |
| Change `bcc check`'s line to name the schemas | it is more informative | STOP: that is a report change outside this scope (OQ-B1-3). The line stays. |
| Change an `.expected`, `trusted/*.txt` or `-- expect:` line without listing it | the gate is red | STOP: §3 says none change. Any that does is reported with its reason before it is edited. |
| Add a premise to `LendFrame`/`LoopFrame` that `LendFrameN`/`LoopFrameN` lack, so a case closes | the induction balks | STOP: report the case and the premise. Never weaken the schema in silence. |
| Weaken `pinLaw_iff` to one direction because the `cases` on `LendForm` fights | it saves time | STOP if the converse cannot be shown: that would mean the restatement changed content. |
| Touch Backend2 `Lint`/`stackK` to fix a downstream break | the build is red | STOP: KERNEL WORK / #746 collision. Report it. |
| Have the checker or driver decide which schema a site uses by anything except the rule tag | it would allow richer reports | STOP: KERNEL WORK. The rule tag maps one-to-one onto the schema. |

## 6. The smallest change and its accounting

**Files that change.**

| file | change |
|---|---|
| `Core/PinLaw.lean` | adds `LendForm`, `LendFrame`, `LoopFrame`; `PinLaw`'s fields become `lendFrame`/`loopFrame`; module docstring. `PinStop`, `PinLoop` and the row examples are unchanged. |
| `scripts/pin/PinFundamental.tmpl.lean` | the `lendR`/`lendLoopR` cases (§2.1); adds `PinLaw.stop`, `PinLaw.loop`, `PinLaw.of_stop_loop`, `pinLaw_iff`; docstring |
| `Core/PinFundamental.lean` | regenerated by `python3 scripts/gen-pin.py` |
| `Backend/Driver.lean` | `typingReport`'s `field` (one line) |
| `scripts/AxiomCheck.lean` | four `#print axioms` lines |
| `SPEC.md` | §29, *Status*, *Changelog* (§3) |
| `docs/async-capabilities.md`, `docs/internals/proved.md`, `Core/README.md` | §3 |

**Theorem statements that change: none** of `fundamentalC_pin`, `adequacyC_pin`, `adequacyD_pin`,
`adequacyD_pin_safe`, `CDerivesP.ofC`, `checked_sem_pin`, `checked_runs_pin`,
`checkProgram_soundP`.

**Hypotheses that change: `PinLaw`'s definition only.** Its content does not change:
`pinLaw_iff : PinLaw ↔ PinStop ∧ PinLoop`. Every theorem that takes `PinLaw` therefore holds under
exactly the assumption it held under before.

**Goldens and expected files that change: none** (§3, last row).

**Not touched:** `Frontend/` Lean, `Backend2/`, `lib/`, `corpus/`, `Paper/`, `Support/`,
`CDerivesP`'s rules, `TExpr`/`TDerives` templates.

**Gate cost.** `Backend/Driver.lean` is under `Backend/`, so the full gate turns on the source
stage for every program (`ci-local.sh`, `BCC_SOURCE=1`). That is the longest gate. It is accepted
because the alternative, leaving `bcc trusted` naming a theorem as a field, is a wrong report.
This is OQ-B1-3.

## 7. Checks for phase 2

Iterate with targeted checks. Run the full gate once.

1. `python3 scripts/gen-pin.py`, then `python3 scripts/gen-pin.py --check`.
2. `lake build Core.PinLaw Core.PinFundamental`, then `lake build Frontend.Check.Program
   Backend.Driver` (targeted). Then `lake build` once, which covers the default targets.
3. `scripts/check-hygiene.sh`: forbidden keywords, imports, `gen-pin.py --check`, and
   `CheckAxioms.lean` (every declaration's axioms ⊆ `propext`, `Classical.choice`, `Quot.sound`).
4. `lake env lean scripts/AxiomCheck.lean`: the §29 block, including the four new names, prints
   only the three standard axioms.
5. Golden tests: `scripts/check-corpus.sh` (in particular `corpus/trusted/*.txt` and every
   `async-r1-*`/`async-*` program), and `bcc trusted corpus/async-r1-drain.bc` by hand to see the
   new `typing:` line (not pinned).
6. One `make gate`, run only as `~/repos/scripts-local/gate-serial.sh gate` from
   `~/repos/borrow-core-743b1`. Never `make` directly, and never `gate-full`.

## 8. Open questions for the reviewer

> **OQ-B1-1. (a) or (b).** Proposed: **(a)** (§1.1). The plan's B1 line names
> "LendForm ref/hold/fam". (a) reaches that shape at B2, when each form gets its rule. The
> standing decisions settle the content but not the staging: "keep the assertion as small and
> precise as possible" (#743, 2026-10-29) and "tested by programs" (`async-pinlaw-decision`)
> favour (a). The 2026-10-30 decision ("two asserted schemas, uniform in depth and holder") holds
> under both. **The reviewer confirms (a) or picks (b).**

> **OQ-B1-2. `RowOf` and `tk` now or at B2.** Proposed: at B2. On main there is one row, and a
> `tk` that selects between two equal rows is an index the code ignores. The cost: B2 adds a
> binder to `LendFrame` as well as widening its row. B2 changes `LendFrame`'s row premise under
> every option, so this adds no new kind of change. *Not settled by a standing decision.*

> **OQ-B1-3. Report wording.** Proposed: `bcc check` unchanged, and `bcc trusted` per site
> `R1 at L:C: LendFrame at ref (PinLaw.lendFrame)` / `R2 at L:C: LoopFrame (PinLaw.loopFrame)`.
> *Settled in part* by the per-site decision (2026-10-15, `docs/unsafe.md` option D on
> `unsafe-spec`: "PinLaw is the SCHEMA the sites instantiate"). Each site is reported, with the
> schema it instantiates. *Open:* whether the one-line `assurance:` should also name the schema.
> Proposed no, because it would touch 10 corpus comments and SPEC/README tables for no new
> information.

> **OQ-B1-4. Names.** Proposed: fields `lendFrame`/`loopFrame`, and theorems `PinLaw.stop`/`PinLaw.loop`.
> That way `hPin.stop : PinStop` keeps its meaning, now as a theorem. The alternative is
> spike-style `stop_of_frames`/`loop_of_frames`, which renames every doc mention. *Not settled
> by a standing decision* (syntax choices are not blocking, `syntax-choices-not-blocking`, so
> this need not hold the build).

> **OQ-B1-5. `pinLaw_iff`.** Proposed: include it. It is the proof that B1 changes no asserted
> content. Two small theorems, retired at B2. *Settled by* "prove what you can, assert what we
> have to" (2026-10-29): it is tractable, so it is proved.

> **OQ-B1-6. Order with #750.** #750 widens `lendR`'s row to `Row.ResumeOC` and adds
> `PinLaw.fin : PinFin` (`spike-cancel-resume`). If B1 lands first, #750's rebase edits
> `LendFrame`'s row premise (one place) instead of `PinStop`'s, and `PinLaw.stop` follows. If
> #750 lands first, B1's `LendFrame` takes `Row.ResumeOC` and `PinLaw` keeps `fin` as a third
> field. *Settled by* the plan: "#750's rules land via #750 as its own unit". B1 assumes neither
> order, and whichever lands second rebases.
