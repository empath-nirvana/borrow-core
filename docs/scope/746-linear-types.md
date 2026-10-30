# #746 scope: two kernel classes, unrestricted and linear

Phase 1 of #746, revised after the user's decisions on v1
(<https://github.com/empath-nirvana/borrow-core/issues/746#issuecomment-6513103490>). It is the
scope document the user reviews before any code changes. It states the kernel facts as Lean
statements to be proved later; it proves nothing new and changes no code.

The rule this serves (user): *"Either it is a linear type or it is not, and if it's not, it gets
another name."* Conveniences are derivations over the kernel concept, never new concepts.

The kernel has two classes of value type: **unrestricted** (`VTy.Persistent`) and **linear**
(everything else). A linear type may have a **derived drop** (`HasDtor`, `dtor_wf`,
`drop_derives`) or a **derived copy** (the kernel constant `copy`, at `Imm`). Neither is a third
class. The word v1 used for a third class, "affine", is removed from the kernel, SPEC, docs, code
names, error messages and this document, and this is the only sentence of this document that
contains it.

Everything below was read at `origin/main` b566c459 (this branch is b566c459 plus this document).
Facts marked *(probe)* were checked in Lean against that build in
`~/repos/scratch-archive/linear-types/probes/Probe746.lean`. Facts marked *(run)* were checked by
running `bcc` from this worktree (section 6).

---

## 0. Summary

- **HARD STOP finding, already known (#746 item 5, audit F3).** Backend2 drops a value of a
  linear closure type with no kernel rule behind it: `Backend2/Convert.lean:1329` (`k'`, in the
  stack step) and `:1388–1389` (`kv`, at a point's `mk`), each added to `Prog.stackKs`, which
  `Backend2/Lint.lean:149` exempts from the type check. The site's own `UNPROVED:` comment
  (`Convert.lean:1380–1386`) says "no typing rule lets a term discard" it. Section 5.5 states the
  kernel statement that would license it.
- **HARD STOP finding (F2).** Backend2's Lint admits a `.drop` at an opaque host type (`.opq`)
  at any site (`Backend2/Lint.lean:70`, `t.drops`). The kernel abandons such a value only at an
  abort (decision 2); no constant and no `HasDtor` rule drops it anywhere else. *(run)* Every
  I/O program reaches one: Backend2's `epilogue` (`Convert.lean:3640–3659`) takes `main`'s
  capabilities back as `let c = free(cap); drop c` at `Input`/`Output`/`Clock`/`Args` (298 drops,
  169 programs; the old backend's `Clos/Convert.lean:950–968` is the same, read). The kernel's
  account of that point is the checked `run_io` wrapper (`Frontend/Check/Externs.lean`), which
  consumes each cell with `take_input`/`take_output`/`take_clock`/`take_args` and drops only
  their unrestricted results. No other Backend2 site emitted an `.opq` drop. Fixed in step 1
  (section 7): L-T's `Tok` is an `.opq` type, so until then Backend2 would admit dropping a
  declared value.
- **Two classes** (section 1.1): `Unrestricted A := A.Persistent`, `Linear A := ¬ A.Persistent`.
  Contraction (`Ctx.SplitP.dup`) and weakening (`Ctx.DeadP.drop`, `Ctx.SoloP.skip`) are kernel
  rules exactly at unrestricted types; that is stated as three inversion lemmas on the context
  relations (not on `CDerives`).
- **Derived drop** (1.2): `DerivedDrop A := Linear A ∧ HasDtor A`, licensed by `drop_derives`,
  pure at the row (decision 1: `dtor_wf`'s type and `kTy_cancel_hasDtor_iff`).
- **Not a drop** (1.3): `⊤` (`topI`), `absurd` (`zeroE`) and an abort's abandonment of a
  `VTy.Drop` context (`effLet`'s `hW`, `effRaise`'s `hd`) absorb a context. This is decision 2;
  SPEC says so.
- **Derived copy** (1.4): `DerivedCopy` at `Imm @a A` and `[Imm @a A]`, licensed by a new
  derived rule `copy_derives` over `CDerives.copy`/`arrCopy` (decision 3). No site inserts one
  today.
- **Continuation qualifiers** (1.5): `κ` at `lin` and at the default `ctl` qualifier are both
  linear types; the default one has a cancel branch, the `A & 1` encoding, and its cancel is a
  derived drop exactly when the cancel row is empty (`HasDtor.close`). At `unr` `κ` is
  unrestricted.
- **Checker** (1.6): `dtorB_complete`/`dtorB_completeA`, hence `hasDtorB_iff`, with the fallback
  of defining `HasDtor` by `dtorB`. Then `Class.of` provably computes the two classes and the drop
  bit, and `Env.pushOwn` provably owes exactly the `DerivedDrop` slots.
- **Declared types with no derived drop** (section 2): L-T (decision 4), a field of a new opaque kind
  `tok`, with `mint`/`burn` constants. No new type former, no change to `VTy.Drop`.
- **Sites** (section 5): the checker reads kernel facts throughout (it builds the derivation). The
  elaborator emits terms the checker types, with three places that restate a kernel definition
  instead of reading it. Both backends rebuild copy and drop decisions from the erased term rather
  than reading them; Backend2's Lint re-checks them by type, with one exemption list (F3) and one
  mis-cited case.
- **Programs** (section 6): one program changes acceptance, by the user's decision (binder `linear`
  removed: `corpus/reject/linear-unused.bc` becomes accepted, its cell dropped by `drop_derives`);
  three corpus programs keep their output *(run)*; the rest are text changes to messages, reports
  and `corpus/kinds.expected`.

---

## 1. The kernel statements

Proposed file `Core/Classes.lean`, importing `Core.Dtor` and `Core.EffRules`. It adds no rule to
`CDerives`, no index and no semantic definition: it names the classes, and states the derived
rules over existing rules. Statement shapes are fixed here; de Bruijn details are fixed when proved.

### 1.1 Two classes

```lean
namespace BoCa.Fig16.LogRel.Core

/-- Unrestricted: contraction and weakening are rules of `CDerives` at `A`
(`Ctx.SplitP.dup`, `Ctx.DeadP.drop`, `Ctx.SoloP.skip`); a value holds `∅`
(`vP_empty_of_persistent`).  `[spec §10]` -/
abbrev Unrestricted (A : VTy) : Prop := A.Persistent

/-- Linear: every other type. A live slot of linear type is consumed by exactly one rule that
uses it, or absorbed by `⊤`/`absurd`/an abort (section 1.3).  `[spec §10, §12]` -/
abbrev Linear (A : VTy) : Prop := ¬ A.Persistent

theorem unrestricted_or_linear (A : VTy) : Unrestricted A ∨ Linear A := em _

/-- Contraction is a rule exactly at unrestricted types. -/
theorem Ctx.SplitP.both_live_iff {T : VTy} {Γ Γ₁ Γ₂ : Ctx VTy} :
    Ctx.SplitP (⟨T, true⟩ :: Γ) (⟨T, true⟩ :: Γ₁) (⟨T, true⟩ :: Γ₂) ↔
      Unrestricted T ∧ Ctx.SplitP Γ Γ₁ Γ₂

/-- Weakening at the end of a derivation is a rule exactly at unrestricted types. -/
theorem Ctx.DeadP.live_iff {T : VTy} {Γ : Ctx VTy} :
    Ctx.DeadP (⟨T, true⟩ :: Γ) ↔ Unrestricted T ∧ Ctx.DeadP Γ

/-- Weakening beside a variable is a rule exactly at unrestricted types. -/
theorem Ctx.SoloP.live_succ_iff {S T : VTy} {Γ : Ctx VTy} {i : Nat} :
    Ctx.SoloP (⟨S, true⟩ :: Γ) (i + 1) T ↔ Unrestricted S ∧ Ctx.SoloP Γ i T
```

Cost: cases on three small inductives (`Core/Persistent.lean:112–139`). This is not an inversion
of `CDerives`. The `←` directions are the existing constructors.

### 1.2 The derived drop

```lean
/-- A linear type with a derived drop: `dtorE A : A ⊸ F 1` is a closed `CDerives` term. -/
def DerivedDrop (A : VTy) : Prop := Linear A ∧ HasDtor A

-- The derivation that licenses every inserted drop (exists, `Core/Dtor.lean:642`):
--   theorem drop_derives (hs : Ctx.SplitP Γ Γ₁ Γ₂) (hx : Ctx.SoloP Γ₁ i T) (hT : HasDtor T)
--       (h : CDerives Δ Γ₂ e (.comp C)) : CDerives Δ Γ (dropE T i e) (.comp C)
-- over `dtor_wf` (`Core/Dtor.lean:518`). The drop is the value's one use.

/-- The syntactic side condition `TiedDer.ofCDerives` needs: `dtorE A` contains no
perform, raise, handler or iterate. Today `dropOne` (`Frontend/Check/Steps.lean:671`) and
`Consts.lean:145` check this per use. It holds at every type, so it is not decision 1: that a
derived drop is pure at the row is carried by `HasDtor.close`/`.nu` asking for a `ret` cancel,
by `dtor_wf` typing `dtorE A` at `A ⊸ F 1`, and by `kTy_cancel_hasDtor_iff` (1.5). -/
theorem dtorE_effFree {A : VTy} (h : HasDtor A) : (dtorE A).effFree = true
theorem dtorE_closed {A : VTy} (h : HasDtor A) : closedAt 0 (dtorE A) = true
```

`HasDtor` also holds at many unrestricted types (`unit`, `int`, `bang`, …: the destructor is
`forget`). That is harmless: at an unrestricted type the kernel's own weakening already applies.
"Has a derived drop" is therefore stated as `DerivedDrop`, a property of linear types.

`dtorE_effFree` and `dtorE_closed` are unverified. If either fails at some constructor, the
per-use checks stay; they decide a Bool on a kernel term, which is reading a kernel fact.

### 1.3 What is not a drop (decision 2)

Three rules absorb a context without using its slots. None is weakening.

| rule | where | condition |
|---|---|---|
| `⊤` introduction | `CDerives.topI` (`Core/Fundamental.lean:131`): any `Γ` | none |
| `absurd` | `CDerives.zeroE` (`:145`): the context split around a value of `0` | none |
| abandonment at an abort | `CDerives.effLet`'s `hW : S.Weak → Γ₂.Drops` (`:409–411`), `effRaise`'s `hd : o.A.Drop` (`:404–405`) | every abandoned slot `VTy.Drop` |

The third is standard linear logic: a computation that aborts never returns to the rest, which
is `⊤`-like, and the abandoned slots hold no owned cell, so nothing leaks:

```lean
-- exists, `Core/EffRules.lean:1054`
theorem vC_noOwn_of_drop {A : VTy} (hA : A.Drop) :
    vC true A ls δ v ρ → NoOwn ρ
```

`VTy.Drop` includes the opaque host types (`Drop.opq`), so an abort may abandon a live `Input`
or `Output` *(probe)*. That stays. SPEC §19 and §11 will say so in these words.

### 1.4 The derived copy at `Imm` (decision 3)

`Imm @a A` is linear (`VTy.persistent (.imm _ _) = false`). It has a derived drop
(`HasDtor.imm`, by `forgetImm`) and a derived copy by the kernel constant `copy`.

```lean
/-- A linear type with a derived copy: a kernel constant duplicates it. -/
inductive DerivedCopy : VTy → Prop where
  | imm (a : Lifetime.Life) (A : VTy) : DerivedCopy (.imm a A)           -- `CDerives.copy`
  | arrImm (a : Lifetime.Life) (A : VTy) : DerivedCopy (.fam (.imm a A))  -- `CDerives.arrCopy`

/-- The copy constant at a `DerivedCopy` type. -/
def copyC : VTy → Expr
  | .fam _ => .val copyV
  | _ => copy

/-- `let (x₁, x₂) = copyC A xᵢ; e`. -/
def copyE (A : VTy) (i : Nat) (e : Expr) : Expr :=
  bindE (.app (copyC A) (.var i)) (.letpair (.var 0) e)

/-- **A copy is a `CDerives` derivation**: the derived rule for every inserted copy. -/
theorem copy_derives {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {i : Nat} {A : VTy} {e : Expr} {C : CTy}
    (hA : DerivedCopy A) (hs : Ctx.SplitP Γ Γ₁ Γ₂) (hx : Ctx.SoloP Γ₁ i A)
    (h : CDerives Δ (⟨A, true⟩ :: ⟨A, true⟩ :: Γ₂) e (.comp C)) :
    CDerives Δ Γ (copyE A i e) (.comp C)
```

Cost: moderate. `CDerives.copy`/`arrCopy`, `lolliE`, `F`-elimination and `tensorE`, with
`CDerives.insert_dead` for the shift. No inversion of `CDerives`. `copyBang` at `!A` is not a
derived copy: `!A` is unrestricted, and the rule `SplitP.dup` applies.

No site inserts a derived copy today. E1 of #58 (implicit `imm` copies) stays rejected
(`class1-revive`). The surface keeps `clone(x)` at unrestricted types (`Sugar.lean:3549–3556`).
"The checker never derives a copy where the program declared otherwise" is Q11.

### 1.5 Continuation qualifiers

`kTy` (`Core/EffRules.lean:1146`):

| `Qual` | `κ` | class | drop |
|---|---|---|---|
| `lin` | `U((B ⊸ F_Σ R) & ⊤)` | linear *(probe)* | none: `¬ HasDtor` *(probe)* |
| `aff` (renamed, section 3) | `U((B ⊸ F_Σ R) & cancelTy Σ F)` | linear *(probe)* | the cancel, `HasDtor.close`, exactly when `cancelTy Σ F = F 1` *(probe at `[]` and at a `Fail` row)* |
| `unr` | `!U(…)` | unrestricted *(probe)* | the kernel's |

```lean
theorem kTy_lin : Linear (kTy S R .lin B F) ∧ ¬ HasDtor (kTy S R .lin B F)
theorem kTy_cancel_linear : Linear (kTy S R .aff B F)
/-- Decision 1: the cancel is a derived drop exactly when it is pure. -/
theorem kTy_cancel_hasDtor_iff : HasDtor (kTy S R .aff B F) ↔ cancelTy S F = .ret .unit
theorem kTy_unr : Unrestricted (kTy S R .unr B F)
```

The default qualifier's `κ` is a linear type with a cancel branch: the `A & 1` encoding, where
the one use of `κ` is either the resume or the cancel. At a row where the cancel performs, the
cancel is an explicit use, written or emitted as `(force κ).2`, not a derived drop. The effectful
§22 closure `νX. (A ⊸ F_Σ(…)) & F_Σ 1` and a task (§30) are the same shape: linear, with a
cancel branch, and with a derived drop only where the branch is `F 1` (`HasDtor.nu` asks for
`ret R`).

### 1.6 The checker decides the predicates (`dtorB_complete`)

```lean
/-- `dtorB` is complete for `HasDtor`. -/
theorem dtorB_complete : ∀ A : CVTy, HasDtor A → dtorB false A = true
/-- …with its `alg` mode, by the mutual induction of `dtorB_soundA`. -/
theorem dtorB_completeA : ∀ (A : CVTy) (Bs : Stack), AlgDtor Bs A → dtorB true A = true

theorem hasDtorB_iff (A : CVTy) : hasDtorB A = true ↔ HasDtor A
instance : DecidablePred HasDtor := fun A => decidable_of_iff _ (hasDtorB_iff A)

theorem dropB_iff (A : VTy) : dropB A = true ↔ A.Drop     -- cases; `dropB_sound` exists
```

Every case but `μ` is the constructor. At `μ`, `HasDtor.mu` gives `PBody A` (decided by
`pBodyB`, `pBodyB_iff` exists) and `AlgDtor [A] A`, and the converse of `dtorB_soundA` is needed;
the stack-independence of `dtorB true` against an `AlgDtor` that depends on `Bs` is the step to
check first. I have not proved `dtorB_completeA` and have not verified that any obstruction is
real.

**Fallback.** Define the predicate by the decider, `HasDtor A := dtorB false A = true`, with
today's constructors as lemmas. `dtor_wf` and every proof by induction on `HasDtor` are then redone
by recursion on `A`. Larger, same result. Either way the stated theorem is `hasDtorB_iff`.

With it, the frontend's classification is the kernel's:

```lean
/-- The class of a value type (`Frontend/Elab/Tir.lean:36`), replacing
`persistent | dtor | linear`. -/
inductive Class where
  | unrestricted
  | linear (drop : Bool)

def Class.of (A : CVTy) : Class :=
  if A.persistent then .unrestricted else .linear (hasDtorB A)

theorem Class.of_unrestricted (A : CVTy) : Class.of A = .unrestricted ↔ Unrestricted A
theorem Class.of_linear (A : CVTy) (d : Bool) :
    Class.of A = .linear d ↔ Linear A ∧ (d = true ↔ HasDtor A)

/-- The owed slot is the one with a derived drop (binder `linear` removed). -/
theorem Env.pushOwn_own (E : Env) (x : String) (A : CVTy) :
    (E.pushOwn x A).own.head? = some (decide (DerivedDrop A))
```

`Class.name` changes from `"persistent" | "destructor" | "linear"` to `"unrestricted"`,
`"linear, with a derived drop"`, `"linear"` (spelling provisional).

---

## 2. Declared types with no derived drop (decision 4: L-T)

Every drop is derived: the language has no hand-written drops. Linear types with no derived drop
already exist (capabilities, must-resume continuations, closures that hold one). L-T lets a data
declaration put its type in that group, for a value whose silent destruction is a bug (a
transaction that must be committed or aborted). Today a `data` type is transparent (SPEC §42)
and `HasDtor` is derived structurally, so the declaration needs a fact the kernel sees.

### 2.1 Mechanism

A declared type `N` with payload `A` is `A ⊗ Tok`, where `Tok = VTy.opq .tok` is a new opaque kind
(`Core/Opaque.lean:24`) with two constants:

```lean
inductive Opaque where
  | input | output | clock | args
  /-- `Tok`: the token of a declared type with no destructor.  `[spec §11, §12]` -/
  | tok

def Opaque.Holds : Opaque → Val → Prop
  | …
  | .tok, v => v = .unit

-- Two constants, at a dead context, like `forgetUnk`:
--   | tokMint {Δ Γ} (hΓ : Ctx.DeadP Γ) : CDerives Δ Γ mint (.val (.lolli .unit (.opq .tok)))
--   | tokBurn {Δ Γ} (hΓ : Ctx.DeadP Γ) : CDerives Δ Γ burn (.val (.lolli (.opq .tok) .unit))
```

`Tok` holds `∅`, so the compatibility lemmas are the `I32`-leaf case. No new `VTy` former, and
`VTy.Drop`'s `opq` constructor is not narrowed: such a value can still be abandoned by an abort
(decision 2), when its payload is `VTy.Drop` too.

### 2.2 The statements

```lean
theorem tok_linear : Linear (.opq .tok) ∧ ¬ HasDtor (.opq .tok)        -- cases
/-- A field with no derived drop makes the container linear with none. -/
theorem not_hasDtor_tensor_right (h : ¬ HasDtor B) : ¬ HasDtor (.tensor A B)
theorem not_persistent_tensor_right (h : ¬ B.Persistent) : ¬ (VTy.tensor A B).Persistent
-- and the same at `.tensor B A`, `.sum`, `.box`, `.ref`, `.fam (.ref _)`, `.mu` (via `keysIn`).
theorem decl_linear (A : VTy) : Linear (.tensor A (.opq .tok)) ∧ ¬ HasDtor (.tensor A (.opq .tok))
/-- Borrows of it are linear with a derived drop: a loan ends, the value is not consumed. -/
theorem decl_imm_drop : DerivedDrop (.imm a (.tensor A (.opq .tok)))   -- `HasDtor.imm`
theorem decl_mut_drop : DerivedDrop (.mut a (.tensor A (.opq .tok)))   -- `HasDtor.mut`
/-- No inserted drop exists at it: a `dtor` node of the typed term carries `HasDtor`. -/
theorem TDerivesP.dtor_hasDtor : TDerivesP Δ Γ (.dtor i j A) j' → HasDtor A
```

`TDerivesP.dtor_hasDtor` inverts `TDerivesP` (one constructor, which carries `hA`), not `CDerives`.

### 2.3 The obligations of #746 item 3

- **Elaboration.** A constructor `C(e…)` ↦ `(payload, mint ())`; a written `match` ↦
  `let (p, t) = v; burn t; …`. The declaration's type is the kernel type; no table outside the
  type holds the fact, so `Class.of` reads it.
- **`HasDtor` and `dtorB` refuse it**: `HasDtor` has no `opq` constructor and `dtorB _ (.opq _) =
  false` already (`Steps.lean:178`).
- **Borrows.** `Imm̲ 'b (A ⊗ Tok) = Imm̲ 'b A ⊗ Unk`, so fields read through a view (`loadField`)
  and the token's view is forgotten. `Mut`: `withswap` hands the whole value over and takes one
  back.
- **Containers and fields.** `HasDtor.tensor/.sum/.box/.ref/.array/.mu` ask every leaf, and
  `persistent` is conjunctive, so a declared field makes the container linear with no derived
  drop. `getAt` needs the discarded fields `Forgettable` (section 3), so a projection that would
  discard a declared field has no derivation.
- **Across an abort.** `N` is live across an abortive computation exactly when its payload is
  `VTy.Drop` (abandoned, decision 2); otherwise `[let]`'s `hW` fails and `[then]`'s `finalOf` finds
  no destructor, and the program is refused.
- **`fundamentalC`/`adequacyC`.** Two compatibility lemmas (`mint`, `burn`) and the `tok` model.
  Their statements are unchanged.
- **Guarantee.** No *derived* drop: the checker cannot insert one (`TDerivesP.dtor_hasDtor`), an
  abort abandons it only under 1.3, and `[then]` has no destructor to run. An explicit `burn` is a
  use; the gate step (section 7, step 3) pins that the elaborator emits `burn` only at a written
  `match`.
- **`!N`.** `.bang A` is persistent for every `A`. Q10.

### 2.4 Surface: explicit consumption, `finally`, resources as effects (user direction 2026-10-30)

A type with no derived drop must be readable and easy to use. The kernel already has everything
this needs, so this section adds surface forms and errors only. Spellings are provisional.

- **A field keyword** in the data declaration marks a field "needs an explicit close". It
  elaborates to L-T: the field is stored with a `Tok`, so the field has no derived drop and every
  type that contains it has none (2.3, *Containers and fields*). The keyword is the only way a
  program writes L-T. The declaration may also name the function that closes it. The name is used
  only by errors and by `finally`, and nothing calls that function unless the program writes the
  call.
- **`finally` on a `with`** (user, 2026-10-30: "the syntax should be with open finally"):
  `with h { … } finally D`. It elaborates to the kernel's `[then]` around the handled computation
  (`M then x. N unwind D`, SPEC §27). `D` runs at its own row, so it may perform IO, and the same
  written `D` runs on the normal exit. Both placements are checked terms, and `D` is a call the
  program wrote, so this is not a drop. It is decision 2's "cleanup goes in a finaliser", made
  readable. The parser's raw `unwind (D)` (`Parser.lean:2430`) is the existing hook.
- **Resources are effects** (user, same day: "File IO is the _classic_ effect and if we aren't
  modeling it as an effect we have gone very wrong"). IO already is: `lib/sys.bc` declares the
  effects, and the platform handlers (`lib/wasi.bc`) hold the stream cells as their state. A file
  is opened by a
  handler, `with open(path) { … }`. The open file is the handler's state, and `read`/`write` are its
  operations, so the program holds no handle and owes no close. The handler's definition closes the
  file on both exits: on return it closes, and on an abort it closes through `[then]`. The handler
  is written once, in the library. File IO itself is a later feature, outside #746. It will also
  need to decide how a body names one of two open files (named instances or passed capabilities,
  System C). #746 supplies only `finally` on `with`.
- **Errors point at the fix.** A value with no derived drop that is unused at the end of its scope,
  or live across an abort, gets one message that names:
  - the value and its type;
  - the field that carries the obligation;
  - the fix: pass it to the function that consumes it before the scope ends.
- **Not this:** an implicit call of the named close function at scope end without a written
  `finally`. That would be a non-derived drop. Every drop stays derived; a close runs only where
  the program wrote it.

---

## 3. Vocabulary

### 3.1 Renames and rewordings

Spellings marked *(prov.)* are provisional; the user said spelling is not blocking. "(removed
word)" stands for the word recorded in the introduction.

| place | today | becomes |
|---|---|---|
| `Core/Records.lean:288` the predicate, `:301` `dropT`, `:309` `dropT_wf`, lemmas at `:347` and `:364`; `Core/Dtor.lean:448`; `Core/Aff.lean:128`; `Core/RecordPrograms.lean` | named after the removed word | `Forgettable`, `forgetT`, `forgetT_wf`, `forgettable_immReborrow`, `forgettable_valTy`, `hasDtor_of_forgettable`, `not_forgettable_aff` (v1's rename stands: "a no-op consumer exists") |
| `Core/Types.lean:39` `Qual.aff`; parser token `aff` (`Parser.lean:772`, 248 uses in 25 corpus files and 8 docs); `Frontend/Syntax.lean:68, 755` | the default qualifier | `Qual.cancel`, token `cancel` *(prov.)*: "has a cancel branch". 162 uses in 22 `Core/` files, 18 in `Frontend/`, 1 in `Backend/` |
| `Kinds.lean:297–301` `qualWord`; `Effects.lean:3886` | `"linear"`, the removed word, `"unrestricted"` | `"must resume"`, `"cancellable"`, `"unrestricted"` *(prov.)*. Changes `corpus/kinds.expected` and 17 `corpus/reports/*.txt` (section 6) |
| surface `ctl` / `linear ctl` / `multi ctl` | default / `lin` / `unr` | keywords unchanged until spelled (Q12). The κ of both `ctl` and `linear ctl` is linear; the prose says "must resume" and "cancellable" |
| `Core/Aff.lean`, `AffRules.lean`, `AffPrograms.lean`; `affT`, `affBox`, `affC`; `lib/aff.bc` `Aff[A, B]<'c>`, `aff_new`, `aff_call`, `aff_call_mut`, `aff_close`, `aff_of_fn`, `aff_once`; `corpus/aff-*.bc`, `corpus/reject/aff-*.bc` | named for the removed word (decision 60, provisional) | a name for "a closure with a `close` observation", for example `Clo[A, B]<'c>` *(prov.)*; files and Lean names follow. It is a linear type with a derived drop (`hasDtor_aff`) |
| "three kinds of function" (SPEC §22, `lib/aff.bc:9–16`, `Core/Aff.lean`) | linear / (removed word) / persistent | linear with no derived drop `A ⇒ B`; linear with a derived drop (the closure); unrestricted `!(A ⇒ B)` |
| `Core/Relation.lean:250` `Persistent (Γ : Ctx VTy)` | "every live slot `!`" | renamed `Ctx.Banged` *(prov.)*, not widened (Q7) |
| `Core/EffRules.lean:957` `Row.Weak`, `Row.weakB` | a row with a cancellable or unrestricted operation | `Row.Cancels`, `Row.cancelsB` *(prov.)*: "weakening" names the structural rule only |
| `Core/EffRules.lean:1041` `VTy.Drop`, `Ctx.Drops`, `dropB` | holds no `own` cell | kept; its doc says "abandoned by an abort (SPEC §19), not a drop"; renaming is Q8′ |
| `Frontend/Elab/Tir.lean:33–48` `Class` | `persistent / dtor / linear` | section 1.6 |
| SPEC §12 class 1 (`SPEC.md:1225–1231`) | "forgettable … genuinely (removed word)" | "Forgettable types: the types whose destructor does nothing (the unrestricted ones and the borrows)" |
| SPEC §12 class 2 (`:1232–1245`) | "These are linear" | unchanged: correct |
| SPEC §12 class 3 (`:1246–1249`) | "strictly linear" | "linear with no derived drop" |
| SPEC §12 opening (`:1212–1216`) | cites an experiment directory named with the removed word | cites `Core/Dtor.lean` (Q13 for the directory) |
| SPEC §19 table (`:2697–2702`) | weakening/contraction per qualifier, one row with the removed word | columns "class" and "its one use": `lin` linear, resumed; cancellable linear, resumed or cancelled (the cancel a derived drop when pure); `unr` unrestricted. The *relevant* row and its *Open* go: the kernel has two classes |
| SPEC §19 `:2709` | "the textbook encoding of a (removed word) type as `A & 1`" | "a linear type with a cancel branch, the `A & 1` encoding" |
| SPEC §18, §19, §27 (`:2424–2427`, `:2716`, `:2754`, `:2987`, `:3032`, `:3061`, `:3261–3308`, `:3387–3480`), §25 (`:4564–4630`), §29, §30, §48–§52 (`:4784–4963`, `:5493`, `:8607–8925`), `:9710` | the qualifier word | "cancellable", or "must resume or cancellable" |
| SPEC §15 (`:1811`, `:1855`, `:1995`) | `yield` "is (removed word)"; "a (removed word) continuation has no destructor" | "`yield` is cancellable"; "a cancellable continuation at a non-empty cancel row has no derived drop" |
| SPEC §22 (`:4097–4264`), §2 table (`:132`) | the closure's name and the coercion names | renamed with the closure |
| SPEC §5 (`:333`) | the projection predicate | `Forgettable` |
| SPEC §30 (`:5572`) and book `guide/async.md:89` "a task is a linear value: run to the end or cancelled"; SPEC §52 (`:8925`) "a dropped task leaks ((removed word), not cancelled)" | contradict each other | "a task is linear, with a cancel branch"; §52: "a task dropped without its cancel leaks" |
| SPEC changelog (`:10577–10778`) | past versions | Q14 |
| `docs/decisions.md` 23 (`:59–64`), titled "Implicit destructors, not (removed word) types" | | title "Implicit destructors are derived drops of linear values"; the body loses "only the forgettable types … are (removed word)" and "the opt-out is a `linear` binder", and records decisions 1–4 |
| `docs/decisions.md` 55 (`:694`), 56 (`:704–712`), 60 (`:780–782`), 63 (`:824`) | the qualifier word; the closure's name | "cancellable"; the closure's new name |
| `Frontend/README.md:347, 360`; `Core/README.md`; `scripts/AxiomCheck.lean:263, 358`; `Paper/S3_Dynamics/Definitions.lean:328–503` (comments on the tag `1`) | the qualifier word | "cancellable" |
| corpus comment headers (`aff-*.bc`, `async-r1-cancel-finaliser-writes.bc:4`, `pending/gen-*.bc`) | prose | reworded |
| `docs/*.md` (about 60 files: `effect-model.md`, `fnmut.md`, `theory-index.md`, `effects-state/`, `effects-tr/`, `research/`, `prior-art-*.md`, …) | our classifications, and descriptions of other systems | our classifications reworded; citations of other systems' type classes are Q15 |

The book (`book/src`) has no use of the removed word.

### 3.2 Error messages

| site | message today | becomes |
|---|---|---|
| `Frontend/Check/Steps.lean:515` | "`x` is declared `linear` and is not consumed in its scope" | removed with the flag |
| `Steps.lean:518`, `:500` | "… its type `A` has no destructor" | "… its type `A` is linear and has no derived drop" *(prov.)* |
| `Steps.lean:516–517` | "… cannot be dropped where its scope ends" | unchanged |
| `Steps.lean:814–816` | "live across a computation that may abort, and its type has no destructor" | "… its type is linear with no derived drop, and an abort abandons only a value that holds no owned cell" |
| `Steps.lean:488–489` | "used twice here, and its type is not persistent" | "… and its type is linear" |
| `Checker.lean:680–682` | "operations that resume once ((removed word) or linear) …" | "operations that resume at most once (cancellable or must-resume) …" |
| `Elab.lean:405–406`, `Program.lean:150–151`, `Effects.lean:3879–3880` | "an abortive operation is (removed word) …", "`1.0 aff … ~> 0`" | "an abortive operation is cancellable, `1.0 cancel … ~> 0` (decision 63)" |
| `Sugar.lean:136` | "`&c` cannot be used in an annotated or `linear` binding" | "… in an annotated binding" |
| `Sugar.lean:596–597`, `:5119–5120`; `Data.lean:427–440` | "… which has no destructor" | "… which is linear with no derived drop" |
| `Checker.lean:530`, `Program.lean:177`, `Sugar.lean:2406, 2454, 3554, 3705, 4681, 4974`, `Lint.lean:143` | "… is not persistent" | "… is linear" where the message classifies; "persistent" stays as the predicate's name |
| `Parser.lean:774` | "a qualifier `lin`, `aff` or `unr`" | "`lin`, `cancel` or `unr`" *(prov.)* |

### 3.3 Binder `linear` (item 1)

v1's removal list stands, re-checked at b566c459.

| site | change |
|---|---|
| `corpus/forms.bc:43–44`, `corpus/join-bind-head.bc:17` (and header lines 1, 6), `corpus/implicit-drops.bc:67` | plain binders |
| `corpus/reject/linear-unused.bc` | deleted; replaced by a declared-type reject program (`corpus/reject/linear-*`, step 3) |
| `Frontend/Tests.lean:88–89` `rt_linear` | deleted; a declaration round trip comes with step 2 |
| `Frontend/Syntax.lean:677–679` `Comp.bind … (lin : Bool)` | field removed |
| threaded only: `Print.lean:191, 290–292`; `Syntax.lean:1015`; `Parser.lean:1195, 1265–1272, 2005`; `Elab/Divisions.lean:70`; `Hygiene.lean:113–116`; `RenameLife.lean:178`; `Respan.lean:180`; `Meta.lean:377–379`; `Subst.lean:176`; `LoopLend.lean:91, 152–156, 324–330, 389, 432–433, 543–546`; `Effects.lean:896, 1023, 1727, 1784, 1844, 1849, 1857, 3625, 3729–3736`; `Sugar.lean:206, 243, 772–790, 817, 857, 965, 1187, 1249–1282, 1473, 2261, 3348–3382, 4270–4303, 5890–5892` | field dropped |
| behaviour: `Parser.lean:2061–2070` (the only place `lin = true` is set) | branch removed |
| behaviour: `Effects.lean:1738` `bindValue` (`if !lin`: fuse with the call's binding) and `:1866–1867` (`if lin`: keep a separate binder) | the `!lin` path always |
| behaviour: `Sugar.lean:135–136` | the annotated half stays |
| behaviour: `Check/Checker.lean:414–429, 750–766`; `Check/Steps.lean:514–515, 546–550, 572–578, 864–867` | argument removed; `own := !A.persistent && hasDtorB A` (`Env.pushOwn_own`) |
| SPEC §12 *Insertion policy* "not declared `linear`", *Opt-out*, *Open* "`linear` on other binders"; `SPEC.md:7347, 10227` | removed; the entry points at declared types (section 2) |
| `docs/syntax-core.md:232, 350, 905`; `docs/surface-cbpv.md:330, 945`; `docs/internals/elaboration/implicit-destructors.md:66–71`; `docs/prior-art-rust-wishlists.md:463` | removed or pointed at declared types |

Kept: the lexer keyword `linear` (`Lexer.lean:59`, for `linear ctl`), `Qual.lin`, and every
`Class`/`isLinear` use, whose meaning is now `Linear ∧ ¬ HasDtor`.

### 3.4 Other meanings of "linear" (Q6, resolved)

The rule is about classifications. "Linear" stays where it does not classify a type, value,
binder or continuation: "linear time" (`corpus/leetcode/graphs/0128-…bc:4`), "linear probing"
(`SPEC.md:6471`), "linear recursion" (`SPEC.md:3906, 8838, 9545`), "linear repair"
(`corpus/aoc/2020-08.bc:12`), the van Laarhoven "linear lens" (`docs/prior-art-optics.md:135`).
"Linear state", where it describes a value, is a classification and follows the rule. The
lifetime order is never called linear (standing precedent).

---

## 4. Decisions applied

| v1 question | decision | resolution |
|---|---|---|
| Q1 weakening with an effect | 1 | a derived drop is pure at the row (`dtorE_effFree`); a cancel at a non-empty cancel row is a use, not a derived drop (`kTy_cancel_hasDtor_iff`). Effectful destructors stay SPEC §12 *Open* |
| Q2 abandonment at an abort | 2 | not a drop: `⊤`-like absorption of a `VTy.Drop` context (1.3). Opaque host types are linear and may be abandoned. `VTy.Drop` is not narrowed |
| Q3 contraction at `Imm` | 3 | `Imm` is linear with a derived copy (`copy_derives`); v1's `Contr` and `Weak` are gone |
| Q4 declared types | 4 | L-T (section 2); the guarantee is "no derived drop" |
| Q5 a declared value across an abort | 4, 2 | abandoned when its payload is `VTy.Drop`, refused otherwise (2.3) |
| Q6 other meanings of "linear" | the rule | 3.4 |
| Q7 `Persistent (Γ)` | the STOP on widening | renamed (`Ctx.Banged` *(prov.)*), not widened |
| Q8 `Forgettable` and `VTy.Drop` | 2 | two notions: `Forgettable` = a derived drop with no action; `VTy.Drop` = abandoned at an abort. Two inductives kept, with `forgettable_iff : Forgettable A ↔ A.Drop ∧ HasDtor A` as a target (read off the constructors, unproved). Renaming `VTy.Drop` is Q8′ |
| Q9 checker strategy | the brief | `dtorB_complete`, fallback: `HasDtor` defined by `dtorB` (1.6) |
| Q10 `!N` | does not follow | open (section 9) |

---

## 5. Every site that decides a drop, a copy or a class

Key: **K** reads a kernel fact (named); **E** emits a term the checker then types; **R** rebuilds
the decision from the erased term or a layout, without reading the fact; **F** is a finding.

### 5.1 Checker (`Frontend/Check`)

The checker builds the typed derivation (`TTied`/`TDerivesP`, erased to `CDerives` by
`checkProgram_sound`); each decision below carries the proof of its kernel premise.

| site | decides | |
|---|---|---|
| `Steps.lean:56–300` `dtorB`, `hasDtorB`, `:139` `dtorB_sound` | `HasDtor` (one direction) | K; `hasDtorB_iff` target |
| `Decide.lean:748–769` `dropB`, `dropB_sound` | `VTy.Drop` (one direction) | K; `dropB_iff` target |
| `Steps.lean:577–578` `Env.pushOwn` | which slots are owed (the insertion *policy*) | K (`persistent`, `hasDtorB`); the `lin` flag is surface-only and goes. Target `Env.pushOwn_own` |
| `Steps.lean:671–686` `dropOne` → `Rules.lean:477` `rDrop` | inserts `dtorE A xᵢ` | K: `hasDtorB_sound` → `drop_derives`; `effFree`/`closedAt` checked per use (`dtorE_effFree` target) |
| `Steps.lean:688–690` `dropOwed` | the owed slots a terminal leaves | K (masks of the typed term) |
| `Steps.lean:805–818` `finalOf` | `[then]`'s finaliser: destructors of non-persistent live slots | K (`hasDtorB`) |
| `Steps.lean:864–895` `effBind` | `[let]` (every slot `dropB`, and `!` at an unrestricted row) or `[then]` | K (`dropB_sound`, `isBangB_sound`, `Row.weakB_iff`) |
| `Steps.lean:478–489` `firstOverlap`, `splitErr` | a slot used twice is refused unless persistent | K (`SplitP.dup`'s premise) |
| `Rules.lean:536–538` `[raise]`; `Checker.lean:723` | the argument `dropB` | K (`effRaise`'s `hd`) |
| `Rules.lean:318–338`, `:640–674`; `Checker.lean:451–530` | `!Γ` at promotion; handler clauses use persistent slots | K (`Persistent Γ`, `VTy.persistent`) |
| `Weaken.lean:99–261`, `TShift.lean:41–43` | a `def` body placed at a use absorbs persistent / `dropB` slots | K (`deadP_ins`, `soloP_ins`, `live_ins` with `dropB_sound`) |
| `Copies.lean` (§10) | an implicit deep copy at a persistent type needs `clone(x)` | K (`TDerivesP.copies` masks, `VTy.persistent`) |
| `Consts.lean:145–155` | a finaliser source needs `HasDtor` and an effect-free closed `dtorE` | K |
| `Steps.lean:383` | reads `lin` off a `κ` type `U((B ⊸ _) & ⊤)` | K (`kTy`) |
| `Masks.lean:282` `SplitMasks.both_persistent` | a slot both parts use is persistent | K |

No checker site decides a guarantee itself.

### 5.2 Elaborator and sugar (`Frontend/Sugar.lean`, `Frontend/Elab`)

No elaborator site emits `copy`, `copy_bang` or a `forget` constant on its own. Drops are dead or
unused binders that the checker then drops (5.1), and cancels are `(force κ).2` arms the checker
types.

| site | decides | |
|---|---|---|
| `Elab/Tir.lean:42–43` `Class.of`; `Sugar.lean:539` `isLinear` | the class | K (`persistent`, `hasDtorB`); `Class.of_*` targets |
| `Sugar.lean:547–555, 591–597` (`termParts`, `loopCxOf`) | a div body's residual keeps its linear components; the others are left for the checker's drop | K → E (alias tracking by `copyOf?` is R, below) |
| `Sugar.lean:802–809` `dret`; `:1204–1230` `mAbort` (`:1226`) | what a closed loop hands back; refuses an unnamed linear leaf | K → E |
| `Sugar.lean:1174–1176, 1340, 1381` `mClose`/`closeSrc`; `:1237–1240, 1307`; `:5145–5149` `leave` | cancels held loops and generators by their `close` or cancel arm | E |
| `Sugar.lean:1416` | an iterator's residual bound dead for the checker's drop | E |
| `Sugar.lean:974–986` `closeGiven` | which residual is which capability, by type equality | R → E (the checker types the result) |
| `Sugar.lean:2404–2454` field read; `:3697–3706` `*e`; `:3549–3556` `clone`; `:4679–4682, 4972–4975` `for` over an owned array; `:3925–3930` fieldwise lend; `:1123–1126, 4604–4605, 5069–5070` externs across a loop; `Elab/Meta.lean:59` | copy only at a persistent type | K (`Class.of`, `persistent`) |
| `Sugar.lean:2669–2673, 4636–4648, 4943–4957` | `array_copy` of an `imm` view in templates | E (a kernel constant, `arrCopy`) |
| `Elab/Data.lean:832–833, 873–881` | a `box` pattern emits `free`; wildcards are left for the checker | E |
| `Elab/Data.lean:380–440` `pClass` | data fields lie in §6's class `P` | K (`FoldP.PB`, `pBodyB`) |
| `Elab/Effects.lean:1738–1747`, `:1866–1867` `bindValue`/`trBind` | binder fusion, which `lin` switches off | E; the `lin` branch goes (3.3) |
| `Effects.lean:2465–2478` `alone` | a `with` state block answers its result alone, the scoped cell dropped | R (syntactic test) → E |
| **F6** `Sugar.lean:4505`; `Effects.lean:466–471` `OpDecl.abortive`; `:393–396` `exhEff?` | abortive = answers `0` and not `lin` | R: restates `Core/ClauseKinds.lean:374` `isAbortive` on surface data. Should call it on the elaborated signature. Not unsound: the clause type is checked |
| `Effects.lean:3878–3880` | refuses `multi ctl … -> never` | R (a restriction; mirrors decision 63 and `Elab.lean:405`) |
| `Effects.lean:2035–2038` | a stateful handler's `κ` is only resumed or dropped | R (a restriction) |
| `Effects.lean:1083–1100` `Cx.copy`; `Syntax.lean:1154–1159` `copyOf?`; `LoopLend.lean:150–156` | `x <- return y` as an alias | R (no duplication emitted) |

### 5.3 Backend2

Convert places `.copy`/`.drop` by its own structure; Lint (`Lint.lean:96–152`) then re-checks every
one by its LIR type, which `ofV` keeps from the checked type (`ofV_persistent`, `ofV_drops`; that
the LIR type is the checked type's image is `UNPROVED:` at `Layout.lean:697`).

| site | decides | |
|---|---|---|
| `Lint.lean:57–62` `copyable` | `persistent` (`SplitP.dup`, `copyable_ofV`), `.imm` (`copy`), `.fam (.imm)` (`arrCopy`) | K, at the type. **F4:** admits an `imm` copy at any site, which the kernel licenses only at the constant |
| `Lint.lean:64–73` `droppable`: `persistent` | `DeadP.drop`, `SoloP.skip` | K |
| `droppable`: `t.drops` | `VTy.Drop` (`ofV_drops`) | K at an abort (`effLet`'s `hW`, `effRaise`). Outside an abort, the forget constants license `imm`/`mut`/`unk`; **HARD STOP F2:** nothing licenses `.opq` there (no constant, no `HasDtor.opq`). Lint does not check that the drop is at an abort |
| `droppable`: `.fam (.imm _)` | `arrForget` | K |
| `droppable`: `.fam (.mut _)` | cites `forget_fam_compatX`, which Core instantiates only at `imm` | **F7:** the licence is `HasDtor.arrayMut` (`Dtor.lean:436`), whose `dtorAt` is `idx` then `forget` (`Dtor.lean:168`), at a `dtor` node. Mis-cited and broader than the kernel's (any site). A borrow, so no owned value is lost |
| `Lint.lean:149` + `Prog.stackKs`; **`Convert.lean:1329`** (`k'`), **`:1388–1389`** (`kv`) | drops a level's suspended computation, a closure | **HARD STOP F3.** No kernel rule. The `UNPROVED:` justification (`:1380–1386`) reads layout closure classes (`stackedOf`, `:3790`; `calleeCodes`), not types |
| `Convert.lean:359–361` `leaf`; `:379` (a live slot neither mask uses) | drops | R (from masks). The kernel says these are persistent (`DeadP`) or absorbed by `⊤`/`absurd`; no theorem says a slot neither mask uses is one of these. Lint checks the type |
| `Convert.lean:374` | copies a slot both masks use | K (the `masks` fact; `SplitMasks.both_persistent`) |
| `Convert.lean:853` `abortK`, `:888` `cancelK`, `:2682` `effLet` abort | drops the frames' captured slots at an abort or cancel | R: `effLet`'s `hW` and `effHandleV`'s `DeadP Γ₁` not read; Lint checks the type |
| `Convert.lean:1190` (`genMach` cancel at `⊤`), `:2276–2277` (κ cancel at `⊤`) | drops in code the comment says never runs | R; Lint would reject them if emitted (`k : thunk`). Should be `unreachable` |
| `Convert.lean:2622` `nilDead` | drops every live slot | R: the kernel's `Ctx.Dead` says none is live; not asserted |
| `Convert.lean:1890–1945` `genDtor` | the destructor generated from the `dtor` node's type | K (`dtor:type`, the `drop_derives` site); generated from the type, not compiled from `dtorE` (`UNPROVED:` `:1900` at `μ`); the fallthrough `.drop x` (`:1945`) also covers `fam (mut)` |
| `Convert.lean:3515–3517` | `copy`/`arrCopy` → `.copy`; `forgetImm/Mut/Unk`, `arrForget` → `.drop` | K (the typed constant node) |
| `Convert.lean:1146, 3399, 3783`; `Layout.lean:396, 642`; `Flow.lean:119`; `Driver.lean:177` | ownership facts read off layouts | R, each marked `UNPROVED:` |
| `Lower.lean:300–304, 838–840, 901–967` | a drop's runtime action by layout class (trivial / closure environment / boxed field) | ordinary lowering of a decided drop |

### 5.4 The old backend (`Backend/`)

The checker hands it only the erased `Expr` (`Backend/Driver.lean:103–104`); no site reads
`persistent`, `Drops`, `HasDtor` or a qualifier. The closure interpreter does not forget entries
silently: it throws on a variable left unconsumed (`Clos/Interp.lean:326`, `:542`) or used twice
(`:97`, `:471`), so every discard is an emitted `.drop`. `deepCopy`/`deepDrop`
(`Clos/Interp.lean:108–138`) copy and free structure but never cells: a wrong copy aliases and a
wrong drop leaks, neither double-frees, and the live-cell count against the source run catches a
leak.

| site | decides | |
|---|---|---|
| `Clos/Convert.lean:200–213` `plan2` (applied at 667–832) | a variable free in two sequential parts is copied for the earlier one | R (free indices). Covers `SplitP.dup`, the `copy` constants and the erased bodies of axioms such as `withbor`'s `(x, f () x)`, without telling them apart |
| `Clos/Convert.lean:677, 683–685, 698–700, 824, 857, 872, 996` | unused binders and one-armed variables dropped; `:996` an unused extern (possibly a capability) | R (non-occurrence). In a checked term a linear slot fails to occur only where it is absorbed (1.3) |
| `Clos/Convert.lean:740` | handler qualifier tags `qs` discarded; `κ` copied when resumed twice, dropped when unused | R. In a checked term only an `unr` `κ` is resumed twice or left unused (a cancellable `κ` with a derived drop is cancelled by its inserted `dtorE`) |
| `Clos/Capture.lean:1013` `cancelArm` | at a cancel, every live non-finaliser variable dropped | R (the cancel's premises not read) |
| `Clos/Unwind.lean:214–217, 295` `propagateOn` | on a raise, the rest of the level dropped | R (`effLet`'s `hW` not read) |
| `Clos/Unwind.lean:237`, `Capture.lean:980–981` | error payloads dropped | R |
| `Clos/Capture.lean:196–265` | clause tables and `hr` copied and dropped | K by citation: `clausesTy_persistent` (`EffRules.lean:1373`) |
| `Clos/Interp.lean:336–438`, `Flat/Lower.lean:978–1056, 1319–1434`, `Clos/Convert.lean:255–260` | step closures copied per slot or level | R (justified only if `!`) |
| `Clos/Interp.lean:549`, `Flat/Lower.lean:1125` | `main`'s value dropped at exit | R |

These sites are all "rebuild, don't read" (CLAUDE.md, *Later stages read the kernel's facts*).
Each would be licensed if the backend carried the typed term's rule to the site. I have not found
a checked program where one of them copies or drops a linear value no kernel rule licenses, and I
have not verified that none exists.

### 5.5 Findings, with the statement that should license each

| # | site | statement |
|---|---|---|
| **F3 (HARD STOP)** | `Backend2/Convert.lean:1329, 1388–1389`; `Lint.lean:149` `stackKs` | one of: (a) a kernel derived drop at the stack machine's closure type, the machine's `k` as codata `νX. … & F 1` whose `close` frees nothing because its state is in the level's frame, so the drop is a `dtor` node that `drop_derives` licenses (`theorem stackK_hasDtor : HasDtor (stackKTy …)`); (b) a named assertion in the trusted base (a `PinLaw`-style field, `StackLaw.k_drop`: "a level's `k` over a stack address alone holds no resource but that frame"); (c) the drop removed, the stack step consuming `k` |
| **F2 (HARD STOP)** | `Lint.lean:70` `t.drops` at `.opq` outside an abort; reached at `Convert.lean:3640–3659` `epilogue` and `Clos/Convert.lean:950–968` | the backends compile the checked `run_io` wrapper, the object of `externs_every_run` (`Core/Stdio.lean:794`), instead of `main` plus a prologue and epilogue of their own. The harness externs (`mk_*`, `take_*`) become host functions like the operations, at the same trust boundary: each meets its extern's contract (`ExternsMeet`). `take_input`'s `Bytes` and the clock's and arguments' results are then dropped by `DeadP` inside the checked term, and no `.opq` value is dropped. Then Lint admits a `.drop` at an `.opq` type only at an abort site |
| F4 | `Lint.lean:57–62` `copyable` at `.imm` anywhere | `DerivedCopy` + `copy_derives` (1.4), under which a copy at any site is a derivation |
| F5 | `Convert.lean:379`, `:2622`, `:853`, `:888`, `:2682`; `Clos/Convert.lean`, `Capture.lean:1013`, `Unwind.lean:295` | carry the typed term's rule (`DeadP`, `Ctx.Dead`, `Ctx.Drops`) to the site; a lemma `SplitMasks.neither_absorbed`: a live slot neither mask uses is persistent, or the node absorbs it (`topI`/`zeroE`) |
| F6 | `Sugar.lean:4505`; `Effects.lean:393–396, 466–471` | call `isAbortive` (`Core/ClauseKinds.lean:374`) |
| F7 | `Lint.lean:72–73` `.fam (.mut _)` | `HasDtor.arrayMut` at a `dtor` node only; the citation corrected |

---

## 6. Programs whose result changes

| program | change | why | checked |
|---|---|---|---|
| `corpus/reject/linear-unused.bc` | rejected → accepted (leaves `reject/`) | binder `linear` removed (the user's decision, #746 item 1). `r : Ref B` has `HasDtor (.ref _)`, so the checker drops it by `drop_derives`. The kernel already licenses this drop; the flag was a surface restriction | *run*: with `linear` removed it checks (`assurance: unconditional`), and `interp` prints `()`, `live 0` |
| `corpus/join-bind-head.bc` | none | the flag at `i32` does nothing | *run*: checks; `interp` output equals `join-bind-head.out` |
| `corpus/implicit-drops.bc` | none | `q` is consumed by `free` | *run*: checks; `interp` output equals `implicit-drops.out` |
| `corpus/forms.bc` | printed form at lines 58–59 | parse-only (`-- check: parse-only`) | *run*: `bcc print` differs only there |
| `Frontend/Tests.lean:88` `rt_linear` | deleted | the form no longer parses | read |
| `corpus/reject/core-effects-unr-abort.bc:3`, `effect-multi-never.bc:3`, `async-r1-spawn-captures.bc:1`, `async-r1-unr.bc:1` | `-- expect:` text | the messages of 3.2 | read |
| `corpus/kinds.expected` (497 of 500 lines) | the qualifier word | `qualWord` | read |
| 17 `corpus/reports/*.txt` (`async-map`, `async-scheduler`, `clause-captures`, `comp-param`, `div-*`, `effects-*`, `io-task`, `rec-*`) | "(ctl, (removed word), …)" and "op (removed word):" | `Effects.lean:3886`, `qualWord` | read |
| 25 corpus programs and 8 docs using `n.i aff …` in core rows | source text only | the token rename | read |
| `corpus/aff-*.bc`, `corpus/reject/aff-*.bc`, users of `lib/aff.bc` | file and function names | the closure rename | read; outputs unchanged except any reject `expect` line that quotes the type's name, to be checked at the rename |
| declared-type programs | new | step 3's `corpus/reject/linear-*` | — |

No other program changes acceptance or output. Every change other than `linear-unused.bc` is text.

---

## 7. Build order

Each step lands with its kernel statements proved, or stops.

1. **Removal and vocabulary** (items 1, 2).
   - Kernel: `Core/Classes.lean` (1.1–1.5): `Unrestricted`, `Linear`, the three `_iff` lemmas,
     `DerivedDrop`, `dtorE_effFree`, `dtorE_closed`, `DerivedCopy`, `copy_derives`, the `kTy`
     lemmas; `forgettable_iff`. The renames of 3.1 (`Forgettable`, `Qual.cancel`, the closure,
     `Ctx.Banged`, `Row.Cancels`).
   - Checker: `dtorB_complete`, `dtorB_completeA`, `hasDtorB_iff`, `dropB_iff`, `Class.of_*`,
     `Env.pushOwn_own` (or the fallback).
   - Binder `linear` removed (3.3); messages (3.2); SPEC, decisions and docs (3.1); the goldens of
     section 6.
   - F2 (5.5): both backends compile the checked `run_io` (and the loop wrapper), with the harness
     externs as host functions meeting their contracts; their own prologue and epilogue go. Then
     Lint admits a `.drop` at an `.opq` type only at an abort site.
2. **Declared types, L-T** (item 3).
   - Kernel: `Opaque.tok` and its model, `CDerives.tokMint`/`tokBurn` with compatibility lemmas,
     `tok_linear`, the closure lemmas, `decl_linear`, `decl_imm_drop`, `decl_mut_drop`,
     `TDerivesP.dtor_hasDtor`. The SPEC §11, §12 and §42 entries first.
   - Elaboration of the declaration and its `match` (2.3).
   - The surface of 2.4: the field keyword, `finally` on `with` over `[then]`, and the error.
   - **Before building:** name a program that needs a declared type with no derived drop and
     cannot be written as a handler. A resource is a handler (2.4), so files are not such a
     program. If there is none, this step waits.
3. **Gate step** (item 4).
   - Kernel: each pinned site cites the rule it emits (`drop_derives`, `copy_derives`, a constant,
     `topI`/`zeroE`, `effLet`'s `hW`). Every `burn` the elaborator emits is at a written `match`.
     F4–F7 (5.5) fixed, or each given its `UNPROVED:` with the statement it would need.
   - `linear ctl` renamed (Q12, revisited).
   - `corpus/reject/linear-*`: a declared type paired with every construct that inserts operations
     (implicit drop, `for` copies, field read, E5, `[then]` finaliser, an abort across it).
4. **F3** (item 5). Kernel: 5.5's F3 statement, (a) or (b), or the drop removed. `Prog.stackKs`
   deleted.
5. **Book chapter: linear values** (`book/src/guide/linear.md`, after *Ownership and borrows*).
   It describes what steps 1–4 built and nothing else, and every example runs as a book program.
   - The language is linear: a value is unrestricted or linear, and there is no third class.
     Every drop is derived, from the type's structure; there are no hand-written drops. Most
     linear values still feel droppable because the checker inserts their derived drop
     (`drop_derives`) where their scope ends. A borrow `imm` is linear with a derived copy
     (`copy_derives`).
   - Linear types with no derived drop: capabilities, must-resume continuations, one-shot closures
     that hold one, and declared types (L-T). What the checker says when one is left unused, and
     how to fix it.
   - Resources are handlers: `with open(…) { … }`, and `finally` on a `with` for the program's own
     cleanup. Values with no derived drop, and the error that points at their consumer (2.4).
   - Writing programs that want to forget a value: keep the type's fields droppable so its drop
     is derived, give a task or continuation a cancel branch (`cancel`), or consume the value
     with a function written for it. Each one is described as the derivation it inserts or the
     consumption it writes, not as a different kind of type.
   - What an abort does to the values in scope (decision 2: they are abandoned, not dropped), and
     where cleanup goes (`[then]` finalisers).
   - A comparison with Rust's affine types. This is the only place the word appears, as a
     citation (Q15).
   - The opening of `guide/ownership.md` ("copyable or owned … this is its model") is rewritten to
     match: Rust's model is affine, and this language's is linear with derived drops.

---

## 8. NOT-do list and tempting shortcuts

Each is a **STOP**: stop and report. Do not take it.

1. **A third class under another name.** No `Weak`, `Droppable`, `Owed` or `Cancellable` *class*
   of types. Derived drop, derived copy and a cancel branch are properties of linear types.
2. **Defining a class by an elaborator mechanism**: "linear means not owed", "has a drop means the
   checker inserts one", or reading the class from `Data.Table`.
3. **A binder flag under a new name** (`must_use x <- M`, `#[linear]`, an annotation setting
   `own := false`).
4. **Checker-only obligations.** A refusal in `Frontend/` of a drop or copy of a declared type with
   no kernel fact behind it. The refusal is "`HasDtor` fails" or "no rule applies".
5. **Enumerating per program**: special-casing `Txn`, E5 for one record, or a new exemption list.
6. **Widening `Persistent Γ`**, making `Imm` unrestricted, inserting implicit `imm` copies,
   narrowing `VTy.Drop` (decision 2 keeps it), or inserting a cancel as a derived drop at a
   non-empty cancel row.
7. **A pure destructor for a cancellable `κ` at an effectful row** (dropping its cancel without its
   finalisers). The lends in `κ` must end by unwinding.
8. **Changing `dtorB` to prove `dtorB_complete`.** A change to `dtorB` changes acceptance.
9. **Growing Backend2's `droppable`/`copyable`, or adding to `Prog.stackKs`.** They read the kernel
   statements of 5.5.
10. **A second constant that consumes `Tok`**, or emitting `burn` anywhere but at a written `match`.
11. **An existential witness for a derived drop** ("some closed term consumes it"). It would make
    every type with a public consumer (`commit`, `burn`) droppable.

---

## 9. Open questions for the user

Accepted provisionally by the user, 2026-10-29: each recommendation below stands until it causes a
problem, which is reported, not worked around.

> **Q10. `!N` at a declared type `N`.** `.bang A` is persistent for every `A`, so `!(A ⊗ Tok)` is
> unrestricted, and `SplitP.dup` then `!E` would duplicate a `Tok`. No rule introduces `!A` except
> at `!U C` (promotion) and the constants, so `!N` should be uninhabited.
> - (a) Prove it: `theorem bang_value : CDerives Δ Γ (.val V) (.val (.bang A)) → (∃ C, A = .thunk
>   C) ∨ A.Persistent`, which inverts `CDerives` at a value. Cost: a case per rule that types a
>   value at `!` (stated per the growth rules). No acceptance change.
> - (b) Well-formedness: `!A` only at `A = U C` or a persistent `A`. Changes the acceptance of
>   programs that write `!N` (none do today); needs the user.
> - (c) Leave it, relying on (a) unproved.
>
> Recommendation: (a). It states the guarantee in the kernel without changing what is accepted.

> **Q11. "The checker never derives a copy where the program declared otherwise" (decision 3).**
> No site derives a copy today, and with binder `linear` gone nothing in a program can say "no
> copy" at an `Imm`. Options: (a) the sentence constrains any future convenience (E1): it emits
> `copy_derives` and nothing else, and a borrow of a declared type stays copyable, since copying a
> view does not copy `N`; (b) declared types also forbid copies of their borrows, which needs a
> fact in `Imm @a N` (a new obligation). Recommendation: (a).

> **Q12. Surface qualifier spellings.** `ctl` (cancellable), `linear ctl` (must resume),
> `multi ctl` (unrestricted). `linear ctl` is true, but it reads as if `ctl`'s `κ` were not linear.
> Not blocking. Recommendation: keep the keywords until the user spells them; prose and messages
> say "cancellable" and "must resume" now.
>
> **Revisited 2026-10-30 (user): fix it.** `linear ctl` uses "linear" for "no derived drop". Every
> `ctl` continuation is linear; the must-resume one is linear with no derived drop. Rename the
> keyword to say what it adds (must resume) in step 3. The spelling is provisional.

> **Q13. The experiment directory** whose name is the removed word (cited at `SPEC.md:1216`).
> Options: rename it, or leave it (outside the library) and drop SPEC's pointer. Recommendation:
> drop the pointer; rename when the experiments are next touched.

> **Q14. The SPEC changelog** (`SPEC.md:10577–10778`) records past versions. Options: leave past
> entries as written and add one recording the rename, or reword them. Recommendation: leave them
> and add the entry.

> **Q15. Descriptions of other systems** (`docs/prior-art-*.md`, `docs/research/`, SPEC §19's
> citations of Tov and Pucella's lattice and of *Affect*). Options: (a) remove the word everywhere,
> paraphrasing the citations; (b) remove it from our own classifications and keep it only where a
> sentence describes another system's type class, marked as theirs. Recommendation: (b), since a
> paraphrase misstates the cited work; but #746 says "everywhere", so this needs the user.

> **Q8′. Renaming `VTy.Drop`.** "Drop" also names `dropE`, the derived drop, which `VTy.Drop` is
> not (decision 2). Options: `VTy.OwnFree`/`Ctx.OwnFree` *(prov.)*, or keep the name with a doc
> comment. Recommendation: rename; it is mechanical (`Core/EffRules.lean`, `Decide.lean`,
> `Weaken.lean`, `TShift.lean`, Backend2's `LTy.drops`).

---

## 10. What this document does not establish

- Nothing in sections 1–2 is proved. `dtorB_completeA`, `dtorE_effFree`, `dtorE_closed`,
  `copy_derives`, `kTy_cancel_hasDtor_iff` and `forgettable_iff` are unverified; the probes check
  `kTy` facts at specific instances only.
- The backend tables (5.3, 5.4) are from reading; no program was run against them, and I have not
  checked whether any program reaches `Convert.lean:1190` or `:2276–2277`.
- Section 6's "read" rows are predictions from the message and report sources, not runs.
- Unread: `experiments/` and `research/`.
