import Support.Syntax.Integers

/-!
# [TR] §1 Syntax  (physical p. 1)

    Var     ∋ x, y, …
    Loc     ∋ ℓ
    Val     ∋ v  ::= () ∣ (v₁, v₂) ∣ inj₁ v ∣ inj₂ v ∣ λx.e ∣ Λ.e ∣ ℓ ∣ p
    Prim    ∋ p  ::= alloc ∣ free ∣ load ∣ store ∣ store v
    Expr    ∋ e  ::= x ∣ v ∣ (e₁, e₂) ∣ inj₁ e ∣ inj₂ e ∣ e₁ ; e₂ ∣ let (x, y) = e₁ in e₂
                   ∣ case e {inj₁ x.e₁ ∣ inj₂ y.e₂} ∣ e₂ e₁
    LifeVar ∋ 'a, 'b, …
    Life    ∋ @a, @b, … ::= ' ∣ ⊤ ∣ @a ⊔ @b ∣ @a ⊓ @b
    LifeCtx ∋ Δ  : LifeVar ⇀ Life
    Type    ∋ T  ::= 1 ∣ T₁ ⊕ T₂ ∣ T₁ ⊗ T₂ ∣ T₁ ⊸ T₂ ∣ Ref T ∣ [@a] T
                   ∣ Imm @a T ∣ Mut @a T ∣ ∀ 'a ⊏ @b. T ∣ Unk

Each printed item is a row, in printed order as far as definition-before-use
allows, with its number (`Paper/INDEX.md`, *Definitions*), printed form, page and
tag: `[as printed]`; `[encoding]` (a representation choice that changes nothing);
`[repair]` (a reading argued in `docs/adjudications.md`, cited by `§N`);
`[about ours]` (not printed, needed by Lean).
-/

noncomputable section

namespace BoCa

/-!
### 1.2 · `Loc ∋ ℓ` · [TR] p. 1 · `[encoding]`

`Nat`, as an `abbrev`; `Loc`, `LifeVar` and the semantic lifetime carrier are all
definitionally `Nat`.
-/
abbrev Loc := Nat

/-!
### 1.11 · `Prim ∋ p ::= alloc` · [TR] p. 1 · `[as printed]`
### 1.12 · `Prim ::= … ∣ free` · [TR] p. 1 · `[as printed]`
### 1.13 · `Prim ::= … ∣ load` · [TR] p. 1 · `[as printed]`
### 1.14 · `Prim ::= … ∣ store` · [TR] p. 1 · `[as printed]`
-/
/-- The four nullary productions of `[TR]` p. 1's `Prim`; `store v` is row 1.15.
    `lit` and `host` are the integer constants of `SPEC.md` §8; `tab`, `idx` and `drop` the
    array primitives of §9 with the split `split`; `count` the counted loop of §16,
    `countTry` the counted loop with an exit and `boundedFix` the fuelled fixed point of §20. -/
inductive Prim where
  | alloc | free | load | store
  /-- An integer literal.  `[spec §8]` -/
  | lit (c : IntLit)
  /-- A host operation, applied by the machine's host step.  `[spec §8]` -/
  | host (op : HostOp)
  /-- Array creation: `tab (c, f)` places the cells and fills them from `f`.  `[spec §9]` -/
  | tab
  /-- Array indexing: `idx ((ℓ, n), i)`, bounds-checked.  `[spec §9]` -/
  | idx
  /-- Array disposal: `drop (f, (ℓ, n))` frees each cell and hands its contents to `f`.
      `[spec §9]` -/
  | drop
  /-- Family split: `split ((ℓ, n), i)` at `i ≤ n` answers the two parts `(ℓ, i)` and
      `(ℓ + i, n − i)`.  `[spec §9]` -/
  | split
  /-- The counted loop: `count (f, (n, (i, s)))` runs `f` at `i, …, len(n) − 1`, threading `s`.
      `[spec §16]` -/
  | count
  /-- The counted loop with an exit: `count_try (f, (n, (i, s)))` runs `f` at `i, …, len(n) − 1`
      while it answers `inj₁` of the next state, and stops at its first `inj₂`.  `[spec §16]` -/
  | countTry
  /-- The fuelled fixed point: `bounded_fix (s, (k, a))` runs `s (self, a)`, `self` the fixed
      point at `k − 1`, or `inj₁ ()` once the budget is spent.  `[spec §20]` -/
  | boundedFix
  /-- A control operation: `perform (n, (i, v))` asks the nearest handler named `n` for its
      operation `i` at `v`, and is resumed with its answer.  `[spec §19]` -/
  | perform
  /-- An abortive operation: `raise (n, (i, v))` unwinds to the nearest handler named `n`, each
      finaliser on the way running innermost first.  `[spec §19]` -/
  | raise
  /-- The handler frame `hnd (n, (h_ret, hs)) e`.  `[spec §19]` -/
  | hnd
  /-- The finaliser frame `ubind (N, D) M`: `M` then `N`, or `D` when `M` unwinds.  `[spec §19]` -/
  | ubind
  /-- The cancel delimiter `ccatch e`, which catches only the reserved name `0`.  `[spec §19]` -/
  | ccatch
  /-- The cancel-mode finaliser frame `cfin s e`: `e` is a finaliser running under a cancel whose
      state is `s`; every `raise` escaping `e` is caught here.  `[spec §19]` -/
  | cfin
  deriving DecidableEq, Repr

/-!
### 1.1 · `Var ∋ x, y, …` · [TR] p. 1 · `[encoding]`

De Bruijn indices.

### 1.16 · `Expr ∋ e ::= x` · [TR] p. 1 · `[encoding]`

De Bruijn index.

### 1.18 · `Expr ::= … ∣ (e₁, e₂)` · [TR] p. 1 · `[as printed]`
### 1.19 · `Expr ::= … ∣ inj₁ e` · [TR] p. 1 · `[as printed]`

[TR] p. 2's ⊕I prints the term as `i e`, the same former (§12.16).

### 1.20 · `Expr ::= … ∣ inj₂ e` · [TR] p. 1 · `[as printed]`
### 1.21 · `Expr ::= … ∣ e₁ ; e₂` · [TR] p. 1 · `[as printed]`
### 1.22 · `Expr ::= … ∣ let (x, y) = e₁ in e₂` · [TR] p. 1 · `[encoding]`

De Bruijn, binding two in the body (`y` = 0, `x` = 1). [TR] p. 2's ⊗E prints the
same form with `;` for `in`.

### 1.23 · `Expr ::= … ∣ case e {inj₁ x.e₁ ∣ inj₂ y.e₂}` · [TR] p. 1 · `[encoding]`

De Bruijn, binding one in each branch. [TR] p. 2's ⊕E prints
`match es {x₁ ⇒ e₁, x₂ ⇒ e₂}` for the same former.

### 1.24 · `Expr ::= … ∣ e₂ e₁` · [TR] p. 1 · `[as printed]`

The fields are (function, argument). [TR] p. 2's ⊸E is row 2.10 (§12.2).
-/
/-- `[TR]` p. 1's `Expr`, carrying its `Val` productions (`e ::= v`, row 1.17). -/
inductive Expr where
  | var     (i : Nat)                 -- x
  | unit                              -- ()
  | pair    (e₁ e₂ : Expr)            -- (e₁,e₂)
  | inj₁    (e : Expr)
  | inj₂    (e : Expr)
  | lam     (body : Expr)             -- λx.e, and Λ.e ≜ λ_.e
  | loc     (ℓ : Loc)                 -- ℓ
  /-- `p` at one of the four nullary `Prim` productions. -/
  | prim    (p : Prim)
  | seq     (e₁ e₂ : Expr)            -- e₁ ; e₂
  | letpair (e₁ e₂ : Expr)            -- let (x,y) = e₁; e₂   — binds 2 (y = 0, x = 1)
  | case    (e e₁ e₂ : Expr)          -- case e {inj₁ x. e₁, inj₂ x. e₂} — binds 1 each
  | app     (f a : Expr)              -- e₂ e₁
  deriving Repr

/-- `[TR]` p. 1's `Val`, as the subset of `Expr` its production `e ::= v` makes
    it: one clause per printed `Val` production, `Λ.e` folded into `λx.e`
    (row 1.8) and `store v` as the application the grammar derives it as.
    `[about ours]` -/
inductive IsVal : Expr → Prop where
  | unit                                                  : IsVal .unit
  | pair {a b : Expr} (h₁ : IsVal a) (h₂ : IsVal b)       : IsVal (.pair a b)
  | inj₁ {a : Expr} (h : IsVal a)                         : IsVal (.inj₁ a)
  | inj₂ {a : Expr} (h : IsVal a)                         : IsVal (.inj₂ a)
  | lam {b : Expr}                                        : IsVal (.lam b)
  | loc {ℓ : Loc}                                         : IsVal (.loc ℓ)
  | prim {p : Prim}                                       : IsVal (.prim p)
  | storeV {a : Expr} (h : IsVal a)                       : IsVal (.app (.prim .store) a)

@[simp] theorem not_isVal_var {i : Nat} : ¬ IsVal (.var i) := fun h => nomatch h

@[simp] theorem not_isVal_seq {a b : Expr} : ¬ IsVal (.seq a b) := fun h => nomatch h

@[simp] theorem not_isVal_letpair {a b : Expr} : ¬ IsVal (.letpair a b) := fun h => nomatch h

@[simp] theorem not_isVal_case {a b c : Expr} : ¬ IsVal (.case a b c) := fun h => nomatch h

/-- `Val ⊆ Expr`. -/
abbrev Val := {e : Expr // IsVal e}

end BoCa

namespace BoCa.Val

/-!
### 1.3 · `Val ∋ v ::= ()` · [TR] p. 1 · `[as printed]`
-/
def unit : Val := ⟨.unit, .unit⟩

@[simp] theorem val_unit : (Val.unit).val = Expr.unit := rfl

/-!
### 1.4 · `Val ::= … ∣ (v₁, v₂)` · [TR] p. 1 · `[as printed]`
-/
def pair (v w : Val) : Val := ⟨.pair v.1 w.1, .pair v.2 w.2⟩

@[simp] theorem val_pair (v w : Val) : (Val.pair v w).val = .pair v.val w.val := rfl

/-!
### 1.5 · `Val ::= … ∣ inj₁ v` · [TR] p. 1 · `[as printed]`
-/
def inj₁ (v : Val) : Val := ⟨.inj₁ v.1, .inj₁ v.2⟩

@[simp] theorem val_inj₁ (v : Val) : (Val.inj₁ v).val = .inj₁ v.val := rfl

/-!
### 1.6 · `Val ::= … ∣ inj₂ v` · [TR] p. 1 · `[as printed]`
-/
def inj₂ (v : Val) : Val := ⟨.inj₂ v.1, .inj₂ v.2⟩

@[simp] theorem val_inj₂ (v : Val) : (Val.inj₂ v).val = .inj₂ v.val := rfl

/-!
### 1.7 · `Val ::= … ∣ λx.e` · [TR] p. 1 · `[encoding]`

De Bruijn: the binder is dropped.

### 1.8 · `Val ::= … ∣ Λ.e` · [TR] p. 1 · `[repair]`

`Λ.e` is `λ_.e`, as [CONF] p. 415:8 states and [TR] p. 4's
`𝒱⟦∀ 'a ⊏ @b. T⟧δ(v) ≜ ∀ α ⊏ @bδ. ℰ⟦T⟧δ(v ())` requires (§12.14, §12.27).
-/
def lam (body : Expr) : Val := ⟨.lam body, .lam⟩

@[simp] theorem val_lam (b : Expr) : (Val.lam b).val = .lam b := rfl

/-!
### 1.9 · `Val ::= … ∣ ℓ` · [TR] p. 1 · `[as printed]`
-/
def loc (ℓ : Loc) : Val := ⟨.loc ℓ, .loc⟩

@[simp] theorem val_loc (ℓ : Loc) : (Val.loc ℓ).val = .loc ℓ := rfl

@[simp] theorem loc_inj {ℓ k : Loc} : Val.loc ℓ = Val.loc k ↔ ℓ = k :=
  ⟨fun h => Expr.loc.inj (congrArg Subtype.val h), fun h => h ▸ rfl⟩

/-!
### 1.10 · `Val ::= … ∣ p` · [TR] p. 1 · `[encoding]`

Split by whether the `Prim` production carries a value: `Val.prim` at the four
nullary schemes, `Val.storeV` at `store v` (row 1.15).
-/
def prim (p : Prim) : Val := ⟨.prim p, .prim⟩

@[simp] theorem val_prim (p : Prim) : (Val.prim p).val = .prim p := rfl

/-!
### 1.15 · `Prim ::= … ∣ store v` · [TR] p. 1 · `[encoding]`

`store v` is at once this production and the application `e₂ e₁`; it is the term
`.app (.prim .store) v`, with the `IsVal` clause that makes it a value (§12.43).
-/
def storeV (v : Val) : Val := ⟨.app (.prim .store) v.1, .storeV v.2⟩

@[simp] theorem val_storeV (v : Val) :
    (Val.storeV v).val = .app (.prim .store) v.val := rfl

end BoCa.Val

namespace BoCa

/-!
### 1.17 · `Expr ::= … ∣ v` · [TR] p. 1 · `[encoding]`

`Val` is a subset of `Expr`: one inductive `Expr`, the predicate `IsVal`, and `Val`
the subtype, with `Expr.val` the inclusion, so a value derived through `v` and
through its structural production is one term (§12.43).
-/
/-- `[TR]` p. 1's production `e ::= v`: the inclusion. -/
abbrev Expr.val (v : Val) : Expr := v.1

end BoCa

namespace BoCa.Lifetime

/-!
### 1.25 · `LifeVar ∋ 'a, 'b, …` · [TR] p. 1 · `[encoding]`

`Nat`-indexed names.
-/
abbrev LifeVar := Nat

/-!
### 1.26 · `Life ∋ @a, @b… ::= '` · [TR] p. 1 · `[encoding]`

The printed bare `'` is read as a variable `'a`, as [CONF] Fig. 7 prints it (§12.8).

### 1.27 · `Life ::= … ∣ ⊤` · [TR] p. 1 · `[as printed]`
### 1.28 · `Life ::= … ∣ @a ⊔ @b` · [TR] p. 1 · `[as printed]`
### 1.29 · `Life ::= … ∣ @a ⊓ @b` · [TR] p. 1 · `[as printed]`
-/
inductive Life where
  /-- `'a`. -/
  | var (a : LifeVar)
  /-- `⊤`. -/
  | top
  /-- `@a ⊔ @b`. -/
  | join (a b : Life)
  /-- `@a ⊓ @b`. -/
  | meet (a b : Life)
  deriving DecidableEq, Repr, Inhabited

/-!
### 1.30 · `LifeCtx ∋ Δ : LifeVar ⇀ Life` · [TR] p. 1 · `[encoding]`

An association list; the innermost binding wins (`assocFind`).
-/
structure LifeCtx where
  entries : List (LifeVar × Life)
  deriving Repr, DecidableEq, Inhabited

end BoCa.Lifetime

namespace BoCa
open BoCa.Lifetime

/-!
### 1.31 · `Type ∋ T ::= 𝟙` · [TR] p. 1 · `[as printed]`
### 1.32 · `Type ::= … ∣ T₁ ⊕ T₂` · [TR] p. 1 · `[as printed]`
### 1.33 · `Type ::= … ∣ T₁ ⊗ T₂` · [TR] p. 1 · `[as printed]`
### 1.34 · `Type ::= … ∣ T₁ ⊸ T₂` · [TR] p. 1 · `[as printed]`
### 1.35 · `Type ::= … ∣ Ref T` · [TR] p. 1 · `[as printed]`
### 1.36 · `Type ::= … ∣ [@a] T` · [TR] p. 1 · `[as printed]`
### 1.37 · `Type ::= … ∣ Imm @a T` · [TR] p. 1 · `[as printed]`

Not the metafunction `Imm̲` of [TR] p. 3 (row 2.49, §12.28).

### 1.38 · `Type ::= … ∣ Mut @a T` · [TR] p. 1 · `[as printed]`
### 1.39 · `Type ::= … ∣ ∀ 'a ⊏ @b. T` · [TR] p. 1 · `[as printed]`

The binder is named, as printed.

### 1.40 · `Type ::= … ∣ Unk` · [TR] p. 1 · `[as printed]`
-/
/-- `all` is `∀`; the name avoids the keyword. -/
inductive Ty where
  | unit
  | sum    (T₁ T₂ : Ty)
  | tensor (T₁ T₂ : Ty)
  | lolli  (T₁ T₂ : Ty)
  | ref    (T : Ty)
  /-- `!T`: the exponential, a value of `T` holding no resource.  `[spec §2]` -/
  | bang   (T : Ty)
  /-- `Imm @a T`. -/
  | imm    (a : Life) (T : Ty)
  /-- `Mut @a T`. -/
  | mut    (a : Life) (T : Ty)
  /-- `[@a] T`. -/
  | box    (a : Life) (T : Ty)
  /-- `∀'x ⊏ @b. T`. -/
  | all    (x : LifeVar) (b : Life) (T : Ty)
  /-- `Unk`. -/
  | unk
  deriving DecidableEq, Repr, Inhabited

end BoCa

end
