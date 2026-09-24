import Mathlib
import Paper.S1_Syntax.Definitions
import Support.Syntax.Terms

/-!
# [TR] §3 Dynamics  (physical pp. 3–4)

    Kont ∋ K ::= [ ] ∣ (K, e) ∣ (v, K) ∣ let (x, y) = K in e ∣ case K {inj₁ x.e₁ ∣ inj₂ y.e₂}
               ∣ e K ∣ K v
    Mem  ∋ µ : Loc ⇀ Val

the step `(µ, e) → (µ′, e′)` closed under `K[−]` from the head reduction
`(µ, e) ↦ (µ′, e′)` (rules 1↦, ⊗↦, ⊕↦, ⊸↦, alloc↦, free↦, load↦, store↦), and the
derived forms (p. 4)

    swap     ≜ λx.λy.let z = load x; store x y; (x, y)
    copy     ≜ λx.(x, x)
    forget   ≜ λx.()
    withbor  ≜ λx.λf.(x, f x)
    withload ≜ λx.λf.(x, f (load x))
    withswap ≜ λx.λf.let (y, z) = f (load x); store x y; (x, z)

`TR3.Kont`/`TR3.Head`/`TR3.Step1` is the printed machine.  `BoLo.Kont`/`BoLo.Head`/
`BoLo.Step1` adds the frames `K; e`, `inj₁ K` and `inj₂ K` (rows 3.30, 3.31,
`[repair]`, §12.42, D6); `[TR]` p. 6's `wp` (row 5.33) runs it.  Rows are laid out
and tagged as in §1's file.
-/

noncomputable section

namespace BoCa.TR3

/-!
### 3.1 · `Kont ∋ K ::= [ ]` · [TR] p. 3 · `[as printed]`

### 3.2 · `Kont ::= … ∣ (K, e)` · [TR] p. 3 · `[as printed]`

### 3.3 · `Kont ::= … ∣ (v, K)` · [TR] p. 3 · `[encoding]`

`v` through the inclusion `Expr.val` (row 1.17).

### 3.4 · `Kont ::= … ∣ let (x, y) = K in e` · [TR] p. 3 · `[encoding]`

De Bruijn (`x` = 1, `y` = 0).

### 3.5 · `Kont ::= … ∣ case K {inj₁ x.e₁ ∣ inj₂ y.e₂}` · [TR] p. 3 · `[encoding]`

De Bruijn; each branch binds index 0.

### 3.6 · `Kont ::= … ∣ e K` · [TR] p. 3 · `[as printed]`

### 3.7 · `Kont ::= … ∣ K v` · [TR] p. 3 · `[encoding]`

`v` through the inclusion `Expr.val`.
-/
/-- `[TR]` p. 3's evaluation contexts.  `[as printed]` -/
inductive Kont where
  /-- `[ ]` -/
  | hole
  /-- `(K, e)` -/
  | pairL   (K : Kont) (e : Expr)
  /-- `(v, K)` -/
  | pairR   (v : Val)  (K : Kont)
  /-- `let (x,y) = K in e` -/
  | letpair (K : Kont) (e : Expr)
  /-- `case K {inj₁ x.e₁ | inj₂ y.e₂}` -/
  | case    (K : Kont) (e₁ e₂ : Expr)
  /-- `e K` -/
  | appR    (e : Expr) (K : Kont)
  /-- `K v` -/
  | appL    (K : Kont) (v : Val)
  deriving Repr

end BoCa.TR3

namespace BoCa.BoLo
open BoCa.Lifetime

/-!
Rows 3.1, 3.2, 3.3, 3.4, 3.5, 3.6, 3.7, continued.

### 3.30 · — no printed counterpart in §3 — · [TR] p. 3 · `[repair]`

The frame `K; e`: [TR] p. 2's 1E types `e₁; e₂` at any `e₁ : 1` and p. 3 prints no such frame (§12.42, D6).

### 3.31 · — no printed counterpart in §3 — · [TR] p. 3 · `[repair]`

The frames `injᵢ K`: [TR] p. 2's ⊕I types `injᵢ e` at any `e` and p. 3 prints no such frame (§12.42, D6).
-/
/-- [TR] §3's evaluation contexts. -/
inductive Kont where
  | hole
  | pairL   (K : Kont) (e : Expr)        -- `(K, e)`
  | pairR   (v : Val)  (K : Kont)        -- `(v, K)`
  | letpair (K : Kont) (e : Expr)        -- `let (x,y) = K in e`
  | case    (K : Kont) (e₁ e₂ : Expr)    -- `case K {…}`
  | appR    (e : Expr) (K : Kont)        -- `e K`  — argument-first
  | appL    (K : Kont) (v : Val)         -- `K v`
  | seq     (K : Kont) (e : Expr)        -- `K; e`      (row 3.30)
  | inj₁    (K : Kont)                   -- `inj₁ K`    (row 3.31)
  | inj₂    (K : Kont)                   -- `inj₂ K`    (row 3.31)
  deriving Repr

end BoCa.BoLo

namespace BoCa.TR3.Kont

/-!
### 3.8 · `K[e]` (used in the context rule; the grammar fixes it implicitly) · [TR] p. 4 · `[encoding]`

-/
/-- `K[e]`. -/
def plug : Kont → Expr → Expr
  | .hole,         e => e
  | .pairL K e₂,   e => .pair (plug K e) e₂
  | .pairR v K,    e => .pair (.val v) (plug K e)
  | .letpair K e₂, e => .letpair (plug K e) e₂
  | .case K e₁ e₂, e => .case (plug K e) e₁ e₂
  | .appR f K,     e => .app f (plug K e)
  | .appL K v,     e => .app (plug K e) (.val v)

@[simp] theorem plug_hole (e : Expr) : plug .hole e = e := rfl

end BoCa.TR3.Kont

namespace BoCa.BoLo.Kont
open BoCa.Lifetime

/-!
Row 3.8, continued.
-/
/-- `K[e]`. -/
def plug : Kont → Expr → Expr
  | .hole,          e => e
  | .pairL K e₂,    e => .pair (plug K e) e₂
  | .pairR v K,     e => .pair (.val v) (plug K e)
  | .letpair K e₂,  e => .letpair (plug K e) e₂
  | .case K e₁ e₂,  e => .case (plug K e) e₁ e₂
  | .appR f K,      e => .app f (plug K e)
  | .appL K v,      e => .app (plug K e) (.val v)
  | .seq K e₂,      e => .seq (plug K e) e₂
  | .inj₁ K,        e => .inj₁ (plug K e)
  | .inj₂ K,        e => .inj₂ (plug K e)

@[simp] theorem plug_hole (e : Expr) : plug .hole e = e := rfl

end BoCa.BoLo.Kont

namespace BoCa.BoLo
open BoCa.Lifetime

/-!
### 3.9 · `Mem ∋ µ : Loc ⇀ Val` · [TR] p. 3 · `[encoding]`

A total function into `Option`.
-/
abbrev Heap := Loc → Option Val

end BoCa.BoLo

namespace BoCa.BoLo.Heap
open BoCa.Lifetime

/-- `μ` with `ℓ` removed, the result of `free↦`.  `[about ours]` -/
def del (μ : Heap) (ℓ : Loc) : Heap := fun k => if k = ℓ then none else μ k

@[simp] theorem del_same (μ : Heap) (ℓ : Loc) : del μ ℓ ℓ = none := by simp [del]

@[simp] theorem del_other {μ : Heap} {ℓ k : Loc} (h : k ≠ ℓ) : del μ ℓ k = μ k := by
  simp [del, h]

/-!
### 3.23 · `µ[ℓ ↦ v]` (in store↦) · [TR] p. 4 · `[as printed]`
-/
/-- `μ[ℓ ↦ v]`. -/
def upd (μ : Heap) (ℓ : Loc) (v : Val) : Heap := fun k => if k = ℓ then some v else μ k

@[simp] theorem upd_same (μ : Heap) (ℓ : Loc) (v : Val) : upd μ ℓ v ℓ = some v := by
  simp [upd]

@[simp] theorem upd_other {μ : Heap} {ℓ k : Loc} {v : Val} (h : k ≠ ℓ) :
    upd μ ℓ v k = μ k := by simp [upd, h]

end BoCa.BoLo.Heap

namespace BoCa.TR3
open BoCa.BoLo (Heap)

/-!
### 3.11 · the boxed judgments `(µ,e) → (µ′,e′)` and `(µ,e) ↦ (µ′,e′)` · [TR] p. 4 · `[encoding]`

`Step1` is `→`, `Steps` is `→*`, and `Head` is `↦`.

### 3.13 · 1↦: `(µ, (); e) ↦ (µ, e)` · [TR] p. 4 · `[encoding]`

### 3.15 · ⊗↦: `(µ, let (x₁,x₂) = (v₁,v₂) in e) ↦ (µ, e[v₁/x₁, v₂/x₂])` · [TR] p. 4 · `[encoding]`

De Bruijn (`x₁` = 1, `x₂` = 0).

### 3.16 · ⊕↦: `(µ, case (injᵢ v) {inj₁ x.e₁ ∣ inj₂ y.e₂}) ↦ (µ, eᵢ[v/xᵢ])` · [TR] p. 4 · `[encoding]`

The schematic `i` as its two instances.

### 3.17 · ⊸↦: `(µ, (λx.e) v) ↦ (µ, e[v/x])` · [TR] p. 4 · `[encoding]`

De Bruijn.

### 3.18 · alloc↦: `(µ, alloc v) ↦ (µ ⊎ ℓ ↦ v, ℓ)` · [TR] p. 4 · `[encoding]`

`µ ⊎ ℓ ↦ v` as "`µ` is undefined at `ℓ`" plus an update.

### 3.19 · free↦: `(µ ⊎ ℓ ↦ v, free ℓ) ↦ (µ, v)` · [TR] p. 4 · `[encoding]`

The left-hand `⊎` as "`µ` carries `v` at `ℓ`", the result as `Heap.del`.

### 3.20 · load↦: `µ(ℓ) = v` / `(µ, load ℓ) ↦ (µ, v)` · [TR] p. 4 · `[encoding]`

### 3.22 · store↦: `ℓ ∈ dom(µ)` / `(µ, store ℓ v) ↦ (µ[ℓ ↦ v], ())` · [TR] p. 4 · `[encoding]`

The function part `store ℓ` is one term, the value `store v` and the application `e₂ e₁` (row 1.15, §12.43).
-/
/-- The head reductions of `[TR]` p. 4's `↦` box; `⊕↦` is its two instances.
`[as printed]` -/
inductive Head : Heap → Expr → Heap → Expr → Prop where
  /-- `1↦`:  `(μ, (); e) ↦ (μ, e)`. -/
  | one (μ : Heap) (e : Expr) : Head μ (.seq (.val .unit) e) μ e
  /-- `⊗↦`:  `(μ, let (x₁,x₂) = (v₁,v₂) in e) ↦ (μ, e[v₁/x₁, v₂/x₂])`. -/
  | tensor (μ : Heap) (v₁ v₂ : Val) (e : Expr) :
      Head μ (.letpair (.val (.pair v₁ v₂)) e) μ
        ((e.subst 0 (v₂.shift 1 0)).subst 0 v₁)
  /-- `⊕↦` at `i = 1`. -/
  | sum₁ (μ : Heap) (v : Val) (e₁ e₂ : Expr) :
      Head μ (.case (.val (.inj₁ v)) e₁ e₂) μ (e₁.subst 0 v)
  /-- `⊕↦` at `i = 2`. -/
  | sum₂ (μ : Heap) (v : Val) (e₁ e₂ : Expr) :
      Head μ (.case (.val (.inj₂ v)) e₁ e₂) μ (e₂.subst 0 v)
  /-- `⊸↦`:  `(μ, (λx.e) v) ↦ (μ, e[v/x])`. -/
  | lolli (μ : Heap) (b : Expr) (v : Val) :
      Head μ (.app (.val (.lam b)) (.val v)) μ (b.subst 0 v)
  /-- `alloc↦`:  `(μ, alloc v) ↦ (μ ⊎ ℓ ↦ v, ℓ)`. -/
  | alloc (μ : Heap) (v : Val) (ℓ : Loc) (h : μ ℓ = none) :
      Head μ (.app (.val (.prim .alloc)) (.val v)) (μ.upd ℓ v) (.val (.loc ℓ))
  /-- `free↦`:  `(μ ⊎ ℓ ↦ v, free ℓ) ↦ (μ, v)`. -/
  | free (μ : Heap) (ℓ : Loc) (v : Val) (h : μ ℓ = some v) :
      Head μ (.app (.val (.prim .free)) (.val (.loc ℓ))) (μ.del ℓ) (.val v)
  /-- `load↦`:  `μ(ℓ) = v` ⟹ `(μ, load ℓ) ↦ (μ, v)`. -/
  | load (μ : Heap) (ℓ : Loc) (v : Val) (h : μ ℓ = some v) :
      Head μ (.app (.val (.prim .load)) (.val (.loc ℓ))) μ (.val v)
  /-- `store↦`:  `ℓ ∈ dom(μ)` ⟹ `(μ, store ℓ v) ↦ (μ[ℓ ↦ v], ())`. -/
  | store (μ : Heap) (ℓ : Loc) (v w : Val) (h : μ ℓ = some w) :
      Head μ (.app (.app (.val (.prim .store)) (.val (.loc ℓ))) (.val v))
        (μ.upd ℓ v) (.val .unit)

/-!
Row 3.11, continued.

### 3.12 · →: `(µ,e) ↦ (µ′,e′)` / `(µ, K[e]) → (µ′, K[e′])` · [TR] p. 4 · `[encoding]`
-/
/-- `(μ,e) ↦ (μ',e')  ⟹  (μ, K[e]) → (μ', K[e'])`.  A `def`, since the index
`K[e]` is not a constructor application.  `[as printed]` -/
def Step1 (μ : Heap) (e : Expr) (μ' : Heap) (e' : Expr) : Prop :=
  ∃ (K : Kont) (a a' : Expr), e = K.plug a ∧ e' = K.plug a' ∧ Head μ a μ' a'

end BoCa.TR3

namespace BoCa.BoLo
open BoCa.Lifetime

/-!
Rows 3.11, 3.15, 3.16, 3.17, 3.18, 3.19, 3.20, continued.

### 3.14 · 1↦: `(µ, (); e) ↦ (µ, e)` · [TR] p. 4 · `[as printed]`

### 3.21 · store↦: `ℓ ∈ dom(µ)` / `(µ, store ℓ v) ↦ (µ[ℓ ↦ v], ())` · [TR] p. 4 · `[encoding]`

As row 3.22.
-/
/-- The head reductions of `[TR]` p. 4's `↦` box: `TR3.Head` under other names. -/
inductive Head : Heap → Expr → Heap → Expr → Prop where
  | beta (μ : Heap) (b : Expr) (v : Val) :
      Head μ (.app (.val (.lam b)) (.val v)) μ (b.subst 0 v)
  | alloc (μ : Heap) (v : Val) (ℓ : Loc) (h : μ ℓ = none) :
      Head μ (.app (.val (.prim .alloc)) (.val v)) (μ.upd ℓ v) (.val (.loc ℓ))
  | free (μ : Heap) (ℓ : Loc) (v : Val) (h : μ ℓ = some v) :
      Head μ (.app (.val (.prim .free)) (.val (.loc ℓ))) (μ.del ℓ) (.val v)
  | load (μ : Heap) (ℓ : Loc) (v : Val) (h : μ ℓ = some v) :
      Head μ (.app (.val (.prim .load)) (.val (.loc ℓ))) μ (.val v)
  /-- `store↦` -/
  | store (μ : Heap) (ℓ : Loc) (v w : Val) (h : μ ℓ = some w) :
      Head μ (.app (.app (.val (.prim .store)) (.val (.loc ℓ))) (.val v))
        (μ.upd ℓ v) (.val .unit)
  /-- `1↦` -/
  | seq (μ : Heap) (e : Expr) : Head μ (.seq (.val .unit) e) μ e
  | letpair (μ : Heap) (v₁ v₂ : Val) (e : Expr) :
      Head μ (.letpair (.val (.pair v₁ v₂)) e) μ ((e.subst 0 (v₂.shift 1 0)).subst 0 v₁)
  | case₁ (μ : Heap) (v : Val) (e₁ e₂ : Expr) :
      Head μ (.case (.val (.inj₁ v)) e₁ e₂) μ (e₁.subst 0 v)
  | case₂ (μ : Heap) (v : Val) (e₁ e₂ : Expr) :
      Head μ (.case (.val (.inj₂ v)) e₁ e₂) μ (e₂.subst 0 v)

/-!
Rows 3.11, 3.12, continued.
-/
/-- `(μ,e) ↦ (μ',e')  ⟹  (μ, K[e]) → (μ', K[e'])`. -/
def Step1 (μ : Heap) (e : Expr) (μ' : Heap) (e' : Expr) : Prop :=
  ∃ (K : Kont) (a a' : Expr), e = K.plug a ∧ e' = K.plug a' ∧ Head μ a μ' a'

end BoCa.BoLo

namespace BoCa

/-!
### 3.25 · `copy ≜ λx.(x, x)` · [TR] p. 4 · `[encoding]`

[CONF] Fig. 15 calls the same term `dupl` (§12.21).
-/
def copy : Expr := .val (.lam (.pair v0 v0))

/-!
### 3.26 · `forget ≜ λx.()` · [TR] p. 4 · `[encoding]`
-/
def forget : Expr := .val (.lam unit')

/-!
### 3.36 · — no printed counterpart; [TR] §1 prints only `let (x,y) = e₁ in e₂` — · [TR] p. 4 · `[repair]`

[TR] p. 4's `swap` and `withswap` use a unary `let z = e;` that no printed grammar produces; it is `(λz. body) e`, as [TR]'s proof of Lemma 6.169 (p. 44) unfolds it (§12.20).
-/
def elet (e : Expr) (body : Expr) : Expr := .app (.val (.lam body)) e

/-!
Row 3.36, continued.
-/
def lam2 (body : Expr) : Expr := .val (.lam (.val (.lam body)))

/-!
### 3.29 · `withswap ≜ λx.λf.let (y, z) = f (load x); store x y; (x, z)` · [TR] p. 4 · `[encoding]`

[CONF] Fig. 15 prints the same term.
-/
/-- De Bruijn: under `λx λf`, `x = 1`, `f = 0`; the `letpair` pushes `y = 1`,
    `z = 0`, shifting them to `x = 3`, `f = 2`. -/
def withswap : Expr :=
  lam2 (.letpair (.app v0 (.app load' v1))
         (.seq (.app (.app store' v3) v1)
               (.pair v3 v0)))

end BoCa

end
