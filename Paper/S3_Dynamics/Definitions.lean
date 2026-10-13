import Mathlib
import Paper.S1_Syntax.Definitions
import Support.Syntax.Terms
import Support.Dynamics.Host
import Support.Dynamics.Arrays

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

/-- `μ ⊎ {ℓ+i ↦ v | i < n}`, the result of the array step `tab`.  `[spec §9]` -/
def fill (μ : Heap) (ℓ : Loc) (n : Nat) (v : Val) : Heap :=
  fun k => if ℓ ≤ k ∧ k < ℓ + n then some v else μ k

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
/-!
### — no printed counterpart — the host step · `[spec §8]`

`(µ, h v) ↦ (µ, r)` when the host applies the operation `h` to `v` with result `r`
(`Host.call`). The machine is parametric in the host: every definition over it takes
`{ℍ : Host} [HostIs ℍ]`, and at each host it is deterministic up to the choice of fresh
locations.

### — no printed counterpart — the array steps · `[spec §9]`

`tab` places `len(c)` cells at fresh consecutive locations and continues as `tabFill`; `idx`
answers `idxAns`; `split` answers `splitAns`; `drop` continues as `dropFill`
(`Support/Dynamics/Arrays.lean`).

### — no printed counterpart — the counted loop · `[spec §16]`

`count (f, (n, (i, s)))` continues as `countNext`: `f (i, s)` and `count` from `i + 1` while
`i < len(n)`, else `s`. `count_try (f, (n, (i, s)))` continues as `countTryNext`: `f (i, s)`, then
`count_try` from `i + 1` on its `inj₁`, or its `inj₂` as the answer; at the bound `inj₁ s`.

### — no printed counterpart — the fuelled fixed point · `[spec §20]`

`bounded_fix (s, (k, a))` continues as `boundedFixNext`: `s (self, a)`, where `self` is
`inj₁ ()` at `k = 0` (the budget is spent) and `inj₂ (λx. bounded_fix (s, (k − 1, x)))` otherwise.
The budget is the machine's, counted down by the machine, so the recursion is total at every
host.
-/
/-!
### — no printed counterpart — handlers, operations and finalisers · `[spec §19]`

`hnd (n, (qs, (h_ret, hs))) e` runs `e` under a handler named `n`, whose operations' continuations
have the qualifiers the tags `qs` record; `perform (n, (i, v))` and `raise (n, (i, v))` are its
control and abortive operations; `ubind (N, D) M` is `M` then `N`, with the finaliser `D` when `M`
unwinds; `ccatch e` catches the reserved name `0`, the cancel of a continuation.  A frame
*catches* a `raise` of name `n` when it is a handler of `n`, a finaliser, a cancel-mode finaliser
`cfin`, or (at `n = 0`) a `ccatch`; a `perform` of name `n` is caught only by a handler of `n`.

**The capture cell** (`[spec §25]`).  At a linear or affine operation, the continuation `κ` the
`[op]` step hands the clause owns a fresh cell holding `()`, allocated by the ordinary `alloc`
before the clause runs.  Using `κ` frees it: resuming, and at an affine operation cancelling.  A
linear `κ`'s cancel branch has no step.  So a `κ` dropped leaves its cell behind, and a `κ` used
twice frees its cell twice.

**Cancels.**  A cancel is a `raise` of the reserved name `0` whose payload is a cancel state: the
first error a finaliser of the cancelled region raised, if any (`cancelVal`).  The cancelled region
is dead: `κ`'s cancel branch runs it with its handler frames and its cancel delimiters removed
(`Kont.dead`), so no frame of the region catches the cancel, a finaliser's raise or a finaliser's
operation.  At a finaliser the cancel runs `D ()` under `cfin`.  A raise escaping `D` is caught
there, and the first error is kept (`errNext`).  An operation of `D` passes the dead region to the
nearest live handler; if that handler cancels its continuation, the new cancel reaches the running
finaliser's `cfin`, and the error kept there, the earlier one, wins.  At `ccatch` the cancel answers
`()`, or re-raises the kept error at the canceller.
-/

/-- `hnd H e`.  `[spec §19]` -/
def hndE (H : Val) (e : Expr) : Expr := .app (.app (.val (.prim .hnd)) (.val H)) e

/-- `ubind ND e`.  `[spec §19]` -/
def ubindE (ND : Val) (e : Expr) : Expr := .app (.app (.val (.prim .ubind)) (.val ND)) e

/-- `ccatch e`.  `[spec §19]` -/
def ccatchE (e : Expr) : Expr := .app (.val (.prim .ccatch)) e

/-- `cfin s e`.  `[spec §19]` -/
def cfinE (st : Val) (e : Expr) : Expr := .app (.app (.val (.prim .cfin)) (.val st)) e

/-- `perform p`.  `[spec §19]` -/
def performE (p : Expr) : Expr := .app (.val (.prim .perform)) p

/-- `raise p`.  `[spec §19]` -/
def raiseE (p : Expr) : Expr := .app (.val (.prim .raise)) p

/-- The payload `(n, (i, v))` of an operation.  `[spec §19]` -/
def opPayload (n i : UInt32) (v : Val) : Val := .pair (.i32 n) (.pair (.i32 i) v)

/-- The handler value `(n, (qs, (h_ret, hs)))`: its name, the tags of its operations'
qualifiers, its answer clause and its clauses.  `[spec §19, §25]` -/
def hndVal (n : UInt32) (qs hr hs : Val) : Val := .pair (.i32 n) (.pair qs (.pair hr hs))

/-- The `i`-th tag of a right-nested tuple of tags; `2` (unrestricted) where there is none.
The tags are `0` (linear), `1` (affine) and `2` (unrestricted).  `[spec §25]` -/
def capTag : Expr → Nat → UInt32
  | .pair (.prim (.lit (.i32 t))) _, 0 => t
  | .pair _ r, i + 1 => capTag r i
  | _, _ => 2

open Classical in
/-- The `i`-th clause of a right-nested tuple of clauses.  `[spec §19]` -/
def clauseAt : Expr → Nat → Option Val
  | .pair c _, 0 => if h : IsVal c then some ⟨c, h⟩ else none
  | .pair _ r, i + 1 => clauseAt r i
  | _, _ => none

/-- An optional error as a value: `inj₁ ()` or `inj₂ E`.  `[spec §19]` -/
def errVal : Option Val → Val
  | none => .inj₁ .unit
  | some E => .inj₂ E

/-- The cancel payload `(0, (0, err))`: the error kept so far.  `[spec §19]` -/
def cancelVal (err : Option Val) : Val := opPayload 0 0 (errVal err)

/-- The error a cancel keeps after a finaliser raises `(m, (j, w))`: the first one.
`[spec §19]` -/
def errNext (err : Option Val) (m j : UInt32) (w : Val) : Option Val :=
  err.or (some (opPayload m j w))

namespace Kont

/-- `K` has a handler frame of name `n`.  `[spec §19]` -/
def HasHnd (n : UInt32) : Kont → Bool
  | .hole => false
  | .pairL K _ | .pairR _ K | .letpair K _ | .case K _ _ | .appL K _ | .seq K _ | .inj₁ K
  | .inj₂ K => HasHnd n K
  | .appR f K =>
      (match f with
        | .app (.prim .hnd) (.pair (.prim (.lit (.i32 m))) _) => m == n
        | _ => false) || HasHnd n K

/-- `K` has a frame that catches a `raise` of name `n`: a handler of `n`, a finaliser, or a
`ccatch` when `n = 0`.  `[spec §19]` -/
def Catches (n : UInt32) : Kont → Bool
  | .hole => false
  | .pairL K _ | .pairR _ K | .letpair K _ | .case K _ _ | .appL K _ | .seq K _ | .inj₁ K
  | .inj₂ K => Catches n K
  | .appR f K =>
      (match f with
        | .app (.prim .hnd) (.pair (.prim (.lit (.i32 m))) _) => m == n
        | .app (.prim .ubind) _ => true
        | .prim .ccatch => n == 0
        | .app (.prim .cfin) _ => true
        | _ => false) || Catches n K

/-- A frame `f [·]` that a cancel kills: a handler frame `hnd (m, …) [·]` or a cancel delimiter
`ccatch [·]`.  `[spec §19]` -/
def DeadFrame (f : Expr) : Bool :=
  match f with
  | .app (.prim .hnd) (.pair (.prim (.lit (.i32 _))) _) => true
  | .prim .ccatch => true
  | _ => false

/-- `K†`: the cancelled region `K` with the frames a cancel kills removed, its handler frames and
its cancel delimiters (`DeadFrame`).  Its other frames stay, finalisers among them.  `[spec §19]` -/
def dead : Kont → Kont
  | .hole => .hole
  | .pairL K e => .pairL (dead K) e
  | .pairR v K => .pairR v (dead K)
  | .letpair K e => .letpair (dead K) e
  | .case K e₁ e₂ => .case (dead K) e₁ e₂
  | .appR f K => if DeadFrame f then dead K else .appR f (dead K)
  | .appL K v => .appL (dead K) v
  | .seq K e => .seq (dead K) e
  | .inj₁ K => .inj₁ (dead K)
  | .inj₂ K => .inj₂ (dead K)

/-- Shift every term of a context.  `[spec §19]` -/
def shift (d c : Nat) : Kont → Kont
  | .hole => .hole
  | .pairL K e => .pairL (shift d c K) (e.shift d c)
  | .pairR v K => .pairR (v.shift d c) (shift d c K)
  | .letpair K e => .letpair (shift d c K) (e.shift d (c + 2))
  | .case K e₁ e₂ => .case (shift d c K) (e₁.shift d (c + 1)) (e₂.shift d (c + 1))
  | .appR f K => .appR (f.shift d c) (shift d c K)
  | .appL K v => .appL (shift d c K) (v.shift d c)
  | .seq K e => .seq (shift d c K) (e.shift d c)
  | .inj₁ K => .inj₁ (shift d c K)
  | .inj₂ K => .inj₂ (shift d c K)

end Kont

/-- The continuation `κ` the `[op]` step hands the clause: the `&` pair of its resume branch
`λy. hnd H K[y]` and its cancel branch `ccatch (K†[raise (0, (0, none))])`, the region `K` dead
(`Kont.dead`), written as `λs. case s {inj₁ u. u; λy. … | inj₂ u. u; …}`.  `[spec §19]` -/
def kappa (H : Val) (K : Kont) : Expr :=
  .val (.lam (.case (.var 0)
    (.seq (.var 0) (.val (.lam (hndE (H.shift 3 0) ((K.shift 3 0).plug (.var 0))))))
    (.seq (.var 0) (ccatchE ((K.dead.shift 2 0).plug (raiseE (.val (cancelVal none))))))))

/-- `free e`.  `[spec §25]` -/
def freeE (e : Expr) : Expr := .app (.val (.prim .free)) e

/-- A term with no step: `() ()`.  `[spec §25]` -/
def stuckE : Expr := .app (.val .unit) (.val .unit)

/-- `κ` at a linear (`aff = false`) or affine operation, its cell at `ℓ`: `kappa`'s branches,
each freeing `ℓ` once the branch is chosen.  A linear `κ`'s cancel branch is at `⊤` and has no
step.  `[spec §25]` -/
def kappaC (aff : Bool) (ℓ : Loc) (H : Val) (K : Kont) : Expr :=
  .val (.lam (.case (.var 0)
    (.seq (.var 0) (.seq (freeE (.val (.loc ℓ)))
      (.val (.lam (hndE (H.shift 3 0) ((K.shift 3 0).plug (.var 0)))))))
    (if aff then
      .seq (.var 0) (.seq (freeE (.val (.loc ℓ)))
        (ccatchE ((K.dead.shift 2 0).plug (raiseE (.val (cancelVal none))))))
    else stuckE)))

/-- `kappaC`'s body over its cell, the cell the variable `c` (index `0` outside the `λs`). -/
def kappaCBody (aff : Bool) (H : Val) (K : Kont) : Expr :=
  .lam (.case (.var 0)
    (.seq (.var 0) (.seq (freeE (.var 2))
      (.val (.lam (hndE (H.shift 4 0) ((K.shift 4 0).plug (.var 0)))))))
    (if aff then
      .seq (.var 0) (.seq (freeE (.var 2))
        (ccatchE ((K.dead.shift 3 0).plug (raiseE (.val (cancelVal none))))))
    else stuckE))

/-- `κ` at a linear or affine operation, before its cell: `(λc. kappaCBody) (alloc ())`, so the
cell is allocated by the ordinary `alloc` step, and `κ` is `kappaC` at its location.
`[spec §25]` -/
def kappaCell (aff : Bool) (H : Val) (K : Kont) : Expr :=
  .app (.val (.lam (kappaCBody aff H K))) (.app (.val (.prim .alloc)) (.val .unit))

/-- The continuation the `[op]` step hands the clause, by the operation's tag: `kappaCell` at a
linear (`0`) or affine (`1`) operation, `kappa` otherwise.  `[spec §19, §25]` -/
def kappaAt (t : UInt32) (H : Val) (K : Kont) : Expr :=
  if t = 0 then kappaCell false H K else if t = 1 then kappaCell true H K else kappa H K

/-- The head reductions of `[TR]` p. 4's `↦` box: `TR3.Head` under other names, the host
    step of `SPEC.md` §8, and the array steps of §9. -/
inductive Head {ℍ : Host} [HostIs ℍ] : Heap → Expr → Heap → Expr → Prop where
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
  /-- The host step: `Host.call op v = some r` ⟹ `(μ, op v) ↦ (μ, r)`.  `[spec §8]` -/
  | host (μ : Heap) (op : HostOp) (v r : Val) (h : ℍ.call op v = some r) :
      Head μ (.app (.val (.prim (.host op))) (.val v)) μ (.val r)
  /-- `(μ, tab (c, f)) ↦ (μ ⊎ {ℓ+i ↦ ()}_{i<n}, tabFill …)` at fresh `ℓ, …, ℓ+n−1`,
      `n = len(c)`.  `[spec §9]` -/
  | tab (μ : Heap) (c : UInt32) (f : Val) (ℓ : Loc)
      (h : ∀ i, i < (arrLen c).toNat → μ (ℓ + i) = none) :
      Head μ (.app (.val (.prim .tab)) (.val (.pair (.i32 c) f)))
        (μ.fill ℓ (arrLen c).toNat .unit) (tabFill f ℓ (arrLen c) 0 (arrLen c).toNat)
  /-- `(μ, idx ((ℓ, n), i)) ↦ (μ, idxAns ℓ n i)`.  `[spec §9]` -/
  | idx (μ : Heap) (ℓ : Loc) (n i : UInt32) :
      Head μ (.app (.val (.prim .idx)) (.val (.pair (.arr ℓ n) (.i32 i)))) μ
        (.val (idxAns ℓ n i))
  /-- `(μ, split ((ℓ, n), i)) ↦ (μ, splitAns ℓ n i)`.  `[spec §9]` -/
  | split (μ : Heap) (ℓ : Loc) (n i : UInt32) :
      Head μ (.app (.val (.prim .split)) (.val (.pair (.arr ℓ n) (.i32 i)))) μ
        (.val (splitAns ℓ n i))
  /-- `(μ, drop (f, (ℓ, n))) ↦ (μ, dropFill f ℓ 0 n)`.  `[spec §9]` -/
  | drop (μ : Heap) (f : Val) (ℓ : Loc) (n : UInt32) :
      Head μ (.app (.val (.prim .drop)) (.val (.pair f (.arr ℓ n)))) μ (dropFill f ℓ 0 n.toNat)
  /-- `(μ, count (f, (n, (i, s)))) ↦ (μ, countNext f n i s)`.  `[spec §16]` -/
  | count (μ : Heap) (f : Val) (n i : UInt32) (s : Val) :
      Head μ (.app (.val (.prim .count)) (.val (.pair f (.pair (.i32 n) (.pair (.i32 i) s))))) μ
        (countNext f n i s)
  /-- `(μ, count_try (f, (n, (i, s)))) ↦ (μ, countTryNext f n i s)`.  `[spec §16]` -/
  | countTry (μ : Heap) (f : Val) (n i : UInt32) (s : Val) :
      Head μ (.app (.val (.prim .countTry)) (.val (.pair f (.pair (.i32 n) (.pair (.i32 i) s))))) μ
        (countTryNext f n i s)
  /-- `(μ, bounded_fix (s, (k, a))) ↦ (μ, boundedFixNext s k a)`.  `[spec §20]` -/
  | boundedFix (μ : Heap) (s : Val) (k : UInt32) (a : Val) :
      Head μ (.app (.val (.prim .boundedFix)) (.val (.pair s (.pair (.i32 k) a)))) μ
        (boundedFixNext s k a)
  /-- `[ret]`: `hnd (n, (qs, (h_ret, hs))) v ↦ h_ret v`.  `[spec §19]` -/
  | hret (μ : Heap) (n : UInt32) (qs hr hs w : Val) :
      Head μ (hndE (hndVal n qs hr hs) (.val w)) μ (.app (.val hr) (.val w))
  /-- `[op]`: `hnd H K[perform (n, (i, v))] ↦ h_i (v, κ)`, `K` free of `n`, `κ` by the
      operation's tag (`kappaAt`).  `[spec §19, §25]` -/
  | hop (μ : Heap) (n i : UInt32) (qs hr hs c v : Val) (K : Kont)
      (hc : clauseAt hs.1 i.toNat = some c) (hK : K.HasHnd n = false) :
      Head μ (hndE (hndVal n qs hr hs) (K.plug (performE (.val (opPayload n i v))))) μ
        (.app (.val c) (.pair (.val v)
          (kappaAt (capTag qs.1 i.toNat) (hndVal n qs hr hs) K)))
  /-- `[unwind]`: `hnd H K[raise (n, (i, v))] ↦ h_i v`, `K` catching nothing of `n`.
      `[spec §19]` -/
  | hunwind (μ : Heap) (n i : UInt32) (qs hr hs c v : Val) (K : Kont)
      (hc : clauseAt hs.1 i.toNat = some c) (hK : K.Catches n = false) :
      Head μ (hndE (hndVal n qs hr hs) (K.plug (raiseE (.val (opPayload n i v))))) μ
        (.app (.val c) (.val v))
  /-- `[then]`: `ubind (N, D) v ↦ N v`.  `[spec §19]` -/
  | uthen (μ : Heap) (N D w : Val) :
      Head μ (ubindE (.pair N D) (.val w)) μ (.app (.val N) (.val w))
  /-- `[finalise]`: `ubind (N, D) K[raise p] ↦ D (); raise p`, `p` not a cancel, `K` catching
      nothing of `p`'s name.  `[spec §19]` -/
  | ufin (μ : Heap) (N D : Val) (n i : UInt32) (v : Val) (K : Kont) (hn : n ≠ 0)
      (hK : K.Catches n = false) :
      Head μ (ubindE (.pair N D) (K.plug (raiseE (.val (opPayload n i v))))) μ
        (.seq (.app (.val D) (.val .unit)) (raiseE (.val (opPayload n i v))))
  /-- `[finalise-cancel]`: `ubind (N, D) K[raise s] ↦ cfin s (D ())`, `s` a cancel.
      `[spec §19]` -/
  | ufinC (μ : Heap) (N D : Val) (err : Option Val) (K : Kont) (hK : K.Catches 0 = false) :
      Head μ (ubindE (.pair N D) (K.plug (raiseE (.val (cancelVal err))))) μ
        (cfinE (cancelVal err) (.app (.val D) (.val .unit)))
  /-- `[cfin-ret]`: the finaliser finished; the cancel goes on.  `[spec §19]` -/
  | cfret (μ : Heap) (err : Option Val) (w : Val) :
      Head μ (cfinE (cancelVal err) (.val w)) μ (raiseE (.val (cancelVal err)))
  /-- `[cfin-raise]`: the finaliser raised `(m, (j, w))`, `m` not the cancel's name; the cancel
      keeps the first error (`errNext`), and goes on.  `[spec §19]` -/
  | cferr (μ : Heap) (err : Option Val) (m j : UInt32) (w : Val) (K : Kont) (hm : m ≠ 0)
      (hK : K.Catches m = false) :
      Head μ (cfinE (cancelVal err) (K.plug (raiseE (.val (opPayload m j w))))) μ
        (raiseE (.val (cancelVal (errNext err m j w))))
  /-- `[cfin-cancel]`: a cancel reached the running finaliser's `cfin`; it keeps the earlier
      error, the finaliser's cancel's, and goes on.  `[spec §19]` -/
  | cfcancel (μ : Heap) (err err' : Option Val) (K : Kont) (hK : K.Catches 0 = false) :
      Head μ (cfinE (cancelVal err) (K.plug (raiseE (.val (cancelVal err'))))) μ
        (raiseE (.val (cancelVal (err.or err'))))
  /-- `[cancel]`: `ccatch K[raise (0, (0, none))] ↦ ()`, `K` catching nothing of `0`.
      `[spec §19]` -/
  | cancel (μ : Heap) (K : Kont) (hK : K.Catches 0 = false) :
      Head μ (ccatchE (K.plug (raiseE (.val (cancelVal none))))) μ (.val .unit)
  /-- `[cancel-raise]`: `ccatch K[raise (0, (0, some E))] ↦ raise E`: the kept error, raised at
      the canceller.  `[spec §19]` -/
  | creraise (μ : Heap) (E : Val) (K : Kont) (hK : K.Catches 0 = false) :
      Head μ (ccatchE (K.plug (raiseE (.val (cancelVal (some E)))))) μ (raiseE (.val E))

/-!
Rows 3.11, 3.12, continued.
-/
/-- `(μ,e) ↦ (μ',e')  ⟹  (μ, K[e]) → (μ', K[e'])`. -/
def Step1 {ℍ : Host} [HostIs ℍ] (μ : Heap) (e : Expr) (μ' : Heap) (e' : Expr) : Prop :=
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
