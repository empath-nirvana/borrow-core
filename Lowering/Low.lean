import Frontend.Check.TExpr

/-!
# Lowering — the low subset of `Expr`  `[spec §53]`

The ownership and control layers of the lowering (SPEC §53) are `Expr → Expr` steps whose output
is in the kernel's relation at the source's type. Their output is in **the low subset** defined
here, the input of the print to the LIR. The print reads no type, so the low subset makes explicit
everything the print would otherwise have to decide:

- **Every variable is consumed exactly once on every path** (`Explicit`, `once`). A persistent
  value used twice goes through the kernel's `copy`, and a value left unused goes through
  `forget` or its destructor `dtorE A` (`dropE`). The print then places no copy and no drop of
  its own: each LIR `copy` and `drop` is the image of one of these constants. This is the LIR's
  own discipline (`Backend2/Syntax.lean`).
- **A path may end at `absurd`** (`absurdE`, the kernel's `case V {x. x | y. y}` at `V : 0`).
  The kernel's `[0E]` absorbs the rest of the context, and the LIR's `absurd` ends the path, so
  a variable may be left unused on a path that ends there. The form is reserved for `absurd`: a
  low term that needs a codiagonal `A ⊕ A → A` writes it otherwise.
- **The kernel's constants are atoms** (`LowConst`): the closed terms the erasure gives a typed
  node with no premise (`copy`, `forget`, `swap`, `dtorE A`, the array and borrow constants, the
  folds, …). Their bodies are the kernel's, not the program's: `copy` itself is `λx. (x, x)`, and
  the print maps each to its LIR operation or generated function.
- **No effect primitive except at a stored-continuation site** (`EffOnlyAt`). The handler and
  control primitives of §19 and `iterate` (whose step performs `Div`'s tick, §14) occur only
  inside a subterm the site predicate `Site` accepts. The static sites are erased in `Expr` by
  their handler laws (U3); a site whose continuation is stored is kept. `Site` is a parameter
  because the representation of a stored continuation is not decided (#703): under K1 (the
  machine's own capture as heap frames) `Site` accepts the stored sites' handler terms; under K2
  (state machines in `Expr`) it accepts nothing (`noSite`). `LowExpr.mono` shows that widening
  `Site` keeps every low term low.
-/

namespace Lowering
open BoCa
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Check

/-! ### Variables -/

/-- `e` mentions the variable `i` (de Bruijn). -/
def mentions : Expr → Nat → Bool
  | .var j, i => j == i
  | .unit, _ | .loc _, _ | .prim _, _ => false
  | .pair a b, i | .seq a b, i | .app a b, i => mentions a i || mentions b i
  | .inj₁ a, i | .inj₂ a, i => mentions a i
  | .lam b, i => mentions b (i + 1)
  | .letpair a b, i => mentions a i || mentions b (i + 2)
  | .case s a b, i => mentions s i || mentions a (i + 1) || mentions b (i + 1)

/-- How often a variable is used on a term's paths: `ret`, the count on every path that returns
(`none` when none returns); `stop`, the most on a path that ends at `absurd` (`none` when none
ends there). -/
structure Uses where
  ret : Option Nat
  stop : Option Nat
  deriving DecidableEq, Repr

/-- The larger of two optional counts. -/
def maxO : Option Nat → Option Nat → Option Nat
  | some x, some y => some (max x y)
  | some x, none => some x
  | none, y => y

namespace Uses

/-- Unused, every path returning. -/
def zero : Uses := ⟨some 0, none⟩
/-- Used once, every path returning. -/
def one : Uses := ⟨some 1, none⟩
/-- Every path ends at `absurd`, unused there. -/
def halt : Uses := ⟨none, some 0⟩

/-- `a`'s term, then `b`'s: `b` runs only on `a`'s returning paths. -/
def andThen (a b : Uses) : Uses :=
  match a.ret with
  | none => a
  | some r => ⟨b.ret.map (r + ·), maxO a.stop (b.stop.map (r + ·))⟩

/-- Two arms of a `case`: their returning paths must agree, or the variable is consumed on one
arm and not the other (`none`). -/
def join (a b : Uses) : Option Uses :=
  match a.ret, b.ret with
  | some x, some y => if x = y then some ⟨some x, maxO a.stop b.stop⟩ else none
  | some x, none | none, some x => some ⟨some x, maxO a.stop b.stop⟩
  | none, none => some ⟨none, maxO a.stop b.stop⟩

end Uses

/-- The uses of the variable `i` in `e`, in the machine's order (a pair left first, an
application its argument first); `none` when two arms of a `case` disagree. A `λ` is a closure:
it consumes the variable once when its body mentions it (its body's own paths are its calls').
`case V {x. x | y. y}` is `absurd`: its paths end. -/
def occ : Expr → Nat → Option Uses
  | .var j, i => some (if j = i then .one else .zero)
  | .unit, _ | .loc _, _ | .prim _, _ => some .zero
  | .pair a b, i | .seq a b, i => do pure ((← occ a i).andThen (← occ b i))
  | .app f a, i => do pure ((← occ a i).andThen (← occ f i))
  | .inj₁ a, i | .inj₂ a, i => occ a i
  | .lam b, i => some ⟨some (if mentions b (i + 1) then 1 else 0), none⟩
  | .letpair a b, i => do pure ((← occ a i).andThen (← occ b (i + 2)))
  | .case s (.var 0) (.var 0), i => do pure ((← occ s i).andThen .halt)
  | .case s a b, i => do pure ((← occ s i).andThen (← Uses.join (← occ a (i + 1)) (← occ b (i + 1))))

/-- Consumed exactly once on every returning path, and at most once on a path that ends at
`absurd`. -/
def once : Option Uses → Bool
  | some ⟨r, s⟩ => (r == some 1 || r == none) && (match s with | some k => k ≤ 1 | none => true)
  | none => false

/-! ### The kernel's constants -/

/-- A typed node with no premise whose erasure is a closed constant of the kernel. -/
def constNode : TExpr → Bool
  | .copyBang .. | .forgetBang .. | .alloc .. | .free .. | .swap .. | .copy .. | .forgetImm ..
  | .forgetMut .. | .forgetUnk .. | .lit .. | .hostOp .. | .arrNew .. | .arrFree .. | .arrSize ..
  | .arrReplace .. | .arrLen .. | .arrGet .. | .arrCopy .. | .arrForget .. | .countFold ..
  | .countTry .. | .boundedFix .. | .iterate .. | .divFuel .. | .sliceBorrowM .. | .sliceBorrowI ..
  | .sliceGetM .. | .sliceLenM .. | .sliceSplitI .. | .sliceSplitM .. | .sliceEmptyI ..
  | .sliceEmptyM .. | .sliceReplaceM .. | .sliceSwapM .. | .withbor1 .. | .withbor2 ..
  | .withbor3 .. | .withload .. | .withswap .. | .withloadU .. | .foldImm .. | .foldOwn ..
  | .foldReuse .. | .unfoldN .. | .dtor .. | .allocS .. | .freeS .. | .withborSM .. | .withborSI ..
  | .withborF2M .. | .withborF2I .. => true
  | _ => false

/-- A constant of the kernel: the erasure of a typed node with no premise. -/
inductive LowConst : Expr → Prop where
  | node (t : TExpr) (h : constNode t = true) : LowConst t.erase

/-! ### Effect primitives -/

/-- The effect primitives: `perform`, `raise` and the frames `hnd`, `ubind`, `ccatch`, `cfin` of
§19, and `iterate`, whose step performs `Div`'s tick (§14). -/
def effPrim : Prim → Bool
  | .perform | .raise | .hnd | .ubind | .ccatch | .cfin | .iterate => true
  | _ => false

/-- Every effect primitive of `e` is inside a subterm `Site` accepts. -/
inductive EffOnlyAt (Site : Expr → Prop) : Expr → Prop where
  | site {e : Expr} (h : Site e) : EffOnlyAt Site e
  | var (i : Nat) : EffOnlyAt Site (.var i)
  | unit : EffOnlyAt Site .unit
  | loc (ℓ : Loc) : EffOnlyAt Site (.loc ℓ)
  | prim {p : Prim} (h : effPrim p = false) : EffOnlyAt Site (.prim p)
  | pair {a b : Expr} (ha : EffOnlyAt Site a) (hb : EffOnlyAt Site b) : EffOnlyAt Site (.pair a b)
  | inj₁ {a : Expr} (h : EffOnlyAt Site a) : EffOnlyAt Site (.inj₁ a)
  | inj₂ {a : Expr} (h : EffOnlyAt Site a) : EffOnlyAt Site (.inj₂ a)
  | lam {b : Expr} (h : EffOnlyAt Site b) : EffOnlyAt Site (.lam b)
  | seq {a b : Expr} (ha : EffOnlyAt Site a) (hb : EffOnlyAt Site b) : EffOnlyAt Site (.seq a b)
  | letpair {a b : Expr} (ha : EffOnlyAt Site a) (hb : EffOnlyAt Site b) :
      EffOnlyAt Site (.letpair a b)
  | case {s a b : Expr} (hs : EffOnlyAt Site s) (ha : EffOnlyAt Site a) (hb : EffOnlyAt Site b) :
      EffOnlyAt Site (.case s a b)
  | app {f a : Expr} (hf : EffOnlyAt Site f) (ha : EffOnlyAt Site a) : EffOnlyAt Site (.app f a)

/-- No stored-continuation site: no effect primitive anywhere (the K2 reading). -/
def noSite : Expr → Prop := fun _ => False

theorem EffOnlyAt.mono {Site Site' : Expr → Prop} (hS : ∀ e, Site e → Site' e) {e : Expr}
    (h : EffOnlyAt Site e) : EffOnlyAt Site' e := by
  induction h with
  | site h => exact .site (hS _ h)
  | var i => exact .var i
  | unit => exact .unit
  | loc ℓ => exact .loc ℓ
  | prim h => exact .prim h
  | pair _ _ iha ihb => exact .pair iha ihb
  | inj₁ _ ih => exact .inj₁ ih
  | inj₂ _ ih => exact .inj₂ ih
  | lam _ ih => exact .lam ih
  | seq _ _ iha ihb => exact .seq iha ihb
  | letpair _ _ iha ihb => exact .letpair iha ihb
  | case _ _ _ ihs iha ihb => exact .case ihs iha ihb
  | app _ _ ihf iha => exact .app ihf iha

/-! ### Explicit ownership -/

/-- Every binder of `e`, and every variable a `λ` of `e` captures, is consumed exactly once on
every path (`once`), outside the kernel's constants. -/
inductive Explicit : Expr → Prop where
  | const {c : Expr} (h : LowConst c) : Explicit c
  | var (i : Nat) : Explicit (.var i)
  | unit : Explicit .unit
  | loc (ℓ : Loc) : Explicit (.loc ℓ)
  | prim (p : Prim) : Explicit (.prim p)
  | pair {a b : Expr} (ha : Explicit a) (hb : Explicit b) : Explicit (.pair a b)
  | inj₁ {a : Expr} (h : Explicit a) : Explicit (.inj₁ a)
  | inj₂ {a : Expr} (h : Explicit a) : Explicit (.inj₂ a)
  | lam {b : Expr} (h : Explicit b) (h0 : once (occ b 0) = true)
      (hcap : ∀ j, mentions b (j + 1) = true → once (occ b (j + 1)) = true) : Explicit (.lam b)
  | seq {a b : Expr} (ha : Explicit a) (hb : Explicit b) : Explicit (.seq a b)
  | letpair {a b : Expr} (ha : Explicit a) (hb : Explicit b) (h0 : once (occ b 0) = true)
      (h1 : once (occ b 1) = true) : Explicit (.letpair a b)
  | case {s a b : Expr} (hs : Explicit s) (ha : Explicit a) (hb : Explicit b)
      (h₁ : once (occ a 0) = true) (h₂ : once (occ b 0) = true) : Explicit (.case s a b)
  | app {f a : Expr} (hf : Explicit f) (ha : Explicit a) : Explicit (.app f a)

/-! ### The low subset -/

/-- **The low subset**: `e`, over a context of `n` variables, has its ownership explicit, each
context variable consumed once on every path and no other free variable, and its effect
primitives only at the sites `Site` accepts. -/
structure LowExpr (Site : Expr → Prop) (n : Nat) (e : Expr) : Prop where
  explicit : Explicit e
  effects : EffOnlyAt Site e
  context : ∀ j, j < n → once (occ e j) = true
  closed : ∀ j, n ≤ j → mentions e j = false

theorem LowExpr.mono {Site Site' : Expr → Prop} (hS : ∀ e, Site e → Site' e) {n : Nat}
    {e : Expr} (h : LowExpr Site n e) : LowExpr Site' n e :=
  ⟨h.explicit, h.effects.mono hS, h.context, h.closed⟩

/-! ### Non-vacuity -/

/-- `()` is low, with no site. -/
theorem lowExpr_unit : LowExpr noSite 0 (.val .unit) :=
  ⟨.unit, .unit, fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ => rfl⟩

/-- `copy` is a constant of the kernel. -/
theorem lowConst_copy : LowConst BoCa.copy :=
  LowConst.node (.copyBang default (.val .unit) .unit) rfl

/-- `copy`'s own body uses its binder twice: the kernel's constants are atoms. -/
theorem copy_body_not_once : once (occ (.pair (.var 0) (.var 0)) 0) = false := by decide

/-- `(λx. let (y, z) = copy x; (y, z)) 7`: a binder used twice through an explicit `copy`. -/
def copyTwice : Expr :=
  .app (.lam (.letpair (.app BoCa.copy (.var 0)) (.pair (.var 1) (.var 0))))
    (.prim (.lit (.i32 7)))

theorem lowExpr_copyTwice : LowExpr noSite 0 copyTwice := by
  refine ⟨?_, ?_, fun _ h => absurd h (Nat.not_lt_zero _), fun j _ => ?_⟩
  · refine .app (.lam (.letpair (.app (.const lowConst_copy) (.var 0)) (.pair (.var 1) (.var 0))
      (by decide) (by decide)) (by decide) ?_) (.prim _)
    intro j hj
    simp [mentions, BoCa.copy, BoCa.v0] at hj
  · exact .app (.lam (.letpair (.app (.lam (.pair (.var 0) (.var 0))) (.var 0))
      (.pair (.var 1) (.var 0)))) (.prim rfl)
  · simp [copyTwice, mentions, BoCa.copy, BoCa.v0]

/-- `λx. absurd y` at a context of one variable `y`: `x` is left unused on a path that ends at
`absurd`. -/
theorem lowExpr_absurd : LowExpr noSite 1 (.lam (absurdE (.var 1))) := by
  refine ⟨.lam (.case (.var 1) (.var 0) (.var 0) (by decide) (by decide)) (by decide) ?_,
    .lam (.case (.var 1) (.var 0) (.var 0)), fun j hj => ?_, fun j hj => ?_⟩
  · intro j hj
    have : j = 0 := by simpa [mentions, absurdE] using hj
    subst this; decide
  · have : j = 0 := by omega
    subst this; decide
  · simp only [mentions, absurdE]; simp; omega

end Lowering
