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
- **A path may end at `absurd`** (`absurdL`): `case V {x. stuck | y. stuck}`, both arms the
  machine's stuck term `stuckE` (`() ()`). A lowering writes it where the typed term has `[0E]`
  (`zeroE`, `V : 0`), so absurdity is read from the checked derivation, not from a term's shape:
  no typed term applies `()`, so a codiagonal `case V {x. x | y. y}` at `A ⊕ A` is an ordinary
  `case` here, whose arms must agree (`not_lowExpr_codiag`). The kernel's `[0E]` absorbs the rest
  of the context and the LIR's `absurd` ends the path, so a variable may be left unused on a path
  that ends there; an arm, if one were reached, is a stuck redex (`stuckAt_unit_app`).
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

/-- **The low subset's `absurd`**: `case V {x. stuck | y. stuck}`, the arms the stuck term `() ()`.
The form a lowering writes at a `[0E]` node of the typed term (`zeroE`). -/
def absurdL (V : Expr) : Expr := .case V BoLo.stuckE BoLo.stuckE

/-- The uses of the variable `i` in `e`, in the machine's order (a pair left first, an
application its argument first); `none` when two arms of a `case` disagree. A `λ` is a closure:
it consumes the variable once when its body mentions it (its body's own paths are its calls').
`absurdL V` is `absurd`: its paths end. -/
def occ : Expr → Nat → Option Uses
  | .var j, i => some (if j = i then .one else .zero)
  | .unit, _ | .loc _, _ | .prim _, _ => some .zero
  | .pair a b, i | .seq a b, i => do pure ((← occ a i).andThen (← occ b i))
  | .app f a, i => do pure ((← occ a i).andThen (← occ f i))
  | .inj₁ a, i | .inj₂ a, i => occ a i
  | .lam b, i => some ⟨some (if mentions b (i + 1) then 1 else 0), none⟩
  | .letpair a b, i => do pure ((← occ a i).andThen (← occ b (i + 2)))
  | .case s a b, i =>
      if a = BoLo.stuckE ∧ b = BoLo.stuckE then do pure ((← occ s i).andThen .halt)
      else do pure ((← occ s i).andThen (← Uses.join (← occ a (i + 1)) (← occ b (i + 1))))

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
  /-- `absurd`: its arms are never run, and bind nothing used. -/
  | absurd {s : Expr} (hs : Explicit s) : Explicit (absurdL s)
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

/-! ### The decision -/

/-- One more than the largest free variable of `e` (`0` when it has none). -/
def fvBound : Expr → Nat
  | .var i => i + 1
  | .unit | .loc _ | .prim _ => 0
  | .pair a b | .seq a b | .app a b => max (fvBound a) (fvBound b)
  | .inj₁ a | .inj₂ a => fvBound a
  | .lam b => fvBound b - 1
  | .letpair a b => max (fvBound a) (fvBound b - 2)
  | .case s a b => max (fvBound s) (max (fvBound a - 1) (fvBound b - 1))

theorem mentions_lt {e : Expr} {i : Nat} (h : mentions e i = true) : i < fvBound e := by
  induction e generalizing i with
  | var j => simp [mentions] at h; simp [fvBound]; omega
  | unit | loc _ | prim _ => simp [mentions] at h
  | pair a b iha ihb | seq a b iha ihb | app a b iha ihb =>
      simp only [mentions, Bool.or_eq_true] at h
      simp only [fvBound]
      rcases h with h | h
      · exact lt_max_of_lt_left (iha h)
      · exact lt_max_of_lt_right (ihb h)
  | inj₁ a ih | inj₂ a ih => simp only [mentions] at h; exact ih h
  | lam b ih => simp only [mentions] at h; have := ih h; simp only [fvBound]; omega
  | letpair a b iha ihb =>
      simp only [mentions, Bool.or_eq_true] at h
      simp only [fvBound]
      rcases h with h | h
      · exact lt_max_of_lt_left (iha h)
      · have := ihb h; exact lt_max_of_lt_right (by omega)
  | case s a b ihs iha ihb =>
      simp only [mentions, Bool.or_eq_true] at h
      simp only [fvBound]
      rcases h with (h | h) | h
      · exact lt_max_of_lt_left (ihs h)
      · have := iha h
        exact lt_max_of_lt_right (lt_max_of_lt_left (by omega))
      · have := ihb h
        exact lt_max_of_lt_right (lt_max_of_lt_right (by omega))

/-- Every variable `j + 1` a `λ`-body mentions is consumed once in it. -/
def capOnceB (b : Expr) : Bool :=
  (List.range (fvBound b)).all fun j => !mentions b (j + 1) || once (occ b (j + 1))

/-- `Explicit`, decided, with `isConst` deciding which terms are the kernel's constants. -/
def explicitB (isConst : Expr → Bool) (e : Expr) : Bool :=
  isConst e || match e with
    | .var _ => true
    | .unit => true
    | .loc _ => true
    | .prim _ => true
    | .pair a b => explicitB isConst a && explicitB isConst b
    | .seq a b => explicitB isConst a && explicitB isConst b
    | .app a b => explicitB isConst a && explicitB isConst b
    | .inj₁ a => explicitB isConst a
    | .inj₂ a => explicitB isConst a
    | .lam b => explicitB isConst b && once (occ b 0) && capOnceB b
    | .letpair a b => explicitB isConst a && explicitB isConst b && once (occ b 0) &&
        once (occ b 1)
    | .case s a b =>
        if a = BoLo.stuckE ∧ b = BoLo.stuckE then explicitB isConst s
        else explicitB isConst s && explicitB isConst a && explicitB isConst b &&
          once (occ a 0) && once (occ b 0)

/-- No effect primitive anywhere. -/
def effFreeB : Expr → Bool
  | .var _ | .unit | .loc _ => true
  | .prim p => !effPrim p
  | .pair a b | .seq a b | .app a b | .letpair a b => effFreeB a && effFreeB b
  | .inj₁ a | .inj₂ a | .lam a => effFreeB a
  | .case s a b => effFreeB s && effFreeB a && effFreeB b

/-- `LowExpr` at no site, decided, with `isConst` deciding the kernel's constants. -/
def lowB (isConst : Expr → Bool) (n : Nat) (e : Expr) : Bool :=
  explicitB isConst e && effFreeB e && (List.range n).all (fun j => once (occ e j)) &&
    decide (fvBound e ≤ n)

theorem explicitB_sound {isConst : Expr → Bool} (hc : ∀ e, isConst e = true → LowConst e) :
    ∀ {e : Expr}, explicitB isConst e = true → Explicit e := by
  intro e
  induction e with
  | var i => intro _; exact .var i
  | unit => intro _; exact .unit
  | loc ℓ => intro _; exact .loc ℓ
  | prim p => intro _; exact .prim p
  | pair a b iha ihb =>
      intro h; rw [explicitB.eq_def] at h
      cases hce : isConst (.pair a b)
      · simp only [hce, Bool.false_or, Bool.and_eq_true] at h; exact .pair (iha h.1) (ihb h.2)
      · exact .const (hc _ hce)
  | seq a b iha ihb =>
      intro h; rw [explicitB.eq_def] at h
      cases hce : isConst (.seq a b)
      · simp only [hce, Bool.false_or, Bool.and_eq_true] at h; exact .seq (iha h.1) (ihb h.2)
      · exact .const (hc _ hce)
  | app a b iha ihb =>
      intro h; rw [explicitB.eq_def] at h
      cases hce : isConst (.app a b)
      · simp only [hce, Bool.false_or, Bool.and_eq_true] at h; exact .app (iha h.1) (ihb h.2)
      · exact .const (hc _ hce)
  | inj₁ a ih =>
      intro h; rw [explicitB.eq_def] at h
      cases hce : isConst (.inj₁ a)
      · simp only [hce, Bool.false_or] at h; exact .inj₁ (ih h)
      · exact .const (hc _ hce)
  | inj₂ a ih =>
      intro h; rw [explicitB.eq_def] at h
      cases hce : isConst (.inj₂ a)
      · simp only [hce, Bool.false_or] at h; exact .inj₂ (ih h)
      · exact .const (hc _ hce)
  | lam b ih =>
      intro h; rw [explicitB.eq_def] at h
      cases hce : isConst (.lam b)
      · simp only [hce, Bool.false_or, Bool.and_eq_true] at h
        refine .lam (ih h.1.1) h.1.2 fun j hj => ?_
        have := List.all_eq_true.mp h.2 j (List.mem_range.mpr (by have := mentions_lt hj; omega))
        simpa [hj] using this
      · exact .const (hc _ hce)
  | letpair a b iha ihb =>
      intro h; rw [explicitB.eq_def] at h
      cases hce : isConst (.letpair a b)
      · simp only [hce, Bool.false_or, Bool.and_eq_true] at h
        exact .letpair (iha h.1.1.1) (ihb h.1.1.2) h.1.2 h.2
      · exact .const (hc _ hce)
  | case s a b ihs iha ihb =>
      intro h; rw [explicitB.eq_def] at h
      cases hce : isConst (.case s a b)
      · simp only [hce, Bool.false_or] at h
        by_cases hab : a = BoLo.stuckE ∧ b = BoLo.stuckE
        · rw [if_pos hab] at h
          obtain ⟨rfl, rfl⟩ := hab
          exact .absurd (ihs h)
        · rw [if_neg hab] at h
          simp only [Bool.and_eq_true] at h
          exact .case (ihs h.1.1.1.1) (iha h.1.1.1.2) (ihb h.1.1.2) h.1.2 h.2
      · exact .const (hc _ hce)

theorem effFreeB_sound {Site : Expr → Prop} : ∀ {e : Expr}, effFreeB e = true → EffOnlyAt Site e
  | .var i, _ => .var i
  | .unit, _ => .unit
  | .loc ℓ, _ => .loc ℓ
  | .prim p, h => .prim (by simpa [effFreeB] using h)
  | .pair a b, h => by
      simp only [effFreeB, Bool.and_eq_true] at h
      exact .pair (effFreeB_sound h.1) (effFreeB_sound h.2)
  | .seq a b, h => by
      simp only [effFreeB, Bool.and_eq_true] at h
      exact .seq (effFreeB_sound h.1) (effFreeB_sound h.2)
  | .app a b, h => by
      simp only [effFreeB, Bool.and_eq_true] at h
      exact .app (effFreeB_sound h.1) (effFreeB_sound h.2)
  | .letpair a b, h => by
      simp only [effFreeB, Bool.and_eq_true] at h
      exact .letpair (effFreeB_sound h.1) (effFreeB_sound h.2)
  | .inj₁ a, h => .inj₁ (effFreeB_sound h)
  | .inj₂ a, h => .inj₂ (effFreeB_sound h)
  | .lam a, h => .lam (effFreeB_sound h)
  | .case s a b, h => by
      simp only [effFreeB, Bool.and_eq_true] at h
      exact .case (effFreeB_sound h.1.1) (effFreeB_sound h.1.2) (effFreeB_sound h.2)

/-- **The decision is sound**: a term `lowB` accepts is low, at any site. -/
theorem lowB_sound {isConst : Expr → Bool} (hc : ∀ e, isConst e = true → LowConst e)
    {Site : Expr → Prop} {n : Nat} {e : Expr} (h : lowB isConst n e = true) : LowExpr Site n e := by
  simp only [lowB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hx, hf⟩, hctx⟩, hb⟩ := h
  refine ⟨explicitB_sound hc hx, effFreeB_sound hf, fun j hj => ?_, fun j hj => ?_⟩
  · exact List.all_eq_true.mp hctx j (List.mem_range.mpr hj)
  · cases hm : mentions e j
    · rfl
    · have := mentions_lt hm; omega

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
theorem lowExpr_absurd : LowExpr noSite 1 (.lam (absurdL (.var 1))) := by
  refine ⟨.lam (.absurd (.var 1)) (by decide) ?_, ?_, fun j hj => ?_, fun j hj => ?_⟩
  · intro j hj
    have : j = 0 := by simpa [mentions, absurdL, BoLo.stuckE] using hj
    subst this; decide
  · exact .lam (.case (.var 1) (.app .unit .unit) (.app .unit .unit))
  · have : j = 0 := by omega
    subst this; decide
  · have : j ≠ 0 := by omega
    simp [mentions, absurdL, BoLo.stuckE, this]

/-- **A codiagonal is not `absurd`**: `case x {a. a | b. b}` at a context `x, y` leaves `y` unused
on paths that return, so it is not low; `absurd x` there is. The kernel's own `absurdE` has the
codiagonal's shape; the low subset reads `absurd` only at `absurdL`. -/
theorem not_lowExpr_codiag : ¬ LowExpr noSite 2 (.case (.var 0) (.var 0) (.var 0)) :=
  fun h => absurd (h.context 1 (by decide)) (by decide)

/-- `absurd x` at the context `x, y`: `y` is left unused on its path, which ends. -/
theorem lowExpr_absurd_ctx : LowExpr noSite 2 (absurdL (.var 0)) := by
  refine ⟨.absurd (.var 0), .case (.var 0) (.app .unit .unit) (.app .unit .unit),
    fun j hj => ?_, fun j hj => ?_⟩
  · have : j = 0 ∨ j = 1 := by omega
    rcases this with rfl | rfl <;> decide
  · simp [mentions, absurdL, BoLo.stuckE]
    omega

end Lowering
