import Paper.S1_Syntax.Definitions

/-!
# Support — Syntax — Terms

`[about ours]`.  Value inversion lemmas, shifting and substitution on de Bruijn terms (single and parallel), and the names of `[TR]` p. 3's derived forms and of the first de Bruijn variables.
-/

noncomputable section

namespace BoCa

theorem IsVal.pair_left {a b : Expr} (h : IsVal (.pair a b)) : IsVal a := by
  cases h; assumption

theorem IsVal.pair_right {a b : Expr} (h : IsVal (.pair a b)) : IsVal b := by
  cases h; assumption

@[simp] theorem isVal_pair_iff {a b : Expr} : IsVal (.pair a b) ↔ IsVal a ∧ IsVal b :=
  ⟨fun h => ⟨h.pair_left, h.pair_right⟩, fun h => .pair h.1 h.2⟩

theorem IsVal.inj₁_inv {a : Expr} (h : IsVal (.inj₁ a)) : IsVal a := by cases h; assumption

@[simp] theorem isVal_inj₁_iff {a : Expr} : IsVal (.inj₁ a) ↔ IsVal a :=
  ⟨IsVal.inj₁_inv, .inj₁⟩

theorem IsVal.inj₂_inv {a : Expr} (h : IsVal (.inj₂ a)) : IsVal a := by cases h; assumption

@[simp] theorem isVal_inj₂_iff {a : Expr} : IsVal (.inj₂ a) ↔ IsVal a :=
  ⟨IsVal.inj₂_inv, .inj₂⟩

/-- A value whose root is an application is `store v`: its function part is the
    primitive `store` and its argument is a value. -/
theorem IsVal.app_fun {f a : Expr} (h : IsVal (.app f a)) : f = .prim .store := by
  cases h; rfl

theorem IsVal.app_arg {f a : Expr} (h : IsVal (.app f a)) : IsVal a := by
  cases h; assumption

@[simp] theorem isVal_app_iff {f a : Expr} :
    IsVal (.app f a) ↔ f = .prim .store ∧ IsVal a :=
  ⟨fun h => ⟨h.app_fun, h.app_arg⟩, fun h => h.1 ▸ .storeV h.2⟩

def Expr.shift (d : Nat) (c : Nat) : Expr → Expr
  | .var i         => if i < c then .var i else .var (i + d)
  | .unit          => .unit
  | .pair e₁ e₂    => .pair (e₁.shift d c) (e₂.shift d c)
  | .inj₁ e        => .inj₁ (e.shift d c)
  | .inj₂ e        => .inj₂ (e.shift d c)
  | .lam b         => .lam (b.shift d (c + 1))
  | .loc ℓ         => .loc ℓ
  | .prim p        => .prim p
  | .seq e₁ e₂     => .seq (e₁.shift d c) (e₂.shift d c)
  | .letpair e₁ e₂ => .letpair (e₁.shift d c) (e₂.shift d (c + 2))
  | .case e e₁ e₂  => .case (e.shift d c) (e₁.shift d (c + 1)) (e₂.shift d (c + 1))
  | .app f a       => .app (f.shift d c) (a.shift d c)

theorem IsVal.shift {e : Expr} (h : IsVal e) (d c : Nat) : IsVal (e.shift d c) := by
  induction h generalizing c with
  | unit => exact .unit
  | pair _ _ ih₁ ih₂ => exact .pair (ih₁ c) (ih₂ c)
  | inj₁ _ ih => exact .inj₁ (ih c)
  | inj₂ _ ih => exact .inj₂ (ih c)
  | lam => exact .lam
  | loc => exact .loc
  | prim => exact .prim
  | storeV _ ih => simp only [Expr.shift]; exact .storeV (ih c)

def Val.shift (d : Nat) (c : Nat) (v : Val) : Val := ⟨v.1.shift d c, v.2.shift d c⟩

@[simp] theorem Val.val_shift (d c : Nat) (v : Val) :
    (Val.shift d c v).val = v.val.shift d c := rfl

def Expr.subst (j : Nat) (s : Val) : Expr → Expr
  | .var i         => if i = j then s.val else if i > j then .var (i - 1) else .var i
  | .unit          => .unit
  | .pair e₁ e₂    => .pair (e₁.subst j s) (e₂.subst j s)
  | .inj₁ e        => .inj₁ (e.subst j s)
  | .inj₂ e        => .inj₂ (e.subst j s)
  | .lam b         => .lam (b.subst (j + 1) (s.shift 1 0))
  | .loc ℓ         => .loc ℓ
  | .prim p        => .prim p
  | .seq e₁ e₂     => .seq (e₁.subst j s) (e₂.subst j s)
  | .letpair e₁ e₂ => .letpair (e₁.subst j s) (e₂.subst (j + 2) (s.shift 2 0))
  | .case e e₁ e₂  =>
      .case (e.subst j s) (e₁.subst (j + 1) (s.shift 1 0)) (e₂.subst (j + 1) (s.shift 1 0))
  | .app f a       => .app (f.subst j s) (a.subst j s)

theorem IsVal.subst {e : Expr} (h : IsVal e) (j : Nat) (s : Val) :
    IsVal (e.subst j s) := by
  induction h generalizing j s with
  | unit => exact .unit
  | pair _ _ ih₁ ih₂ => exact .pair (ih₁ j s) (ih₂ j s)
  | inj₁ _ ih => exact .inj₁ (ih j s)
  | inj₂ _ ih => exact .inj₂ (ih j s)
  | lam => exact .lam
  | loc => exact .loc
  | prim => exact .prim
  | storeV _ ih => simp only [Expr.subst]; exact .storeV (ih j s)

def Val.subst (j : Nat) (s : Val) (v : Val) : Val := ⟨v.1.subst j s, v.2.subst j s⟩

@[simp] theorem Val.val_subst (j : Nat) (s v : Val) :
    (Val.subst j s v).val = v.val.subst j s := rfl

/-! ### Shifting and substituting, executably

`Expr.subst` shifts the value it substitutes at each binder it passes, which rebuilds the value
each time, and `Expr.shift` and `Expr.subst` copy every node, changed or not. A closed value is
unchanged by a shift, so substituting one needs no shift: `Expr.substFast` checks closedness
once and substitutes without shifting, and both `Expr.substFast` and `Expr.shiftFast` keep each
subterm they leave unchanged instead of copying it. `Expr.subst_eq_substFast` and
`Expr.shift_eq_shiftFast` prove them equal to `Expr.subst` and `Expr.shift`, so compiled code
runs them in their place (`@[csimp]`). Every statement still reads `Expr.subst` and
`Expr.shift`. -/

/-- Every free variable of `e` is below `k`. -/
def Expr.closedAt (k : Nat) : Expr → Bool
  | .var i         => decide (i < k)
  | .unit          => true
  | .pair e₁ e₂    => e₁.closedAt k && e₂.closedAt k
  | .inj₁ e        => e.closedAt k
  | .inj₂ e        => e.closedAt k
  | .lam b         => b.closedAt (k + 1)
  | .loc _         => true
  | .prim _        => true
  | .seq e₁ e₂     => e₁.closedAt k && e₂.closedAt k
  | .letpair e₁ e₂ => e₁.closedAt k && e₂.closedAt (k + 2)
  | .case e e₁ e₂  => e.closedAt k && e₁.closedAt (k + 1) && e₂.closedAt (k + 1)
  | .app f a       => f.closedAt k && a.closedAt k

/-- A shift at or above every free variable is the identity. -/
theorem Expr.shift_of_closedAt : ∀ (e : Expr) {k : Nat} (d c : Nat),
    e.closedAt k = true → k ≤ c → e.shift d c = e
  | .var i, k, d, c, h, hc => by
      simp only [closedAt, decide_eq_true_eq] at h
      simp only [shift]; rw [if_pos (by omega)]
  | .unit, _, _, _, _, _ => rfl
  | .loc _, _, _, _, _, _ => rfl
  | .prim _, _, _, _, _, _ => rfl
  | .pair a b, k, d, c, h, hc => by
      simp only [closedAt, Bool.and_eq_true] at h
      simp only [shift, a.shift_of_closedAt d c h.1 hc, b.shift_of_closedAt d c h.2 hc]
  | .seq a b, k, d, c, h, hc => by
      simp only [closedAt, Bool.and_eq_true] at h
      simp only [shift, a.shift_of_closedAt d c h.1 hc, b.shift_of_closedAt d c h.2 hc]
  | .app a b, k, d, c, h, hc => by
      simp only [closedAt, Bool.and_eq_true] at h
      simp only [shift, a.shift_of_closedAt d c h.1 hc, b.shift_of_closedAt d c h.2 hc]
  | .inj₁ a, k, d, c, h, hc => by
      simp only [closedAt] at h; simp only [shift, a.shift_of_closedAt d c h hc]
  | .inj₂ a, k, d, c, h, hc => by
      simp only [closedAt] at h; simp only [shift, a.shift_of_closedAt d c h hc]
  | .lam b, k, d, c, h, hc => by
      simp only [closedAt] at h; simp only [shift, b.shift_of_closedAt d (c + 1) h (by omega)]
  | .letpair a b, k, d, c, h, hc => by
      simp only [closedAt, Bool.and_eq_true] at h
      simp only [shift, a.shift_of_closedAt d c h.1 hc,
        b.shift_of_closedAt d (c + 2) h.2 (by omega)]
  | .case e a b, k, d, c, h, hc => by
      simp only [closedAt, Bool.and_eq_true] at h
      simp only [shift, e.shift_of_closedAt d c h.1.1 hc,
        a.shift_of_closedAt d (c + 1) h.1.2 (by omega), b.shift_of_closedAt d (c + 1) h.2 (by omega)]

/-- A closed value is unchanged by a shift. -/
theorem Val.shift_of_closed {s : Val} (h : s.val.closedAt 0 = true) (d c : Nat) :
    s.shift d c = s :=
  Subtype.ext (Expr.shift_of_closedAt s.val d c h (Nat.zero_le c))

/-- `Expr.subst` of `s`, not shifted at the binders it passes. -/
def Expr.substClosed (j : Nat) (s : Expr) : Expr → Expr
  | .var i         => if i = j then s else if i > j then .var (i - 1) else .var i
  | .unit          => .unit
  | .pair e₁ e₂    => .pair (substClosed j s e₁) (substClosed j s e₂)
  | .inj₁ e        => .inj₁ (substClosed j s e)
  | .inj₂ e        => .inj₂ (substClosed j s e)
  | .lam b         => .lam (substClosed (j + 1) s b)
  | .loc ℓ         => .loc ℓ
  | .prim p        => .prim p
  | .seq e₁ e₂     => .seq (substClosed j s e₁) (substClosed j s e₂)
  | .letpair e₁ e₂ => .letpair (substClosed j s e₁) (substClosed (j + 2) s e₂)
  | .case e e₁ e₂  =>
      .case (substClosed j s e) (substClosed (j + 1) s e₁) (substClosed (j + 1) s e₂)
  | .app f a       => .app (substClosed j s f) (substClosed j s a)

theorem Expr.substClosed_eq {s : Val} (hs : s.val.closedAt 0 = true) :
    ∀ (e : Expr) (j : Nat), substClosed j s.val e = e.subst j s
  | .var i, j => rfl
  | .unit, _ | .loc _, _ | .prim _, _ => rfl
  | .pair a b, j | .seq a b, j | .app a b, j => by
      simp only [substClosed, subst, substClosed_eq hs a j, substClosed_eq hs b j]
  | .inj₁ a, j | .inj₂ a, j => by simp only [substClosed, subst, substClosed_eq hs a j]
  | .lam b, j => by
      simp only [substClosed, subst, Val.shift_of_closed hs, substClosed_eq hs b (j + 1)]
  | .letpair a b, j => by
      simp only [substClosed, subst, Val.shift_of_closed hs, substClosed_eq hs a j,
        substClosed_eq hs b (j + 2)]
  | .case e a b, j => by
      simp only [substClosed, subst, Val.shift_of_closed hs, substClosed_eq hs e j,
        substClosed_eq hs a (j + 1), substClosed_eq hs b (j + 1)]

/-- A node of one child rebuilt when its child changed (`some`), else unchanged (`none`). -/
@[inline] def Expr.rebuild1 (k : Expr → Expr) : Option Expr → Option Expr
  | none => none
  | some a' => some (k a')

/-- A node of two children rebuilt when either changed. -/
@[inline] def Expr.rebuild2 (k : Expr → Expr → Expr) (a b : Expr) :
    Option Expr → Option Expr → Option Expr
  | none, none => none
  | a', b' => some (k (a'.getD a) (b'.getD b))

/-- A node of three children rebuilt when any changed. -/
@[inline] def Expr.rebuild3 (k : Expr → Expr → Expr → Expr) (a b c : Expr) :
    Option Expr → Option Expr → Option Expr → Option Expr
  | none, none, none => none
  | a', b', c' => some (k (a'.getD a) (b'.getD b) (c'.getD c))

theorem Expr.rebuild2_getD (k : Expr → Expr → Expr) (a b : Expr) (oa ob : Option Expr) :
    (rebuild2 k a b oa ob).getD (k a b) = k (oa.getD a) (ob.getD b) := by
  cases oa <;> cases ob <;> rfl

theorem Expr.rebuild3_getD (k : Expr → Expr → Expr → Expr) (a b c : Expr)
    (oa ob oc : Option Expr) :
    (rebuild3 k a b c oa ob oc).getD (k a b c) = k (oa.getD a) (ob.getD b) (oc.getD c) := by
  cases oa <;> cases ob <;> cases oc <;> rfl

/-- `substClosed j s e` when it differs from `e` (`some`), and `none` where it is `e`: a subterm
with no variable at or above its index is kept, not copied. -/
def Expr.substO (j : Nat) (s : Expr) : Expr → Option Expr
  | .var i         => if i = j then some s else if i > j then some (.var (i - 1)) else none
  | .unit          => none
  | .pair e₁ e₂    => rebuild2 .pair e₁ e₂ (substO j s e₁) (substO j s e₂)
  | .inj₁ e        => rebuild1 .inj₁ (substO j s e)
  | .inj₂ e        => rebuild1 .inj₂ (substO j s e)
  | .lam b         => rebuild1 .lam (substO (j + 1) s b)
  | .loc _         => none
  | .prim _        => none
  | .seq e₁ e₂     => rebuild2 .seq e₁ e₂ (substO j s e₁) (substO j s e₂)
  | .letpair e₁ e₂ => rebuild2 .letpair e₁ e₂ (substO j s e₁) (substO (j + 2) s e₂)
  | .case e e₁ e₂  =>
      rebuild3 .case e e₁ e₂ (substO j s e) (substO (j + 1) s e₁) (substO (j + 1) s e₂)
  | .app f a       => rebuild2 .app f a (substO j s f) (substO j s a)

theorem Expr.substO_getD (s : Expr) : ∀ (e : Expr) (j : Nat),
    (substO j s e).getD e = substClosed j s e
  | .var i, j => by
      simp only [substO, substClosed]
      split
      · rfl
      · split <;> rfl
  | .unit, _ | .loc _, _ | .prim _, _ => rfl
  | .pair a b, j => by
      rw [substO, substClosed, ← substO_getD s a j, ← substO_getD s b j]
      exact rebuild2_getD _ a b _ _
  | .seq a b, j => by
      rw [substO, substClosed, ← substO_getD s a j, ← substO_getD s b j]
      exact rebuild2_getD _ a b _ _
  | .app a b, j => by
      rw [substO, substClosed, ← substO_getD s a j, ← substO_getD s b j]
      exact rebuild2_getD _ a b _ _
  | .letpair a b, j => by
      rw [substO, substClosed, ← substO_getD s a j, ← substO_getD s b (j + 2)]
      exact rebuild2_getD _ a b _ _
  | .inj₁ a, j => by
      rw [substO, substClosed, ← substO_getD s a j]
      cases substO j s a <;> rfl
  | .inj₂ a, j => by
      rw [substO, substClosed, ← substO_getD s a j]
      cases substO j s a <;> rfl
  | .lam b, j => by
      rw [substO, substClosed, ← substO_getD s b (j + 1)]
      cases substO (j + 1) s b <;> rfl
  | .case e a b, j => by
      rw [substO, substClosed, ← substO_getD s e j, ← substO_getD s a (j + 1),
        ← substO_getD s b (j + 1)]
      exact rebuild3_getD _ e a b _ _ _

/-- `e.shift d c` when it differs from `e` (`some`), and `none` where it is `e`. -/
def Expr.shiftO (d : Nat) : Nat → Expr → Option Expr
  | c, .var i         => if i < c then none else some (.var (i + d))
  | _, .unit          => none
  | c, .pair e₁ e₂    => rebuild2 .pair e₁ e₂ (shiftO d c e₁) (shiftO d c e₂)
  | c, .inj₁ e        => rebuild1 .inj₁ (shiftO d c e)
  | c, .inj₂ e        => rebuild1 .inj₂ (shiftO d c e)
  | c, .lam b         => rebuild1 .lam (shiftO d (c + 1) b)
  | _, .loc _         => none
  | _, .prim _        => none
  | c, .seq e₁ e₂     => rebuild2 .seq e₁ e₂ (shiftO d c e₁) (shiftO d c e₂)
  | c, .letpair e₁ e₂ => rebuild2 .letpair e₁ e₂ (shiftO d c e₁) (shiftO d (c + 2) e₂)
  | c, .case e e₁ e₂  =>
      rebuild3 .case e e₁ e₂ (shiftO d c e) (shiftO d (c + 1) e₁) (shiftO d (c + 1) e₂)
  | c, .app f a       => rebuild2 .app f a (shiftO d c f) (shiftO d c a)

theorem Expr.shiftO_getD (d : Nat) : ∀ (e : Expr) (c : Nat), (shiftO d c e).getD e = e.shift d c
  | .var i, c => by
      simp only [shiftO, shift]
      split <;> rfl
  | .unit, _ | .loc _, _ | .prim _, _ => rfl
  | .pair a b, c => by
      rw [shiftO, shift, ← shiftO_getD d a c, ← shiftO_getD d b c]
      exact rebuild2_getD _ a b _ _
  | .seq a b, c => by
      rw [shiftO, shift, ← shiftO_getD d a c, ← shiftO_getD d b c]
      exact rebuild2_getD _ a b _ _
  | .app a b, c => by
      rw [shiftO, shift, ← shiftO_getD d a c, ← shiftO_getD d b c]
      exact rebuild2_getD _ a b _ _
  | .letpair a b, c => by
      rw [shiftO, shift, ← shiftO_getD d a c, ← shiftO_getD d b (c + 2)]
      exact rebuild2_getD _ a b _ _
  | .inj₁ a, c => by
      rw [shiftO, shift, ← shiftO_getD d a c]
      cases shiftO d c a <;> rfl
  | .inj₂ a, c => by
      rw [shiftO, shift, ← shiftO_getD d a c]
      cases shiftO d c a <;> rfl
  | .lam b, c => by
      rw [shiftO, shift, ← shiftO_getD d b (c + 1)]
      cases shiftO d (c + 1) b <;> rfl
  | .case e a b, c => by
      rw [shiftO, shift, ← shiftO_getD d e c, ← shiftO_getD d a (c + 1),
        ← shiftO_getD d b (c + 1)]
      exact rebuild3_getD _ e a b _ _ _

/-- `Expr.shift`, keeping each subterm the shift leaves unchanged. -/
def Expr.shiftFast (d c : Nat) (e : Expr) : Expr := (shiftO d c e).getD e

@[csimp] theorem Expr.shift_eq_shiftFast : @Expr.shift = @Expr.shiftFast := by
  funext d c e
  exact (shiftO_getD d e c).symm

/-- `Expr.subst`, substituting a closed value without shifting it, and keeping each subterm the
substitution leaves unchanged. -/
def Expr.substFast (j : Nat) (s : Val) (e : Expr) : Expr :=
  if s.val.closedAt 0 then (substO j s.val e).getD e else e.subst j s

@[csimp] theorem Expr.subst_eq_substFast : @Expr.subst = @Expr.substFast := by
  funext j s e
  unfold Expr.substFast
  split
  · rw [substO_getD]; exact (Expr.substClosed_eq ‹_› e j).symm
  · rfl

end BoCa

namespace BoCa.Val

/-- Two values are equal when their expressions are: `Val` is a subset of
    `Expr`, so `IsVal` contributes nothing to the identity of a value. -/
theorem ext {v w : Val} (h : v.val = w.val) : v = w := Subtype.ext h

/-- The inclusion lands in `IsVal`, at the spelling `Expr.val v` rather than
    `v.val`, so that `h ▸ Val.isVal v` rewrites where a term was written with
    the inclusion. -/
theorem isVal (v : Val) : IsVal (Expr.val v) := v.2

end BoCa.Val

namespace BoCa

def load'  : Expr := .val (.prim .load)

def store' : Expr := .val (.prim .store)

def unit' : Expr := .val .unit

def v0 : Expr := .var 0

def v1 : Expr := .var 1

def v2 : Expr := .var 2

def v3 : Expr := .var 3

/-- `γ(e)` under `k` binders. -/
def Expr.psub (k : Nat) (γ : List Val) : Expr → Expr
  | .var i         =>
      if i < k then .var i
      else match γ[i - k]? with
           | some v => .val (v.shift k 0)
           | none   => .var (i - γ.length)
  | .unit          => .unit
  | .pair e₁ e₂    => .pair (Expr.psub k γ e₁) (Expr.psub k γ e₂)
  | .inj₁ e        => .inj₁ (Expr.psub k γ e)
  | .inj₂ e        => .inj₂ (Expr.psub k γ e)
  | .lam b         => .lam (Expr.psub (k + 1) γ b)
  | .loc ℓ         => .loc ℓ
  | .prim p        => .prim p
  | .seq e₁ e₂     => .seq (Expr.psub k γ e₁) (Expr.psub k γ e₂)
  | .letpair e₁ e₂ => .letpair (Expr.psub k γ e₁) (Expr.psub (k + 2) γ e₂)
  | .case e e₁ e₂  =>
      .case (Expr.psub k γ e) (Expr.psub (k + 1) γ e₁) (Expr.psub (k + 1) γ e₂)
  | .app f a       => .app (Expr.psub k γ f) (Expr.psub k γ a)

theorem Expr.shift_zero : ∀ (c : Nat) (e : Expr), Expr.shift 0 c e = e
  | _, .var _         => by
      simp only [Expr.shift]; split <;> simp_all
  | _, .unit          => rfl
  | c, .pair a b      => by
      simp only [Expr.shift, Expr.shift_zero c a, Expr.shift_zero c b]
  | c, .inj₁ a        => by simp only [Expr.shift, Expr.shift_zero c a]
  | c, .inj₂ a        => by simp only [Expr.shift, Expr.shift_zero c a]
  | c, .lam b         => by simp only [Expr.shift, Expr.shift_zero (c + 1) b]
  | _, .loc _         => rfl
  | _, .prim _        => rfl
  | c, .seq a b       => by
      simp only [Expr.shift, Expr.shift_zero c a, Expr.shift_zero c b]
  | c, .letpair a b   => by
      simp only [Expr.shift, Expr.shift_zero c a, Expr.shift_zero (c + 2) b]
  | c, .case a b₁ b₂  => by
      simp only [Expr.shift, Expr.shift_zero c a, Expr.shift_zero (c + 1) b₁,
        Expr.shift_zero (c + 1) b₂]
  | c, .app f a       => by
      simp only [Expr.shift, Expr.shift_zero c f, Expr.shift_zero c a]

theorem Val.shift_zero (c : Nat) (v : Val) : Val.shift 0 c v = v :=
  Val.ext (Expr.shift_zero c v.val)

theorem Expr.shift_shift : ∀ (a b c : Nat) (e : Expr),
    Expr.shift a c (Expr.shift b c e) = Expr.shift (a + b) c e
  | _, b, c, .var i        => by
      by_cases h : i < c
      · simp only [Expr.shift, if_pos h]
      · have h' : ¬ (i + b < c) := by omega
        simp only [Expr.shift, if_neg h, if_neg h']
        congr 1
        omega
  | _, _, _, .unit         => rfl
  | a, b, c, .pair p q     => by
      simp only [Expr.shift, Expr.shift_shift a b c p, Expr.shift_shift a b c q]
  | a, b, c, .inj₁ p       => by simp only [Expr.shift, Expr.shift_shift a b c p]
  | a, b, c, .inj₂ p       => by simp only [Expr.shift, Expr.shift_shift a b c p]
  | a, b, c, .lam e        => by simp only [Expr.shift, Expr.shift_shift a b (c + 1) e]
  | _, _, _, .loc _        => rfl
  | _, _, _, .prim _       => rfl
  | a, b, c, .seq p q      => by
      simp only [Expr.shift, Expr.shift_shift a b c p, Expr.shift_shift a b c q]
  | a, b, c, .letpair p q  => by
      simp only [Expr.shift, Expr.shift_shift a b c p, Expr.shift_shift a b (c + 2) q]
  | a, b, c, .case p q₁ q₂ => by
      simp only [Expr.shift, Expr.shift_shift a b c p, Expr.shift_shift a b (c + 1) q₁,
        Expr.shift_shift a b (c + 1) q₂]
  | a, b, c, .app f x      => by
      simp only [Expr.shift, Expr.shift_shift a b c f, Expr.shift_shift a b c x]

theorem Val.shift_shift (a b c : Nat) (v : Val) :
    Val.shift a c (Val.shift b c v) = Val.shift (a + b) c v :=
  Val.ext (Expr.shift_shift a b c v.val)

theorem Expr.subst_shift : ∀ (d c j : Nat) (s : Val) (e : Expr),
    c ≤ j → j ≤ c + d → Expr.subst j s (Expr.shift (d + 1) c e) = Expr.shift d c e
  | d, c, j, _, .var i,        _, _ => by
      simp only [Expr.shift]
      by_cases h : i < c
      · simp only [if_pos h, Expr.subst]
        have e₁ : ¬ (i = j) := by omega
        have e₂ : ¬ (i > j) := by omega
        simp only [if_neg e₁, if_neg e₂]
      · simp only [if_neg h, Expr.subst]
        have e₁ : ¬ (i + (d + 1) = j) := by omega
        have e₂ : i + (d + 1) > j := by omega
        have e₃ : i + (d + 1) - 1 = i + d := by omega
        simp only [if_neg e₁, if_pos e₂, e₃]
  | _, _, _, _, .unit,         _, _ => by simp only [Expr.shift, Expr.subst]
  | d, c, j, s, .pair p q,     h₁, h₂ => by
      simp only [Expr.shift, Expr.subst, Expr.subst_shift d c j s p h₁ h₂,
        Expr.subst_shift d c j s q h₁ h₂]
  | d, c, j, s, .inj₁ p,       h₁, h₂ => by
      simp only [Expr.shift, Expr.subst, Expr.subst_shift d c j s p h₁ h₂]
  | d, c, j, s, .inj₂ p,       h₁, h₂ => by
      simp only [Expr.shift, Expr.subst, Expr.subst_shift d c j s p h₁ h₂]
  | d, c, j, s, .lam e,        h₁, h₂ => by
      simp only [Expr.shift, Expr.subst,
        Expr.subst_shift d (c + 1) (j + 1) (s.shift 1 0) e (by omega) (by omega)]
  | _, _, _, _, .loc _,        _, _ => by simp only [Expr.shift, Expr.subst]
  | _, _, _, _, .prim _,       _, _ => by simp only [Expr.shift, Expr.subst]
  | d, c, j, s, .seq p q,      h₁, h₂ => by
      simp only [Expr.shift, Expr.subst, Expr.subst_shift d c j s p h₁ h₂,
        Expr.subst_shift d c j s q h₁ h₂]
  | d, c, j, s, .letpair p q,  h₁, h₂ => by
      simp only [Expr.shift, Expr.subst, Expr.subst_shift d c j s p h₁ h₂,
        Expr.subst_shift d (c + 2) (j + 2) (s.shift 2 0) q (by omega) (by omega)]
  | d, c, j, s, .case p q₁ q₂, h₁, h₂ => by
      simp only [Expr.shift, Expr.subst, Expr.subst_shift d c j s p h₁ h₂,
        Expr.subst_shift d (c + 1) (j + 1) (s.shift 1 0) q₁ (by omega) (by omega),
        Expr.subst_shift d (c + 1) (j + 1) (s.shift 1 0) q₂ (by omega) (by omega)]
  | d, c, j, s, .app f x,      h₁, h₂ => by
      simp only [Expr.shift, Expr.subst, Expr.subst_shift d c j s f h₁ h₂,
        Expr.subst_shift d c j s x h₁ h₂]

theorem Expr.psub_cons : ∀ (k : Nat) (v : Val) (γ : List Val) (e : Expr),
    Expr.psub k (v :: γ) e = Expr.subst k (v.shift k 0) (Expr.psub (k + 1) γ e)
  | k, v, γ, .var i => by
      by_cases h : i < k
      · have h' : i < k + 1 := by omega
        have e₁ : ¬ (i = k) := by omega
        have e₂ : ¬ (i > k) := by omega
        simp only [Expr.psub, if_pos h, if_pos h', Expr.subst, if_neg e₁, if_neg e₂]
      · obtain ⟨m, rfl⟩ : ∃ m, i = k + m := ⟨i - k, by omega⟩
        cases m with
        | zero =>
            simp only [Expr.psub, Nat.add_zero, Nat.sub_self,
              List.getElem?_cons_zero, if_pos (by omega : k < k + 1), Expr.subst]
            simp
        | succ m =>
            have hk : ¬ (k + (m + 1) < k) := by omega
            have hk' : ¬ (k + (m + 1) < k + 1) := by omega
            have ea : k + (m + 1) - k = m + 1 := by omega
            have eb : k + (m + 1) - (k + 1) = m := by omega
            cases hm : γ[m]? with
            | some w =>
                simp only [Expr.psub, if_neg hk, ea, List.getElem?_cons_succ, hm,
                  if_neg hk', eb]
                exact (Expr.subst_shift k 0 k (v.shift k 0) w.val
                  (by omega) (by omega)).symm
            | none =>
                have hlen : γ.length ≤ m := List.getElem?_eq_none_iff.mp hm
                have e₁ : ¬ (k + (m + 1) - γ.length = k) := by omega
                have e₂ : k + (m + 1) - γ.length > k := by omega
                have e₃ : k + (m + 1) - γ.length - 1 = k + (m + 1) - (γ.length + 1) := by
                  omega
                simp only [Expr.psub, if_neg hk, ea, List.getElem?_cons_succ, hm,
                  if_neg hk', eb, Expr.subst, List.length_cons, if_neg e₁, if_pos e₂, e₃]
  | _, _, _, .unit => by simp only [Expr.psub, Expr.subst]
  | k, v, γ, .pair p q => by
      simp only [Expr.psub, Expr.subst, Expr.psub_cons k v γ p, Expr.psub_cons k v γ q]
  | k, v, γ, .inj₁ p => by
      simp only [Expr.psub, Expr.subst, Expr.psub_cons k v γ p]
  | k, v, γ, .inj₂ p => by
      simp only [Expr.psub, Expr.subst, Expr.psub_cons k v γ p]
  | k, v, γ, .lam b => by
      have hs : Val.shift 1 0 (Val.shift k 0 v) = Val.shift (k + 1) 0 v := by
        rw [Val.shift_shift]; congr 1; omega
      simp only [Expr.psub, Expr.subst, Expr.psub_cons (k + 1) v γ b, hs]
  | _, _, _, .loc _ => by simp only [Expr.psub, Expr.subst]
  | _, _, _, .prim _ => by simp only [Expr.psub, Expr.subst]
  | k, v, γ, .seq p q => by
      simp only [Expr.psub, Expr.subst, Expr.psub_cons k v γ p, Expr.psub_cons k v γ q]
  | k, v, γ, .letpair p q => by
      have hs : Val.shift 2 0 (Val.shift k 0 v) = Val.shift (k + 2) 0 v := by
        rw [Val.shift_shift]; congr 1; omega
      simp only [Expr.psub, Expr.subst, Expr.psub_cons k v γ p,
        Expr.psub_cons (k + 2) v γ q, hs]
  | k, v, γ, .case p q₁ q₂ => by
      have hs : Val.shift 1 0 (Val.shift k 0 v) = Val.shift (k + 1) 0 v := by
        rw [Val.shift_shift]; congr 1; omega
      simp only [Expr.psub, Expr.subst, Expr.psub_cons k v γ p,
        Expr.psub_cons (k + 1) v γ q₁, Expr.psub_cons (k + 1) v γ q₂, hs]
  | k, v, γ, .app f x => by
      simp only [Expr.psub, Expr.subst, Expr.psub_cons k v γ f, Expr.psub_cons k v γ x]

theorem Expr.psub_cons₂ : ∀ (k : Nat) (v₂ v₁ : Val) (γ : List Val) (e : Expr),
    Expr.psub k (v₂ :: v₁ :: γ) e =
      Expr.subst k (v₁.shift k 0)
        (Expr.subst k (v₂.shift (k + 1) 0) (Expr.psub (k + 2) γ e))
  | k, v₂, v₁, γ, .var i => by
      by_cases h : i < k
      · have h' : i < k + 2 := by omega
        have e₁ : ¬ (i = k) := by omega
        have e₂ : ¬ (i > k) := by omega
        simp only [Expr.psub, if_pos h, if_pos h', Expr.subst, if_neg e₁, if_neg e₂]
      · obtain ⟨m, rfl⟩ : ∃ m, i = k + m := ⟨i - k, by omega⟩
        match m with
        | 0 =>
            simp only [Expr.psub, Nat.add_zero, Nat.sub_self,
              List.getElem?_cons_zero, if_pos (by omega : k < k + 2), Expr.subst]
            simp only [Nat.lt_irrefl, if_false, if_true]
            exact (Expr.subst_shift k 0 k (v₁.shift k 0) v₂.val
              (by omega) (by omega)).symm
        | 1 =>
            have hk : ¬ (k + 1 < k) := by omega
            have ea : k + 1 - k = 1 := by omega
            have e₁ : ¬ (k + 1 = k) := by omega
            have e₂ : k + 1 > k := by omega
            simp only [Expr.psub, if_neg hk, ea, List.getElem?_cons_succ,
              List.getElem?_cons_zero, if_pos (by omega : k + 1 < k + 2), Expr.subst,
              if_neg e₁, if_pos e₂, Nat.add_sub_cancel, Nat.lt_irrefl, if_false,
              if_true]
        | (m + 2) =>
            have hk : ¬ (k + (m + 2) < k) := by omega
            have hk' : ¬ (k + (m + 2) < k + 2) := by omega
            have ea : k + (m + 2) - k = m + 2 := by omega
            have eb : k + (m + 2) - (k + 2) = m := by omega
            cases hm : γ[m]? with
            | some w =>
                have s₁ : Expr.subst k (v₂.shift (k + 1) 0) (Expr.shift (k + 2) 0 w.val)
                    = Expr.shift (k + 1) 0 w.val :=
                  Expr.subst_shift (k + 1) 0 k (v₂.shift (k + 1) 0) w.val
                    (by omega) (by omega)
                have s₂ : Expr.subst k (v₁.shift k 0) (Expr.shift (k + 1) 0 w.val)
                    = Expr.shift k 0 w.val :=
                  Expr.subst_shift k 0 k (v₁.shift k 0) w.val (by omega) (by omega)
                simp only [Expr.psub, if_neg hk, ea, List.getElem?_cons_succ, hm,
                  if_neg hk', eb, Val.val_shift, s₁, s₂]
            | none =>
                have hlen : γ.length ≤ m := List.getElem?_eq_none_iff.mp hm
                have e₁ : ¬ (k + (m + 2) - γ.length = k) := by omega
                have e₂ : k + (m + 2) - γ.length > k := by omega
                have e₃ : k + (m + 2) - γ.length - 1 = k + (m + 2) - (γ.length + 1) := by
                  omega
                have f₁ : ¬ (k + (m + 2) - (γ.length + 1) = k) := by omega
                have f₂ : k + (m + 2) - (γ.length + 1) > k := by omega
                have f₃ : k + (m + 2) - (γ.length + 1) - 1
                    = k + (m + 2) - (γ.length + 1 + 1) := by omega
                simp only [Expr.psub, if_neg hk, ea, List.getElem?_cons_succ, hm,
                  if_neg hk', eb, Expr.subst, List.length_cons, if_neg e₁, if_pos e₂,
                  e₃, if_neg f₁, if_pos f₂, f₃]
  | _, _, _, _, .unit => by simp only [Expr.psub, Expr.subst]
  | k, v₂, v₁, γ, .pair p q => by
      simp only [Expr.psub, Expr.subst, Expr.psub_cons₂ k v₂ v₁ γ p,
        Expr.psub_cons₂ k v₂ v₁ γ q]
  | k, v₂, v₁, γ, .inj₁ p => by
      simp only [Expr.psub, Expr.subst, Expr.psub_cons₂ k v₂ v₁ γ p]
  | k, v₂, v₁, γ, .inj₂ p => by
      simp only [Expr.psub, Expr.subst, Expr.psub_cons₂ k v₂ v₁ γ p]
  | k, v₂, v₁, γ, .lam b => by
      have h₁ : Val.shift 1 0 (Val.shift k 0 v₁) = Val.shift (k + 1) 0 v₁ := by
        rw [Val.shift_shift]; congr 1; omega
      have h₂ : Val.shift 1 0 (Val.shift (k + 1) 0 v₂) = Val.shift (k + 1 + 1) 0 v₂ := by
        rw [Val.shift_shift]; congr 1; omega
      simp only [Expr.psub, Expr.subst, Expr.psub_cons₂ (k + 1) v₂ v₁ γ b, h₁, h₂]
  | _, _, _, _, .loc _ => by simp only [Expr.psub, Expr.subst]
  | _, _, _, _, .prim _ => by simp only [Expr.psub, Expr.subst]
  | k, v₂, v₁, γ, .seq p q => by
      simp only [Expr.psub, Expr.subst, Expr.psub_cons₂ k v₂ v₁ γ p,
        Expr.psub_cons₂ k v₂ v₁ γ q]
  | k, v₂, v₁, γ, .letpair p q => by
      have h₁ : Val.shift 2 0 (Val.shift k 0 v₁) = Val.shift (k + 2) 0 v₁ := by
        rw [Val.shift_shift]; congr 1; omega
      have h₂ : Val.shift 2 0 (Val.shift (k + 1) 0 v₂) = Val.shift (k + 2 + 1) 0 v₂ := by
        rw [Val.shift_shift]; congr 1; omega
      simp only [Expr.psub, Expr.subst, Expr.psub_cons₂ k v₂ v₁ γ p,
        Expr.psub_cons₂ (k + 2) v₂ v₁ γ q, h₁, h₂]
  | k, v₂, v₁, γ, .case p q₁ q₂ => by
      have h₁ : Val.shift 1 0 (Val.shift k 0 v₁) = Val.shift (k + 1) 0 v₁ := by
        rw [Val.shift_shift]; congr 1; omega
      have h₂ : Val.shift 1 0 (Val.shift (k + 1) 0 v₂) = Val.shift (k + 1 + 1) 0 v₂ := by
        rw [Val.shift_shift]; congr 1; omega
      simp only [Expr.psub, Expr.subst, Expr.psub_cons₂ k v₂ v₁ γ p,
        Expr.psub_cons₂ (k + 1) v₂ v₁ γ q₁, Expr.psub_cons₂ (k + 1) v₂ v₁ γ q₂, h₁, h₂]
  | k, v₂, v₁, γ, .app f x => by
      simp only [Expr.psub, Expr.subst, Expr.psub_cons₂ k v₂ v₁ γ f,
        Expr.psub_cons₂ k v₂ v₁ γ x]

end BoCa

end
