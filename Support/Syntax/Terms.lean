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
