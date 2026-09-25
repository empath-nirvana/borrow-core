import LeafPlaces.Layout

/-!
# The struct operations, as terms

Each operation is a closed term of the language, defined by recursion on the shape:

    allocS (leaf T)     ≜ alloc
    allocS (node s₁ s₂) ≜ λv. let (v₁, v₂) = v; (allocS s₁ v₁, allocS s₂ v₂)
    freeS               — the same with free
    withborS (leaf T)   ≜ withbor
    withborS (node s₁ s₂) ≜ λp. λg. let (x, y) = p;
                  let (x′, r) = withborS s₁ x (Λ. λmx.
                                  let (y′, t) = withborS s₂ y (Λ. λmy. g () (⇓s₁ mx, my));
                                  (y′, t));
                  let (y′, t) = r; ((x′, y′), t)

`⇓σ e` (`shortenE`) rebuilds a family leaf by leaf.  At run time it is the identity on the
tuple; its typing applies `⊑Mut`/`⊑Imm` at every leaf, which moves the outer family from the
outer lifetime to the inner one.  `withborS` at `node (leaf A) (leaf B)` is
`Places.withbor2` with `⇓` in place of the leaf's `⊑`.

`clAt n e`: every free variable of `e` is below `n`.  Closed terms are fixed by substitution
and shifting, and `Records.occ` finds no variable in them.
-/

noncomputable section

namespace BoCa.LeafPlaces
open BoCa BoCa.Lifetime BoCa.Programs

/-! ## Closed terms -/

/-- Every free de Bruijn index of the term is below `n`. -/
def clAt : Nat → Expr → Bool
  | n, .var i => decide (i < n)
  | _, .unit => true
  | n, .pair a b => clAt n a && clAt n b
  | n, .inj₁ a => clAt n a
  | n, .inj₂ a => clAt n a
  | n, .lam b => clAt (n + 1) b
  | _, .loc _ => true
  | _, .prim _ => true
  | n, .seq a b => clAt n a && clAt n b
  | n, .letpair a b => clAt n a && clAt (n + 2) b
  | n, .case a b c => clAt n a && clAt (n + 1) b && clAt (n + 1) c
  | n, .app a b => clAt n a && clAt n b

theorem subst_clAt : ∀ (e : Expr) {n j : Nat} (s : Val), clAt n e = true → n ≤ j →
    e.subst j s = e
  | .var i, n, j, s, h, hj => by
      simp only [clAt, decide_eq_true_eq] at h
      have e₁ : ¬ i = j := by omega
      have e₂ : ¬ i > j := by omega
      simp [Expr.subst, e₁, e₂]
  | .unit, _, _, _, _, _ => rfl
  | .pair a b, _, _, s, h, hj => by
      simp only [clAt, Bool.and_eq_true] at h
      simp [Expr.subst, subst_clAt a s h.1 hj, subst_clAt b s h.2 hj]
  | .inj₁ a, _, _, s, h, hj => by simp only [clAt] at h; simp [Expr.subst, subst_clAt a s h hj]
  | .inj₂ a, _, _, s, h, hj => by simp only [clAt] at h; simp [Expr.subst, subst_clAt a s h hj]
  | .lam b, n, j, s, h, hj => by
      simp only [clAt] at h; simp [Expr.subst, subst_clAt b (n := n + 1) (j := j + 1) _ h (by omega)]
  | .loc _, _, _, _, _, _ => rfl
  | .prim _, _, _, _, _, _ => rfl
  | .seq a b, _, _, s, h, hj => by
      simp only [clAt, Bool.and_eq_true] at h
      simp [Expr.subst, subst_clAt a s h.1 hj, subst_clAt b s h.2 hj]
  | .letpair a b, n, j, s, h, hj => by
      simp only [clAt, Bool.and_eq_true] at h
      simp [Expr.subst, subst_clAt a s h.1 hj, subst_clAt b (n := n + 2) (j := j + 2) _ h.2 (by omega)]
  | .case a b c, n, j, s, h, hj => by
      simp only [clAt, Bool.and_eq_true] at h
      simp [Expr.subst, subst_clAt a s h.1.1 hj,
        subst_clAt b (n := n + 1) (j := j + 1) _ h.1.2 (by omega),
        subst_clAt c (n := n + 1) (j := j + 1) _ h.2 (by omega)]
  | .app a b, _, _, s, h, hj => by
      simp only [clAt, Bool.and_eq_true] at h
      simp [Expr.subst, subst_clAt a s h.1 hj, subst_clAt b s h.2 hj]

theorem shift_clAt : ∀ (e : Expr) {n c : Nat} (d : Nat), clAt n e = true → n ≤ c →
    e.shift d c = e
  | .var i, n, c, d, h, hc => by
      simp only [clAt, decide_eq_true_eq] at h
      have e₁ : i < c := by omega
      simp [Expr.shift, e₁]
  | .unit, _, _, _, _, _ => rfl
  | .pair a b, _, _, d, h, hc => by
      simp only [clAt, Bool.and_eq_true] at h
      simp [Expr.shift, shift_clAt a d h.1 hc, shift_clAt b d h.2 hc]
  | .inj₁ a, _, _, d, h, hc => by simp only [clAt] at h; simp [Expr.shift, shift_clAt a d h hc]
  | .inj₂ a, _, _, d, h, hc => by simp only [clAt] at h; simp [Expr.shift, shift_clAt a d h hc]
  | .lam b, n, c, d, h, hc => by
      simp only [clAt] at h; simp [Expr.shift, shift_clAt b (n := n + 1) (c := c + 1) d h (by omega)]
  | .loc _, _, _, _, _, _ => rfl
  | .prim _, _, _, _, _, _ => rfl
  | .seq a b, _, _, d, h, hc => by
      simp only [clAt, Bool.and_eq_true] at h
      simp [Expr.shift, shift_clAt a d h.1 hc, shift_clAt b d h.2 hc]
  | .letpair a b, n, c, d, h, hc => by
      simp only [clAt, Bool.and_eq_true] at h
      simp [Expr.shift, shift_clAt a d h.1 hc, shift_clAt b (n := n + 2) (c := c + 2) d h.2 (by omega)]
  | .case a b c, n, c', d, h, hc => by
      simp only [clAt, Bool.and_eq_true] at h
      simp [Expr.shift, shift_clAt a d h.1.1 hc,
        shift_clAt b (n := n + 1) (c := c' + 1) d h.1.2 (by omega),
        shift_clAt c (n := n + 1) (c := c' + 1) d h.2 (by omega)]
  | .app a b, _, _, d, h, hc => by
      simp only [clAt, Bool.and_eq_true] at h
      simp [Expr.shift, shift_clAt a d h.1 hc, shift_clAt b d h.2 hc]

theorem occ_clAt : ∀ (e : Expr) {n i : Nat}, clAt n e = true → n ≤ i → Records.occ i e = false
  | .var j, n, i, h, hi => by
      simp only [clAt, decide_eq_true_eq] at h
      simp only [Records.occ, beq_eq_false_iff_ne]; omega
  | .unit, _, _, _, _ => rfl
  | .pair a b, _, _, h, hi => by
      simp only [clAt, Bool.and_eq_true] at h
      simp [Records.occ, occ_clAt a h.1 hi, occ_clAt b h.2 hi]
  | .inj₁ a, _, _, h, hi => by simp only [clAt] at h; simp [Records.occ, occ_clAt a h hi]
  | .inj₂ a, _, _, h, hi => by simp only [clAt] at h; simp [Records.occ, occ_clAt a h hi]
  | .lam b, n, i, h, hi => by
      simp only [clAt] at h; simp [Records.occ, occ_clAt b (n := n + 1) (i := i + 1) h (by omega)]
  | .loc _, _, _, _, _ => rfl
  | .prim _, _, _, _, _ => rfl
  | .seq a b, _, _, h, hi => by
      simp only [clAt, Bool.and_eq_true] at h
      simp [Records.occ, occ_clAt a h.1 hi, occ_clAt b h.2 hi]
  | .letpair a b, n, i, h, hi => by
      simp only [clAt, Bool.and_eq_true] at h
      simp [Records.occ, occ_clAt a h.1 hi, occ_clAt b (n := n + 2) (i := i + 2) h.2 (by omega)]
  | .case a b c, n, i, h, hi => by
      simp only [clAt, Bool.and_eq_true] at h
      simp [Records.occ, occ_clAt a h.1.1 hi, occ_clAt b (n := n + 1) (i := i + 1) h.1.2 (by omega),
        occ_clAt c (n := n + 1) (i := i + 1) h.2 (by omega)]
  | .app a b, _, _, h, hi => by
      simp only [clAt, Bool.and_eq_true] at h
      simp [Records.occ, occ_clAt a h.1 hi, occ_clAt b h.2 hi]

theorem clAt_mono : ∀ (e : Expr) {n m : Nat}, clAt n e = true → n ≤ m → clAt m e = true
  | .var j, n, m, h, hm => by
      simp only [clAt, decide_eq_true_eq] at h ⊢; omega
  | .unit, _, _, _, _ => rfl
  | .pair a b, _, _, h, hm => by
      simp only [clAt, Bool.and_eq_true] at h ⊢; exact ⟨clAt_mono a h.1 hm, clAt_mono b h.2 hm⟩
  | .inj₁ a, _, _, h, hm => by simp only [clAt] at h ⊢; exact clAt_mono a h hm
  | .inj₂ a, _, _, h, hm => by simp only [clAt] at h ⊢; exact clAt_mono a h hm
  | .lam b, n, m, h, hm => by
      simp only [clAt] at h ⊢; exact clAt_mono b (n := n + 1) (m := m + 1) h (by omega)
  | .loc _, _, _, _, _ => rfl
  | .prim _, _, _, _, _ => rfl
  | .seq a b, _, _, h, hm => by
      simp only [clAt, Bool.and_eq_true] at h ⊢; exact ⟨clAt_mono a h.1 hm, clAt_mono b h.2 hm⟩
  | .letpair a b, n, m, h, hm => by
      simp only [clAt, Bool.and_eq_true] at h ⊢
      exact ⟨clAt_mono a h.1 hm, clAt_mono b (n := n + 2) (m := m + 2) h.2 (by omega)⟩
  | .case a b c, n, m, h, hm => by
      simp only [clAt, Bool.and_eq_true] at h ⊢
      exact ⟨⟨clAt_mono a h.1.1 hm, clAt_mono b (n := n + 1) (m := m + 1) h.1.2 (by omega)⟩,
        clAt_mono c (n := n + 1) (m := m + 1) h.2 (by omega)⟩
  | .app a b, _, _, h, hm => by
      simp only [clAt, Bool.and_eq_true] at h ⊢; exact ⟨clAt_mono a h.1 hm, clAt_mono b h.2 hm⟩

/-- A closed value is fixed by shifting. -/
theorem Val.shift_cl {v : Val} (h : clAt 0 v.1 = true) (d c : Nat) : v.shift d c = v :=
  Val.ext (shift_clAt v.1 d h (Nat.zero_le c))

/-! ## The operations -/

/-- Allocate a struct: one `alloc` per leaf, in order. -/
def allocS : Shape → Expr
  | .leaf _ => alloc'
  | .node s₁ s₂ => lam (.letpair (.var 0) (.pair (.app (allocS s₁) (.var 1)) (.app (allocS s₂) (.var 0))))

/-- Free a struct: one `free` per leaf, returning the values in the shape of the tree. -/
def freeS : Shape → Expr
  | .leaf _ => free'
  | .node s₁ s₂ => lam (.letpair (.var 0) (.pair (.app (freeS s₁) (.var 1)) (.app (freeS s₂) (.var 0))))

/-- `⇓σ e`: the family `e`, rebuilt leaf by leaf. -/
def shortenE : Shape → Expr → Expr
  | .leaf _, e => e
  | .node s₁ s₂, e => .letpair e (.pair (shortenE s₁ (.var 1)) (shortenE s₂ (.var 0)))

/-- Borrow a struct: every leaf, the family handed to the callback at one lifetime. -/
def withborS : Shape → Expr
  | .leaf _ => withbor
  | .node s₁ s₂ =>
      lam2 (.letpair (.var 1)
        (.letpair (app2 (withborS s₁) (.var 1)
            (lam (lam (.letpair (app2 (withborS s₂) (.var 2)
                (lam (lam (app2 (.var 6) unit' (.pair (shortenE s₁ (.var 2)) (.var 0))))))
              (.pair (.var 1) (.var 0))))))
          (.letpair (.var 0) (.pair (.pair (.var 3) (.var 1)) (.var 0)))))

/-- The inner callback of `withborS (node s₁ s₂)`: `Λ. λmy. g () (⇓s₁ mx, my)`, `mx` at 2 and
`g` at 6. -/
def innerS (s₁ : Shape) : Expr := lam (lam (app2 (.var 6) unit' (.pair (shortenE s₁ (.var 2)) (.var 0))))

/-- The outer callback: `Λ. λmx. let (y′, t) = withborS s₂ y innerS; (y′, t)`, `y` at 2. -/
def outerS (s₁ s₂ : Shape) : Expr :=
  lam (lam (.letpair (app2 (withborS s₂) (.var 2) (innerS s₁)) (.pair (.var 1) (.var 0))))

theorem withborS_node (s₁ s₂ : Shape) :
    withborS (.node s₁ s₂) =
      lam2 (.letpair (.var 1)
        (.letpair (app2 (withborS s₁) (.var 1) (outerS s₁ s₂))
          (.letpair (.var 0) (.pair (.pair (.var 3) (.var 1)) (.var 0))))) := rfl

/-! ## Closedness -/

theorem clAt_shortenE : ∀ (σ : Shape) {n : Nat} {e : Expr}, clAt n e = true →
    clAt n (shortenE σ e) = true
  | .leaf _, _, _, h => h
  | .node s₁ s₂, n, e, h => by
      simp only [shortenE, clAt, Bool.and_eq_true]
      exact ⟨h, clAt_shortenE s₁ (by simp [clAt]), clAt_shortenE s₂ (by simp [clAt])⟩

theorem clAt_allocS : ∀ σ : Shape, clAt 0 (allocS σ) = true
  | .leaf _ => rfl
  | .node s₁ s₂ => by
      simp only [allocS, lam, Val.lam, clAt, Bool.and_eq_true]
      exact ⟨rfl, ⟨clAt_mono _ (clAt_allocS s₁) (by omega), rfl⟩,
        clAt_mono _ (clAt_allocS s₂) (by omega), rfl⟩

theorem clAt_freeS : ∀ σ : Shape, clAt 0 (freeS σ) = true
  | .leaf _ => rfl
  | .node s₁ s₂ => by
      simp only [freeS, lam, Val.lam, clAt, Bool.and_eq_true]
      exact ⟨rfl, ⟨clAt_mono _ (clAt_freeS s₁) (by omega), rfl⟩,
        clAt_mono _ (clAt_freeS s₂) (by omega), rfl⟩

theorem clAt_withborS : ∀ σ : Shape, clAt 0 (withborS σ) = true
  | .leaf _ => rfl
  | .node s₁ s₂ => by
      have h₁ : ∀ n, clAt n (withborS s₁) = true := fun n => clAt_mono _ (clAt_withborS s₁) (Nat.zero_le n)
      have h₂ : ∀ n, clAt n (withborS s₂) = true := fun n => clAt_mono _ (clAt_withborS s₂) (Nat.zero_le n)
      have h₃ : clAt 8 (shortenE s₁ (.var 2)) = true := clAt_shortenE s₁ (by simp [clAt])
      simp [withborS, lam2, lam, app2, Val.lam, unit', Val.unit, clAt, h₁, h₂, h₃]

/-- `allocS σ`, `freeS σ` and `withborS σ` as values. -/
def allocV (σ : Shape) : Val :=
  match σ with
  | .leaf _ => .prim .alloc
  | .node s₁ s₂ => .lam (.letpair (.var 0) (.pair (.app (allocS s₁) (.var 1)) (.app (allocS s₂) (.var 0))))

theorem allocV_val (σ : Shape) : (allocV σ).1 = allocS σ := by cases σ <;> rfl

def freeV (σ : Shape) : Val :=
  match σ with
  | .leaf _ => .prim .free
  | .node s₁ s₂ => .lam (.letpair (.var 0) (.pair (.app (freeS s₁) (.var 1)) (.app (freeS s₂) (.var 0))))

theorem freeV_val (σ : Shape) : (freeV σ).1 = freeS σ := by cases σ <;> rfl

theorem isVal_withborS : ∀ σ : Shape, IsVal (withborS σ)
  | .leaf _ => .lam
  | .node _ _ => .lam

def withborV (σ : Shape) : Val := ⟨withborS σ, isVal_withborS σ⟩

theorem clAt_addr : ∀ (σ : Shape) (b : Loc), clAt 0 (σ.addr b).1 = true
  | .leaf _, _ => rfl
  | .node s₁ s₂, b => by
      simp only [Shape.addr, Val.pair, clAt, Bool.and_eq_true]
      exact ⟨clAt_addr s₁ b, clAt_addr s₂ _⟩

end BoCa.LeafPlaces

end
