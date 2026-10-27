import Lowering.Rename

/-!
# Lowering — the low subset under composition and renaming  `[spec §54]`

The facts `Lowering/OwnLow.lean` builds `own`'s low output from:

- **how uses compose** (`ZeroU`, `once`): a variable unused by one part and used once by the other
  is used once by the sequence (`seqO_one_zero`, `seqO_zero_one`), two arms that each use it once
  use it once (`joinO_one`), and a path that ends keeps it (`seqO_halt_one`);
- **an unmentioned variable is unused** (`zeroU_of_not_mentions`);
- **an injective renaming moves uses with the variables** (`mentions_ren`, `occ_ren`,
  `mentions_ren_out`) and keeps explicit ownership (`ExplicitC.ren`): `ExplicitC` is `Explicit`
  with each constant closed, as every constant `own` writes is.
-/

namespace Lowering
open BoCa
open BoCa.Fig16.LogRel.Core (closedAt)

/-! ### Uses -/

/-- `a`, then `b`: `occ`'s sequence. -/
def seqO (a b : Option Uses) : Option Uses := do pure ((← a).andThen (← b))

/-- Two arms: `occ`'s join. -/
def joinO (a b : Option Uses) : Option Uses := do Uses.join (← a) (← b)

/-- The variable is unused on every path. -/
def ZeroU (u : Option Uses) : Prop :=
  ∃ r s, u = some ⟨r, s⟩ ∧ (r = some 0 ∨ r = none) ∧ (s = none ∨ s = some 0)

theorem once_iff {u : Option Uses} : once u = true ↔
    ∃ r s, u = some ⟨r, s⟩ ∧ (r = some 1 ∨ r = none) ∧ (s = none ∨ ∃ k, s = some k ∧ k ≤ 1) := by
  rcases u with _ | ⟨r, s⟩
  · simp [once]
  · rcases s with _ | k <;> simp [once]

theorem zeroU_iff {u : Option Uses} : ZeroU u ↔
    ∃ r s, u = some ⟨r, s⟩ ∧ (r = some 0 ∨ r = none) ∧ (s = none ∨ s = some 0) := Iff.rfl

theorem seqO_zero_zero {a b : Option Uses} (ha : ZeroU a) (hb : ZeroU b) : ZeroU (seqO a b) := by
  obtain ⟨r₁, s₁, rfl, hr₁, hs₁⟩ := ha
  obtain ⟨r₂, s₂, rfl, hr₂, hs₂⟩ := hb
  rcases hr₁ with rfl | rfl <;> rcases hr₂ with rfl | rfl <;> rcases hs₁ with rfl | rfl <;>
    rcases hs₂ with rfl | rfl <;> simp [seqO, Uses.andThen, maxO, ZeroU]

theorem seqO_one_zero {a b : Option Uses} (ha : once a = true) (hb : ZeroU b) :
    once (seqO a b) = true := by
  obtain ⟨r₁, s₁, rfl, hr₁, hs₁⟩ := once_iff.mp ha
  obtain ⟨r₂, s₂, rfl, hr₂, hs₂⟩ := hb
  rcases hs₁ with rfl | ⟨k, rfl, hk⟩ <;> rcases hr₁ with rfl | rfl <;> rcases hr₂ with rfl | rfl <;>
    rcases hs₂ with rfl | rfl <;> simp [seqO, Uses.andThen, maxO, once] <;> omega

theorem seqO_zero_one {a b : Option Uses} (ha : ZeroU a) (hb : once b = true) :
    once (seqO a b) = true := by
  obtain ⟨r₁, s₁, rfl, hr₁, hs₁⟩ := ha
  obtain ⟨r₂, s₂, rfl, hr₂, hs₂⟩ := once_iff.mp hb
  rcases hs₂ with rfl | ⟨k, rfl, hk⟩ <;> rcases hr₁ with rfl | rfl <;> rcases hr₂ with rfl | rfl <;>
    rcases hs₁ with rfl | rfl <;> simp [seqO, Uses.andThen, maxO, once] <;> omega

theorem joinO_zero {a b : Option Uses} (ha : ZeroU a) (hb : ZeroU b) : ZeroU (joinO a b) := by
  obtain ⟨r₁, s₁, rfl, hr₁, hs₁⟩ := ha
  obtain ⟨r₂, s₂, rfl, hr₂, hs₂⟩ := hb
  rcases hr₁ with rfl | rfl <;> rcases hr₂ with rfl | rfl <;> rcases hs₁ with rfl | rfl <;>
    rcases hs₂ with rfl | rfl <;> simp [joinO, Uses.join, maxO, ZeroU]

theorem joinO_one {a b : Option Uses} (ha : once a = true) (hb : once b = true) :
    once (joinO a b) = true := by
  obtain ⟨r₁, s₁, rfl, hr₁, hs₁⟩ := once_iff.mp ha
  obtain ⟨r₂, s₂, rfl, hr₂, hs₂⟩ := once_iff.mp hb
  rcases hs₁ with rfl | ⟨k, rfl, hk⟩ <;> rcases hs₂ with rfl | ⟨k', rfl, hk'⟩ <;>
    rcases hr₁ with rfl | rfl <;> rcases hr₂ with rfl | rfl <;>
    simp [joinO, Uses.join, maxO, once] <;> omega

theorem seqO_halt_zero {a : Option Uses} (ha : ZeroU a) : ZeroU (seqO a (some .halt)) := by
  obtain ⟨r, s, rfl, hr, hs⟩ := ha
  rcases hr with rfl | rfl <;> rcases hs with rfl | rfl <;>
    simp [seqO, Uses.andThen, Uses.halt, maxO, ZeroU]

theorem seqO_halt_one {a : Option Uses} (ha : once a = true) :
    once (seqO a (some .halt)) = true := by
  obtain ⟨r, s, rfl, hr, hs⟩ := once_iff.mp ha
  rcases hs with rfl | ⟨k, rfl, hk⟩ <;> rcases hr with rfl | rfl <;>
    simp [seqO, Uses.andThen, Uses.halt, maxO, once] <;> omega

theorem zeroU_zero : ZeroU (some Uses.zero) := ⟨some 0, none, rfl, .inl rfl, .inl rfl⟩

theorem once_one : once (some Uses.one) = true := rfl

/-! ### `occ` at each former -/

theorem occ_var (j i : Nat) : occ (.var j) i = some (if j = i then .one else .zero) := rfl
theorem occ_pair (a b : Expr) (i : Nat) : occ (.pair a b) i = seqO (occ a i) (occ b i) := rfl
theorem occ_seq (a b : Expr) (i : Nat) : occ (.seq a b) i = seqO (occ a i) (occ b i) := rfl
theorem occ_app (f a : Expr) (i : Nat) : occ (.app f a) i = seqO (occ a i) (occ f i) := rfl
theorem occ_inj₁ (a : Expr) (i : Nat) : occ (.inj₁ a) i = occ a i := rfl
theorem occ_inj₂ (a : Expr) (i : Nat) : occ (.inj₂ a) i = occ a i := rfl
theorem occ_lam (b : Expr) (i : Nat) :
    occ (.lam b) i = some ⟨some (if mentions b (i + 1) then 1 else 0), none⟩ := rfl
theorem occ_letpair (a b : Expr) (i : Nat) :
    occ (.letpair a b) i = seqO (occ a i) (occ b (i + 2)) := rfl
theorem occ_case (s a b : Expr) (i : Nat) :
    occ (.case s a b) i = if a = BoLo.stuckE ∧ b = BoLo.stuckE then seqO (occ s i) (some .halt)
      else seqO (occ s i) (joinO (occ a (i + 1)) (occ b (i + 1))) := by
  simp only [occ, seqO, joinO]
  split
  · rfl
  · cases occ s i <;> cases occ a (i + 1) <;> cases occ b (i + 1) <;> rfl

theorem occ_absurdL (s : Expr) (i : Nat) : occ (absurdL s) i = seqO (occ s i) (some .halt) := by
  rw [absurdL, occ_case, if_pos ⟨rfl, rfl⟩]

/-- **An unmentioned variable is unused.** -/
theorem zeroU_of_not_mentions {e : Expr} {i : Nat} (h : mentions e i = false) : ZeroU (occ e i) := by
  induction e generalizing i with
  | var j =>
      rw [occ_var]
      have : j ≠ i := by simpa [mentions] using h
      simp [this, zeroU_zero]
  | unit | loc _ | prim _ => exact zeroU_zero
  | pair a b iha ihb | seq a b iha ihb =>
      simp only [mentions, Bool.or_eq_false_iff] at h
      exact seqO_zero_zero (iha h.1) (ihb h.2)
  | app a b iha ihb =>
      simp only [mentions, Bool.or_eq_false_iff] at h
      exact seqO_zero_zero (ihb h.2) (iha h.1)
  | inj₁ a ih | inj₂ a ih => exact ih h
  | lam b _ =>
      rw [occ_lam]
      have : mentions b (i + 1) = false := h
      simp [this, ZeroU]
  | letpair a b iha ihb =>
      simp only [mentions, Bool.or_eq_false_iff] at h
      exact seqO_zero_zero (iha h.1) (ihb h.2)
  | case s a b ihs iha ihb =>
      simp only [mentions, Bool.or_eq_false_iff] at h
      rw [occ_case]
      split
      · exact seqO_halt_zero (ihs h.1.1)
      · exact seqO_zero_zero (ihs h.1.1) (joinO_zero (iha h.1.2) (ihb h.2))

/-! ### Renaming -/

theorem liftR_injective {ρ : Nat → Nat} (h : Function.Injective ρ) :
    Function.Injective (liftR ρ) := by
  intro a b hab
  cases a <;> cases b <;> simp [liftR] at hab ⊢
  exact h hab

/-- A renamed term mentions the image of each variable it mentioned. -/
theorem mentions_ren {ρ : Nat → Nat} (hρ : Function.Injective ρ) (e : Expr) (i : Nat) :
    mentions (ren ρ e) (ρ i) = mentions e i := by
  induction e generalizing ρ i with
  | var j => simp only [ren, mentions, beq_eq_beq]; exact ⟨fun h => hρ h, fun h => h ▸ rfl⟩
  | unit | loc _ | prim _ => rfl
  | pair a b iha ihb | seq a b iha ihb | app a b iha ihb =>
      simp only [ren, mentions, iha hρ, ihb hρ]
  | inj₁ a ih | inj₂ a ih => exact ih hρ i
  | lam b ih =>
      simp only [ren, mentions]
      exact ih (liftR_injective hρ) (i + 1)
  | letpair a b iha ihb =>
      simp only [ren, mentions, iha hρ]
      exact congrArg _ (ihb (liftR_injective (liftR_injective hρ)) (i + 2))
  | case s a b ihs iha ihb =>
      simp only [ren, mentions, ihs hρ]
      rw [show ρ i + 1 = liftR ρ (i + 1) from rfl, iha (liftR_injective hρ),
        ihb (liftR_injective hρ)]

/-- A renamed term mentions no variable outside the renaming's image. -/
theorem mentions_ren_out {ρ : Nat → Nat} (e : Expr) {j : Nat} (h : ∀ i, ρ i ≠ j) :
    mentions (ren ρ e) j = false := by
  induction e generalizing ρ j with
  | var i => simpa [ren, mentions] using h i
  | unit | loc _ | prim _ => rfl
  | pair a b iha ihb | seq a b iha ihb | app a b iha ihb =>
      simp only [ren, mentions, iha h, ihb h, Bool.or_false]
  | inj₁ a ih | inj₂ a ih => exact ih h
  | lam b ih =>
      refine ih fun i => ?_
      cases i <;> simp [liftR, h]
  | letpair a b iha ihb =>
      simp only [ren, mentions, iha h, Bool.false_or]
      refine ihb fun i => ?_
      rcases i with _ | _ | i <;> simp [liftR, h]
  | case s a b ihs iha ihb =>
      simp only [ren, mentions, ihs h, Bool.false_or]
      have h' : ∀ i, liftR ρ i ≠ j + 1 := fun i => by cases i <;> simp [liftR, h]
      rw [iha h', ihb h']; rfl

theorem ren_eq_stuckE {ρ : Nat → Nat} {a : Expr} : ren ρ a = BoLo.stuckE ↔ a = BoLo.stuckE := by
  constructor
  · intro h
    cases a with
    | app f x =>
        simp only [ren, BoLo.stuckE, Expr.val, Val.unit, Expr.app.injEq] at h ⊢
        cases f <;> cases x <;> simp_all [ren]
    | _ => simp [ren, BoLo.stuckE] at h
  · rintro rfl; rfl

/-- **A renaming moves each variable's uses with it.** -/
theorem occ_ren {ρ : Nat → Nat} (hρ : Function.Injective ρ) (e : Expr) (i : Nat) :
    occ (ren ρ e) (ρ i) = occ e i := by
  induction e generalizing ρ i with
  | var j =>
      simp only [ren, occ_var]
      by_cases hj : j = i
      · simp [hj]
      · have : ρ j ≠ ρ i := fun h => hj (hρ h)
        simp [hj, this]
  | unit | loc _ | prim _ => rfl
  | pair a b iha ihb => simp only [ren, occ_pair, iha hρ, ihb hρ]
  | seq a b iha ihb => simp only [ren, occ_seq, iha hρ, ihb hρ]
  | app a b iha ihb => simp only [ren, occ_app, iha hρ, ihb hρ]
  | inj₁ a ih | inj₂ a ih => exact ih hρ i
  | lam b _ =>
      simp only [ren, occ_lam]
      rw [show ρ i + 1 = liftR ρ (i + 1) from rfl, mentions_ren (liftR_injective hρ)]
  | letpair a b iha ihb =>
      simp only [ren, occ_letpair, iha hρ]
      rw [show ρ i + 2 = liftR (liftR ρ) (i + 2) from rfl,
        ihb (liftR_injective (liftR_injective hρ))]
  | case s a b ihs iha ihb =>
      simp only [ren, occ_case, ihs hρ, ren_eq_stuckE]
      rw [show ρ i + 1 = liftR ρ (i + 1) from rfl, iha (liftR_injective hρ),
        ihb (liftR_injective hρ)]

/-- Off the renaming's image, a renamed term uses nothing. -/
theorem zeroU_ren_out {ρ : Nat → Nat} (e : Expr) {j : Nat} (h : ∀ i, ρ i ≠ j) :
    ZeroU (occ (ren ρ e) j) :=
  zeroU_of_not_mentions (mentions_ren_out e h)

/-! ### Closed terms -/

theorem mentions_of_closedAt {e : Expr} {k : Nat} (h : closedAt k e = true) {i : Nat} (hi : k ≤ i) :
    mentions e i = false := by
  induction e generalizing k i with
  | var j => simp only [closedAt, decide_eq_true_eq] at h; simp [mentions]; omega
  | unit | loc _ | prim _ => rfl
  | pair a b iha ihb | seq a b iha ihb | app a b iha ihb =>
      simp only [closedAt, Bool.and_eq_true] at h
      simp [mentions, iha h.1 hi, ihb h.2 hi]
  | inj₁ a ih | inj₂ a ih => exact ih h hi
  | lam b ih => exact ih (k := k + 1) h (i := i + 1) (by omega)
  | letpair a b iha ihb =>
      simp only [closedAt, Bool.and_eq_true] at h
      simp [mentions, iha h.1 hi, ihb (k := k + 2) h.2 (i := i + 2) (by omega)]
  | case s a b ihs iha ihb =>
      simp only [closedAt, Bool.and_eq_true] at h
      simp [mentions, ihs h.1.1 hi, iha (k := k + 1) h.1.2 (i := i + 1) (by omega),
        ihb (k := k + 1) h.2 (i := i + 1) (by omega)]

/-- A closed term is its own renaming. -/
theorem ren_closed {e : Expr} {k : Nat} {ρ : Nat → Nat} (h : closedAt k e = true)
    (hρ : ∀ i, i < k → ρ i = i) : ren ρ e = e := by
  induction e generalizing k ρ with
  | var j => simp only [closedAt, decide_eq_true_eq] at h; simp [ren, hρ j h]
  | unit | loc _ | prim _ => rfl
  | pair a b iha ihb | seq a b iha ihb | app a b iha ihb =>
      simp only [closedAt, Bool.and_eq_true] at h
      simp [ren, iha h.1 hρ, ihb h.2 hρ]
  | inj₁ a ih | inj₂ a ih => simp [ren, ih h hρ]
  | lam b ih =>
      have hl : ∀ i, i < k + 1 → liftR ρ i = i := fun i hi => by
        cases i with
        | zero => rfl
        | succ i => simp [liftR, hρ i (by omega)]
      simp [ren, ih (k := k + 1) h hl]
  | letpair a b iha ihb =>
      simp only [closedAt, Bool.and_eq_true] at h
      have hl : ∀ i, i < k + 2 → liftR (liftR ρ) i = i := fun i hi => by
        rcases i with _ | _ | i
        · rfl
        · rfl
        · simp [liftR, hρ i (by omega)]
      simp [ren, iha h.1 hρ, ihb (k := k + 2) h.2 hl]
  | case s a b ihs iha ihb =>
      simp only [closedAt, Bool.and_eq_true] at h
      have hl : ∀ i, i < k + 1 → liftR ρ i = i := fun i hi => by
        cases i with
        | zero => rfl
        | succ i => simp [liftR, hρ i (by omega)]
      simp [ren, ihs h.1.1 hρ, iha (k := k + 1) h.1.2 hl, ihb (k := k + 1) h.2 hl]

/-! ### Explicit ownership with closed constants -/

/-- `Explicit`, each constant closed. -/
inductive ExplicitC : Expr → Prop where
  | const {c : Expr} (h : LowConst c) (hc : closedAt 0 c = true) : ExplicitC c
  | var (i : Nat) : ExplicitC (.var i)
  | unit : ExplicitC .unit
  | loc (ℓ : Loc) : ExplicitC (.loc ℓ)
  | prim (p : Prim) : ExplicitC (.prim p)
  | pair {a b : Expr} (ha : ExplicitC a) (hb : ExplicitC b) : ExplicitC (.pair a b)
  | inj₁ {a : Expr} (h : ExplicitC a) : ExplicitC (.inj₁ a)
  | inj₂ {a : Expr} (h : ExplicitC a) : ExplicitC (.inj₂ a)
  | lam {b : Expr} (h : ExplicitC b) (h0 : once (occ b 0) = true)
      (hcap : ∀ j, mentions b (j + 1) = true → once (occ b (j + 1)) = true) : ExplicitC (.lam b)
  | seq {a b : Expr} (ha : ExplicitC a) (hb : ExplicitC b) : ExplicitC (.seq a b)
  | letpair {a b : Expr} (ha : ExplicitC a) (hb : ExplicitC b) (h0 : once (occ b 0) = true)
      (h1 : once (occ b 1) = true) : ExplicitC (.letpair a b)
  | case {s a b : Expr} (hs : ExplicitC s) (ha : ExplicitC a) (hb : ExplicitC b)
      (h₁ : once (occ a 0) = true) (h₂ : once (occ b 0) = true) : ExplicitC (.case s a b)
  | absurd {s : Expr} (hs : ExplicitC s) : ExplicitC (absurdL s)
  | app {f a : Expr} (hf : ExplicitC f) (ha : ExplicitC a) : ExplicitC (.app f a)

theorem ExplicitC.explicit {e : Expr} (h : ExplicitC e) : Explicit e := by
  induction h with
  | const h _ => exact .const h
  | var i => exact .var i
  | unit => exact .unit
  | loc ℓ => exact .loc ℓ
  | prim p => exact .prim p
  | pair _ _ iha ihb => exact .pair iha ihb
  | inj₁ _ ih => exact .inj₁ ih
  | inj₂ _ ih => exact .inj₂ ih
  | lam _ h0 hcap ih => exact .lam ih h0 hcap
  | seq _ _ iha ihb => exact .seq iha ihb
  | letpair _ _ h0 h1 iha ihb => exact .letpair iha ihb h0 h1
  | case _ _ _ h₁ h₂ ihs iha ihb => exact .case ihs iha ihb h₁ h₂
  | absurd _ ih => exact .absurd ih
  | app _ _ ihf iha => exact .app ihf iha

/-- A variable a renamed term mentions is the image of one the term mentions. -/
theorem mentions_ren_inv {ρ : Nat → Nat} {e : Expr} {j : Nat} (h : mentions (ren ρ e) j = true) :
    ∃ i, ρ i = j := by
  by_contra hn
  simp only [not_exists] at hn
  rw [mentions_ren_out e hn] at h
  exact Bool.false_ne_true h

/-- **An injective renaming keeps explicit ownership.** -/
theorem ExplicitC.ren {e : Expr} (h : ExplicitC e) :
    ∀ {ρ : Nat → Nat}, Function.Injective ρ → ExplicitC (Lowering.ren ρ e) := by
  induction h with
  | const h hc =>
      intro ρ _; rw [ren_closed hc (fun _ h => (Nat.not_lt_zero _ h).elim)]; exact .const h hc
  | var i => intro ρ _; exact .var _
  | unit => intro ρ _; exact .unit
  | loc ℓ => intro ρ _; exact .loc ℓ
  | prim p => intro ρ _; exact .prim p
  | pair _ _ iha ihb => intro ρ hρ; exact .pair (iha hρ) (ihb hρ)
  | inj₁ _ ih => intro ρ hρ; exact .inj₁ (ih hρ)
  | inj₂ _ ih => intro ρ hρ; exact .inj₂ (ih hρ)
  | @lam b _ h0 hcap ih =>
      intro ρ hρ
      have hl := liftR_injective hρ
      refine .lam (ih hl) (by rw [show (0 : Nat) = liftR ρ 0 from rfl, occ_ren hl]; exact h0)
        fun j hj => ?_
      obtain ⟨i, hi⟩ := mentions_ren_inv hj
      cases i with
      | zero => simp [liftR] at hi
      | succ i =>
          rw [← hi, occ_ren hl]
          rw [← hi, mentions_ren hl] at hj
          exact hcap i hj
  | seq _ _ iha ihb => intro ρ hρ; exact .seq (iha hρ) (ihb hρ)
  | @letpair a b _ _ h0 h1 iha ihb =>
      intro ρ hρ
      have hl := liftR_injective (liftR_injective hρ)
      refine .letpair (iha hρ) (ihb hl) ?_ ?_
      · rw [show (0 : Nat) = liftR (liftR ρ) 0 from rfl, occ_ren hl]; exact h0
      · rw [show (1 : Nat) = liftR (liftR ρ) 1 from rfl, occ_ren hl]; exact h1
  | case _ _ _ h₁ h₂ ihs iha ihb =>
      intro ρ hρ
      have hl := liftR_injective hρ
      refine .case (ihs hρ) (iha hl) (ihb hl) ?_ ?_
      · rw [show (0 : Nat) = liftR ρ 0 from rfl, occ_ren hl]; exact h₁
      · rw [show (0 : Nat) = liftR ρ 0 from rfl, occ_ren hl]; exact h₂
  | absurd _ ih => intro ρ hρ; exact .absurd (ih hρ)
  | app _ _ ihf iha => intro ρ hρ; exact .app (ihf hρ) (iha hρ)

/-- No effect primitive survives a renaming. -/
theorem effFreeB_ren (ρ : Nat → Nat) (e : Expr) : effFreeB (ren ρ e) = effFreeB e := by
  induction e generalizing ρ with
  | var _ | unit | loc _ | prim _ => rfl
  | pair a b iha ihb | seq a b iha ihb | app a b iha ihb | letpair a b iha ihb =>
      simp [ren, effFreeB, iha, ihb]
  | inj₁ a ih | inj₂ a ih | lam a ih => simp [ren, effFreeB, ih]
  | case s a b ihs iha ihb => simp [ren, effFreeB, ihs, iha, ihb]

end Lowering
