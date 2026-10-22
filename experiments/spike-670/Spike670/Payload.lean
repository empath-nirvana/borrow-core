import Spike670.Closure

/-!
# #670 — slice 2 groundwork: the payload builders (SPEC §47)

`injectPay`, `casePay`, `coercePay`, `coerceRes` build the sums that rows' aborts travel in. Each
takes a continuation; each lemma says: if the continuation consumes its value and the rest of the
owned set `Θ`, the whole consumes the input and `Θ`, and every variable it invents (an injection's
result, an arm's binder) is used once.
-/

namespace Backend2.Spike670
open Backend2 BoCa.Fig16.LogRel.Core BoCa.Fig16.LogRel.Core.Check

variable {D : Var → Prop}

/-- A continuation consuming its value `w` and the owned set `Θ`. -/
def ContK (D : Var → Prop) (Θ : Finset Var) (k : Var → CM Tm) : Prop :=
  ∀ w s₁ b s₂, w ∉ Θ → w < s₁.next → (∀ y ∈ Θ, y < s₁.next) → Ok (k w) s₁ b s₂ →
    Grows s₁ s₂ ∧ PostG D (insert w Θ) s₁.next s₂ b

/-- `let w = e; b`, `e` an operand form consuming `xs`, `w` the counter's next variable. -/
theorem post_letv_op {e : Tm} {xs : List Var} {Θ : Finset Var} {s s₁ s₂ : CState} {b : Tm}
    (ho : operands e = some xs) (hn : xs.Nodup) (hd : ∀ x ∈ xs, x ∉ Θ)
    (hn₁ : s₁.next = s.next + 1) (hm₁ : s₁.mach = s.mach)
    (hb : Grows s₁ s₂ ∧ PostG D (insert s.next Θ) s₁.next s₂ b) :
    Grows s s₂ ∧ PostG D (xs.toFinset ∪ Θ) s.next s₂ (.letv s.next e b) := by
  obtain ⟨g, ⟨cl, nd, rg⟩⟩ := hb
  have gn := g.next
  refine ⟨⟨by vomega, g.mach.trans hm₁⟩, ⟨?_, ?_, ?_⟩⟩
  · exact LinL.letv_closed (postG_ops (D := D) (lo := s.next) (s' := s) ho hn).closed cl
      fun y hy => ⟨fun h => hd y (by simpa using h) hy, by simp [operands_bnd ho]⟩
  · simp only [bnd, operands_bnd ho, List.nil_append, List.nodup_cons]
    exact ⟨fun h => by have := (rg _ h).1; vomega, nd⟩
  · intro y hy
    simp only [bnd, operands_bnd ho, List.nil_append, List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact ⟨le_refl _, by vomega⟩
    · have := rg y hy; exact ⟨by vomega, this.2⟩

theorem ok_lift' {r : Except String α} {s s' : CState} {a : α} (h : Ok (lift r) s a s') :
    Keeps s s' := ok_lift h ▸ Keeps.refl _

/-- **`injectPay p j v k`**: `v` at summand `j`, the injections each named and used once. -/
theorem injectPay_spec {Θ : Finset Var} : ∀ (p : Pay) (j : Nat) (v : Var) (k : Var → CM Tm)
    (s s' : CState) (tm : Tm), Ok (injectPay p j v k) s tm s' → v ∉ Θ → v < s.next →
    (∀ y ∈ Θ, y < s.next) → ContK D Θ k → Grows s s' ∧ PostG D (insert v Θ) s.next s' tm
  | [], _, _, _, _, _, _, h, _, _, _, _ => by
    simp only [injectPay] at h; exact (ok_throw h).elim
  | [_], _, v, k, s, s', tm, h, hv, hlt, hΘ, hk => by
    simp only [injectPay] at h
    exact hk v s tm s' hv hlt hΘ h
  | _ :: _ :: rest, 0, v, k, s, s', tm, h, hv, hlt, hΘ, hk => by
    simp only [injectPay] at h
    obtain ⟨t, s₁, h₁, h⟩ := ok_bind h
    have k₁ := ok_lift' h₁
    obtain ⟨w, s₂, h₂, h⟩ := ok_bind h
    obtain ⟨rfl, hn₂, hm₂⟩ := ok_fresh h₂
    obtain ⟨b, s₃, h₃, h⟩ := ok_bind h
    obtain ⟨rfl, hs⟩ := ok_pure h
    rw [hs]
    have hb := hk s₁.next s₂ b s₃ (fun h => by have := hΘ _ h; rw [k₁.1] at *; vomega)
      (by vomega) (fun y hy => by have := hΘ y hy; rw [k₁.1] at *; vomega) h₃
    have := post_letv_op (e := .inj false v) (xs := [v]) rfl (List.nodup_singleton v)
      (by simpa using hv) hn₂ hm₂ hb
    refine ⟨k₁.grows.trans this.1, ?_⟩
    have e : ([v].toFinset ∪ Θ) = insert v Θ := by ext z; simp
    rw [e] at this; rw [← k₁.1]; exact this.2
  | _ :: q :: rest, j + 1, v, k, s, s', tm, h, hv, hlt, hΘ, hk => by
    simp only [injectPay] at h
    refine injectPay_spec (q :: rest) j v _ s s' tm h hv hlt hΘ ?_
    intro r s₁ b s₂ hr hrlt hΘ₁ hb
    obtain ⟨t, sa, h₁, hb⟩ := ok_bind hb
    have k₁ := ok_lift' h₁
    obtain ⟨w, sb, h₂, hb⟩ := ok_bind hb
    obtain ⟨rfl, hn₂, hm₂⟩ := ok_fresh h₂
    obtain ⟨b', sc, h₃, hb⟩ := ok_bind hb
    obtain ⟨rfl, hs⟩ := ok_pure hb
    rw [hs]
    have hb' := hk sa.next sb b' sc (fun h => by have := hΘ₁ _ h; rw [k₁.1] at *; vomega)
      (by vomega) (fun y hy => by have := hΘ₁ y hy; rw [k₁.1] at *; vomega) h₃
    have := post_letv_op (e := .inj true r) (xs := [r]) rfl (List.nodup_singleton r)
      (by simpa using hr) hn₂ hm₂ hb'
    refine ⟨k₁.grows.trans this.1, ?_⟩
    have e : ([r].toFinset ∪ Θ) = insert r Θ := by ext z; simp
    rw [e] at this; rw [← k₁.1]; exact this.2

/-- A family of continuations, one per summand. -/
def ContKs (D : Var → Prop) (Θ : Finset Var) (k : Nat → Var → CM Tm) : Prop :=
  ∀ j, ContK D Θ (k j)

/-- **`casePay p x k`**: `x` taken apart, an arm per summand, each arm's binder used once. -/
theorem casePay_spec {Θ : Finset Var} : ∀ (p : Pay) (x : Var) (k : Nat → Var → CM Tm)
    (s s' : CState) (tm : Tm), Ok (casePay p x k) s tm s' → x ∉ Θ → x < s.next →
    (∀ y ∈ Θ, y < s.next) → ContKs D Θ k → Grows s s' ∧ PostG D (insert x Θ) s.next s' tm
  | [], _, _, _, _, _, h, _, _, _, _ => by
    simp only [casePay] at h; exact (ok_throw h).elim
  | [_], x, k, s, s', tm, h, hx, hlt, hΘ, hk => by
    simp only [casePay] at h
    exact hk 0 x s tm s' hx hlt hΘ h
  | (_, t) :: q :: rest, x, k, s, s', tm, h, hx, hlt, hΘ, hk => by
    simp only [casePay] at h
    obtain ⟨a, s₁, h₁, h⟩ := ok_bind h
    obtain ⟨rfl, hn₁, hm₁⟩ := ok_fresh h₁
    obtain ⟨bt, s₂, h₂, h⟩ := ok_bind h
    have k₂ := ok_lift' h₂
    obtain ⟨b, s₃, h₃, h⟩ := ok_bind h
    obtain ⟨rfl, hn₃, hm₃⟩ := ok_fresh h₃
    obtain ⟨arm₁, s₄, h₄, h⟩ := ok_bind h
    obtain ⟨arm₂, s₅, h₅, h⟩ := ok_bind h
    obtain ⟨rfl, hs⟩ := ok_pure h
    rw [hs]
    have hΘ₃ : ∀ y ∈ Θ, y < s₃.next := fun y hy => by have := hΘ y hy; rw [k₂.1] at *; vomega
    obtain ⟨g₁, p₁⟩ := hk 0 s.next s₃ arm₁ s₄ (fun h => by have := hΘ _ h; vomega)
      (by rw [k₂.1] at *; vomega) hΘ₃ h₄
    have gn₁ := g₁.next
    obtain ⟨g₂, p₂⟩ := casePay_spec (q :: rest) s₂.next (fun j v => k (j + 1) v) s₄ s₅ arm₂ h₅
      (fun h => by have := hΘ _ h; rw [k₂.1] at *; vomega) (by rw [k₂.1] at *; vomega)
      (fun y hy => by have := hΘ₃ y hy; vomega) (fun j => hk (j + 1))
    have gn₂ := g₂.next
    refine ⟨⟨by rw [k₂.1] at *; vomega, by rw [g₂.mach, g₁.mach, hm₃, k₂.2, hm₁]⟩, ?_⟩
    have q₁ : PostG D (insert s.next Θ) s.next s₅ arm₁ :=
      ⟨p₁.closed, p₁.nodup, fun z hz => ⟨by have := (p₁.range z hz).1; rw [k₂.1] at *; vomega,
        by have := (p₁.range z hz).2; vomega⟩⟩
    have q₂ : PostG D (insert s₂.next Θ) s.next s₅ arm₂ := p₂.lower (by rw [k₂.1] at *; vomega)
    refine postG_case (fun h => hx h) q₁ q₂ ⟨le_refl _, by rw [k₂.1] at *; vomega⟩
      ⟨by rw [k₂.1] at *; vomega, by rw [k₂.1] at *; vomega⟩
      ⟨fun hh => ?_, fun hh => ?_, by rw [k₂.1] at *; vomega⟩ ⟨fun hh => ?_, fun hh => ?_⟩
      (fun a ha hb => ?_)
    · have := (p₁.range _ hh).1; rw [k₂.1] at *; vomega
    · have := (p₂.range _ hh).1; rw [k₂.1] at *; vomega
    · have := (p₁.range _ hh).1; rw [k₂.1] at *; vomega
    · have := (p₂.range _ hh).1; vomega
    · have := (p₁.range _ ha).2; have := (p₂.range _ hb).1; vomega

end Backend2.Spike670
