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

/-- The action leaves the functions as they were. -/
def SameFns (s s' : CState) : Prop := s'.fns = s.fns

theorem same_fresh {t : LTy} {s s' : CState} {x : Var} (h : Ok (fresh t) s x s') :
    SameFns s s' := by
  have := ok_modifyGet h; simp only [Prod.mk.injEq] at this; rw [this.2]; rfl

theorem SameFns.trans {a b c : CState} (h₁ : SameFns a b) (h₂ : SameFns b c) : SameFns a c := by
  unfold SameFns at *; rw [h₂, h₁]

theorem SameFns.refl (s : CState) : SameFns s s := rfl

/-- A continuation consuming its value `w` and the owned set `Θ`, making no function. -/
def ContK (D : Var → Prop) (Θ : Finset Var) (k : Var → CM Tm) : Prop :=
  ∀ w s₁ b s₂, w ∉ Θ → w < s₁.next → (∀ y ∈ Θ, y < s₁.next) → Ok (k w) s₁ b s₂ →
    SameFns s₁ s₂ ∧ Grows s₁ s₂ ∧ PostG D (insert w Θ) s₁.next s₂ b

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
    (∀ y ∈ Θ, y < s.next) → ContK D Θ k →
    SameFns s s' ∧ Grows s s' ∧ PostG D (insert v Θ) s.next s' tm
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
    obtain ⟨sf, hb⟩ := hk s₁.next s₂ b s₃ (fun h => by have := hΘ _ h; rw [k₁.1] at *; vomega)
      (by vomega) (fun y hy => by have := hΘ y hy; rw [k₁.1] at *; vomega) h₃
    have := post_letv_op (e := .inj false v) (xs := [v]) rfl (List.nodup_singleton v)
      (by simpa using hv) hn₂ hm₂ hb
    refine ⟨(show SameFns s s₁ by rw [ok_lift h₁]; rfl).trans ((same_fresh h₂).trans sf),
      k₁.grows.trans this.1, ?_⟩
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
    obtain ⟨sf, hb'⟩ := hk sa.next sb b' sc (fun h => by have := hΘ₁ _ h; rw [k₁.1] at *; vomega)
      (by vomega) (fun y hy => by have := hΘ₁ y hy; rw [k₁.1] at *; vomega) h₃
    have := post_letv_op (e := .inj true r) (xs := [r]) rfl (List.nodup_singleton r)
      (by simpa using hr) hn₂ hm₂ hb'
    refine ⟨(show SameFns s₁ sa by rw [ok_lift h₁]; rfl).trans ((same_fresh h₂).trans sf),
      k₁.grows.trans this.1, ?_⟩
    have e : ([r].toFinset ∪ Θ) = insert r Θ := by ext z; simp
    rw [e] at this; rw [← k₁.1]; exact this.2

/-- A family of continuations, one per summand. -/
def ContKs (D : Var → Prop) (Θ : Finset Var) (k : Nat → Var → CM Tm) : Prop :=
  ∀ j, ContK D Θ (k j)

/-- **`casePay p x k`**: `x` taken apart, an arm per summand, each arm's binder used once. -/
theorem casePay_spec {Θ : Finset Var} : ∀ (p : Pay) (x : Var) (k : Nat → Var → CM Tm)
    (s s' : CState) (tm : Tm), Ok (casePay p x k) s tm s' → x ∉ Θ → x < s.next →
    (∀ y ∈ Θ, y < s.next) → ContKs D Θ k →
    SameFns s s' ∧ Grows s s' ∧ PostG D (insert x Θ) s.next s' tm
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
    obtain ⟨sf₁, g₁, p₁⟩ := hk 0 s.next s₃ arm₁ s₄ (fun h => by have := hΘ _ h; vomega)
      (by rw [k₂.1] at *; vomega) hΘ₃ h₄
    have gn₁ := g₁.next
    obtain ⟨sf₂, g₂, p₂⟩ := casePay_spec (q :: rest) s₂.next (fun j v => k (j + 1) v) s₄ s₅ arm₂ h₅
      (fun h => by have := hΘ _ h; rw [k₂.1] at *; vomega) (by rw [k₂.1] at *; vomega)
      (fun y hy => by have := hΘ₃ y hy; vomega) (fun j => hk (j + 1))
    have gn₂ := g₂.next
    refine ⟨(same_fresh h₁).trans ((show SameFns s₁ s₂ by rw [ok_lift h₂]; rfl).trans
      ((same_fresh h₃).trans (sf₁.trans sf₂))),
      ⟨by rw [k₂.1] at *; vomega, by rw [g₂.mach, g₁.mach, hm₃, k₂.2, hm₁]⟩, ?_⟩
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

/-- The result of a builder: no function made, the counter grown, the term consuming `Γ`. -/
abbrev BuildOK (D : Var → Prop) (Γ : Finset Var) (s s' : CState) (b : Tm) : Prop :=
  SameFns s s' ∧ Grows s s' ∧ PostG D Γ s.next s' b

theorem buildOK_ops {t : Tm} {xs : List Var} {s : CState} (ho : operands t = some xs)
    (hn : xs.Nodup) : BuildOK D xs.toFinset s s t :=
  ⟨SameFns.refl s, Grows.refl s, postG_ops ho hn⟩

theorem contK_pure_ops {Θ : Finset Var} {f : Var → Tm}
    (hf : ∀ w, operands (f w) = some (w :: Θ.toList)) : ContK D Θ (fun w => pure (f w)) := by
  intro w s₁ b s₂ hw _ _ h
  obtain ⟨rfl, hs⟩ := ok_pure h
  rw [hs]
  have := buildOK_ops (D := D) (s := s₁) (hf w) (List.nodup_cons.2 ⟨by simpa using hw,
    Finset.nodup_toList Θ⟩)
  simpa using this

/-- **`coercePay p q x k`**: the payload `x` of `p` as one of `q`, handed to `k`. -/
theorem coercePay_spec {Θ : Finset Var} {p q : Pay} {x : Var} {k : Var → CM Tm} {s s' : CState}
    {tm : Tm} (h : Ok (coercePay p q x k) s tm s') (hx : x ∉ Θ) (hlt : x < s.next)
    (hΘ : ∀ y ∈ Θ, y < s.next) (hk : ContK D Θ k) : BuildOK D (insert x Θ) s s' tm := by
  simp only [coercePay] at h
  split at h
  · exact hk x s tm s' hx hlt hΘ h
  · refine casePay_spec p x _ s s' tm h hx hlt hΘ fun j => ?_
    intro v s₁ b s₂ hv hvlt hΘ₁ hb
    split at hb
    · split at hb
      · exact injectPay_spec q _ v k s₁ s₂ b hb hv hvlt hΘ₁ hk
      · exact (ok_throw hb).elim
    · exact (ok_throw hb).elim

/-- `let w = e; roll w`, `e` an injection of `x`: the machine's outcome forms. -/
theorem roll_inj_spec {x : Var} {right : Bool} {T : LTy} {s s' : CState} {tm : Tm}
    (h : Ok (do let w ← fresh T; return Tm.letv w (.inj right x) (.prim .roll [w])) s tm s')
    (hlt : x < s.next) : BuildOK D {x} s s' tm := by
  obtain ⟨w, s₁, h₁, h⟩ := ok_bind h
  obtain ⟨rfl, hn, hm⟩ := ok_fresh h₁
  obtain ⟨rfl, hs⟩ := ok_pure h
  rw [hs]
  have := post_letv_op (D := D) (Θ := ∅) (e := .inj right x) (xs := [x]) rfl
    (List.nodup_singleton x) (by simp) hn hm
    (b := .prim .roll [s.next]) (s₂ := s₁) ⟨Grows.refl _, by
      simpa using postG_ops (D := D) (lo := s₁.next) (s' := s₁) (t := .prim .roll [s.next])
        (xs := [s.next]) rfl (List.nodup_singleton _)⟩
  exact ⟨same_fresh h₁, this.1, by simpa using this.2⟩

theorem outValue_spec {F : OutInfo} {x : Var} {s s' : CState} {tm : Tm}
    (h : Ok (outValue F x) s tm s') (hlt : x < s.next) : BuildOK D {x} s s' tm :=
  roll_inj_spec h hlt

theorem outExit_spec {F : OutInfo} {x : Var} {s s' : CState} {tm : Tm}
    (h : Ok (outExit F x) s tm s') (hlt : x < s.next) : BuildOK D {x} s s' tm :=
  roll_inj_spec h hlt

theorem outAbort_spec {F : OutInfo} {e : Var} {s s' : CState} {tm : Tm}
    (h : Ok (outAbort F e) s tm s') (hlt : e < s.next) : BuildOK D {e} s s' tm := by
  simp only [outAbort] at h
  split at h
  · exact (ok_throw h).elim
  obtain ⟨x, s₁, h₁, h⟩ := ok_bind h
  obtain ⟨rfl, hn, hm⟩ := ok_fresh h₁
  obtain ⟨b, s₂, h₂, h⟩ := ok_bind h
  obtain ⟨rfl, rfl⟩ := ok_pure h
  obtain ⟨sf, g, p⟩ := outExit_spec (D := D) h₂ (by vomega)
  have := post_letv_op (D := D) (Θ := ∅) (e := .inj false e) (xs := [e]) rfl
    (List.nodup_singleton e) (by simp) hn hm ⟨g, by simpa using p⟩
  exact ⟨(same_fresh h₁).trans sf, this.1, by simpa using this.2⟩

/-- Two arms, each over its own fresh binder, of a `case` on `r`. -/
theorem buildOK_case {r x e : Var} {b₁ b₂ : Tm} {s s₂ s₃ s₄ : CState}
    (hx : x = s.next) (he : e = s.next + 1) (hn₂ : s.next + 2 ≤ s₂.next) (hm₂ : s₂.mach = s.mach)
    (sf₂ : SameFns s s₂) (hr : r < s.next)
    (h₁ : BuildOK D {x} s₂ s₃ b₁) (h₂ : BuildOK D {e} s₃ s₄ b₂) :
    BuildOK D {r} s s₄ (.case r x b₁ e b₂) := by
  obtain ⟨sf₁, g₁, p₁⟩ := h₁
  obtain ⟨sf₂', g₂, p₂⟩ := h₂
  have gn₁ := g₁.next; have gn₂ := g₂.next
  refine ⟨sf₂.trans (sf₁.trans sf₂'), ⟨by vomega, by rw [g₂.mach, g₁.mach, hm₂]⟩, ?_⟩
  have q₁ : PostG D (insert x ∅) s.next s₄ b₁ :=
    ⟨by simpa using p₁.closed, p₁.nodup, fun z hz => ⟨by have := (p₁.range z hz).1; vomega,
      by have := (p₁.range z hz).2; vomega⟩⟩
  have q₂ : PostG D (insert e ∅) s.next s₄ b₂ := by
    have := p₂.lower (lo' := s.next) (by vomega); simpa using this
  have := postG_case (Γ := ∅) (sv := r) (lo := s.next) (s' := s₄) (by simp) q₁ q₂
    ⟨by vomega, by vomega⟩ ⟨by vomega, by vomega⟩
    ⟨fun hh => by have := (p₁.range _ hh).1; vomega, fun hh => by have := (p₂.range _ hh).1; vomega,
      by vomega⟩
    ⟨fun hh => by have := (p₁.range _ hh).1; vomega, fun hh => by have := (p₂.range _ hh).1; vomega⟩
    (fun a ha hb => by have := (p₁.range _ ha).2; have := (p₂.range _ hb).1; vomega)
  simpa using this

/-- **`coerceRes a p q r`**: a result at `p` as one at `q`. -/
theorem coerceRes_spec {a : LTy} {p q : Pay} {r : Var} {s s' : CState} {tm : Tm}
    (h : Ok (coerceRes a p q r) s tm s') (hr : r < s.next) : BuildOK D {r} s s' tm := by
  simp only [coerceRes] at h
  have hv : ∀ t, operands t = some [r] → BuildOK D {r} s s t := fun t ho => by
    simpa using (buildOK_ops ho (List.nodup_singleton r) : BuildOK D [r].toFinset s s t)
  split at h
  · obtain ⟨rfl, hs⟩ := ok_pure h; rw [hs]; exact hv _ rfl
  split at h
  · obtain ⟨rfl, hs⟩ := ok_pure h; rw [hs]; exact hv _ rfl
  · obtain ⟨rfl, hs⟩ := ok_pure h; rw [hs]; exact hv _ rfl
  · obtain ⟨x, s₁, h₁, h⟩ := ok_bind h
    obtain ⟨rfl, hn₁, hm₁⟩ := ok_fresh h₁
    obtain ⟨e, s₂, h₂, h⟩ := ok_bind h
    obtain ⟨rfl, hn₂, hm₂⟩ := ok_fresh h₂
    obtain ⟨arm, s₃, h₃, h⟩ := ok_bind h
    obtain ⟨rfl, hs⟩ := ok_pure h
    rw [hs]
    have hc := coercePay_spec (D := D) (Θ := ∅) h₃ (by simp) (by vomega) (by simp)
      (contK_pure_ops (f := fun e' => .inj true e') fun w => by simp [operands])
    exact buildOK_case rfl hn₁ (by vomega) (hm₂.trans hm₁) ((same_fresh h₁).trans (same_fresh h₂))
      hr (by simpa using (buildOK_ops rfl (List.nodup_singleton _) :
        BuildOK D [s.next].toFinset s₂ s₂ (.inj false s.next))) (by simpa using hc)
  · exact (ok_throw h).elim

/-- **`toResult`**: the cancel's answer, at a payload or at an outcome. -/
theorem toResult_spec {a : LTy} {p : Pay} {target : Option OutInfo} {q : Pay} {r : Var}
    {s s' : CState} {tm : Tm} (h : Ok (toResult a p target q r) s tm s') (hr : r < s.next) :
    BuildOK D {r} s s' tm := by
  simp only [toResult] at h
  split at h
  · exact coerceRes_spec h hr
  split at h
  · exact outValue_spec h hr
  obtain ⟨x, s₁, h₁, h⟩ := ok_bind h
  obtain ⟨rfl, hn₁, hm₁⟩ := ok_fresh h₁
  obtain ⟨e, s₂, h₂, h⟩ := ok_bind h
  obtain ⟨rfl, hn₂, hm₂⟩ := ok_fresh h₂
  split at h
  swap; · exact (ok_throw h).elim
  obtain ⟨e', s₃, h₃, h⟩ := ok_bind h
  obtain ⟨rfl, hn₃, hm₃⟩ := ok_fresh h₃
  obtain ⟨b₁, s₄, h₄, h⟩ := ok_bind h
  obtain ⟨c, s₅, h₅, h⟩ := ok_bind h
  obtain ⟨b₂, s₆, h₆, h⟩ := ok_bind h
  obtain ⟨rfl, hs⟩ := ok_pure h
  rw [hs]
  obtain ⟨sf₄, g₄, p₄⟩ := outValue_spec (D := D) h₄ (by vomega)
  have gn₄ := g₄.next
  obtain ⟨sf₅, g₅, p₅⟩ := coercePay_spec (D := D) (Θ := ∅) h₅ (by simp) (by vomega) (by simp)
    (contK_pure_ops (f := fun v => .var v) fun w => by simp [operands])
  have gn₅ := g₅.next
  obtain ⟨sf₆, g₆, p₆⟩ := outAbort_spec (D := D) h₆ (by vomega)
  have gn₆ := g₆.next
  -- The abort arm: the coerced payload named `e'`, then the outcome's abort.
  have cl₂ : ClosedL D {s₁.next} (.letv s₂.next c b₂) := by
    have := LinL.letv_closed (Γ₂ := ∅) (x := s₂.next) (by simpa using p₅.closed) p₆.closed (by simp)
    simpa using this
  refine ⟨(same_fresh h₁).trans ((same_fresh h₂).trans ((same_fresh h₃).trans
    (sf₄.trans (sf₅.trans sf₆)))), ⟨by vomega, by rw [g₆.mach, g₅.mach, g₄.mach, hm₃, hm₂, hm₁]⟩,
    ?_⟩
  have q₁ : PostG D (insert s.next ∅) s.next s₆ b₁ :=
    ⟨by simpa using p₄.closed, p₄.nodup, fun z hz => ⟨by have := (p₄.range z hz).1; vomega,
      by have := (p₄.range z hz).2; vomega⟩⟩
  have q₂ : PostG D (insert s₁.next ∅) s.next s₆ (.letv s₂.next c b₂) := by
    refine ⟨by simpa using cl₂, ?_, ?_⟩
    · simp only [bnd, List.nodup_cons, List.mem_append, not_or, List.nodup_append]
      exact ⟨⟨fun hh => by have := (p₅.range _ hh).1; vomega,
        fun hh => by have := (p₆.range _ hh).1; vomega⟩, p₅.nodup, p₆.nodup,
        fun a ha b hb e => by rw [e] at ha; have := (p₅.range _ ha).2; have := (p₆.range _ hb).1; vomega⟩
    · intro z hz
      simp only [bnd, List.mem_cons, List.mem_append] at hz
      rcases hz with rfl | hz | hz
      · constructor <;> vomega
      · have := p₅.range z hz; exact ⟨by vomega, by vomega⟩
      · have := p₆.range z hz; exact ⟨by vomega, this.2⟩
  have := postG_case (Γ := ∅) (sv := r) (lo := s.next) (s' := s₆) (by simp) q₁ q₂
    ⟨by vomega, by vomega⟩ ⟨by vomega, by vomega⟩
    ⟨fun hh => by have := (p₄.range _ hh).1; vomega, fun hh => by
        simp only [bnd, List.mem_cons, List.mem_append] at hh
        rcases hh with hh | hh | hh
        · vomega
        · have := (p₅.range _ hh).1; vomega
        · have := (p₆.range _ hh).1; vomega, by vomega⟩
    ⟨fun hh => by have := (p₄.range _ hh).1; vomega, fun hh => by
        simp only [bnd, List.mem_cons, List.mem_append] at hh
        rcases hh with hh | hh | hh
        · vomega
        · have := (p₅.range _ hh).1; vomega
        · have := (p₆.range _ hh).1; vomega⟩
    (fun a ha hb => by
      have := (p₄.range _ ha); simp only [bnd, List.mem_cons, List.mem_append] at hb
      rcases hb with hb | hb | hb
      · vomega
      · have := (p₅.range _ hb).1; vomega
      · have := (p₆.range _ hb).1; vomega)
  simpa using this

end Backend2.Spike670
