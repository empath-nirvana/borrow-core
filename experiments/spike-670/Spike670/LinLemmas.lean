import Spike670.LinOK
import Backend2.Convert

/-!
# #670 — structural lemmas of `LinL`

Framing (`LinL.frame`): an owned set disjoint from a term's context and binders passes through
it untouched. The conversion's small builders (`drops`, `bindTm`'s two shapes) as rules.
-/

namespace Backend2.Spike670
open Backend2

variable {D : Var → Prop}

/-- The leftovers of a returning term are its context's or its binders. -/
theorem UseAll.sub {Γ xs Γ'} (h : UseAll Γ xs Γ') : Γ' ⊆ Γ := by
  induction h with
  | nil => exact le_refl _
  | cons _ _ ih => exact ih.trans (Finset.erase_subset _ _)

theorem UseAll.mem {Γ xs Γ'} (h : UseAll Γ xs Γ') : ∀ y ∈ xs, y ∈ Γ := by
  induction h with
  | nil => simp
  | cons hx _ ih =>
    intro y hy
    rcases List.mem_cons.1 hy with rfl | h
    · exact hx
    · exact Finset.mem_of_mem_erase (ih y h)

theorem UseAll.frame {Γ xs Γ'} (h : UseAll Γ xs Γ') (Θ : Finset Var) (hd : ∀ y ∈ Θ, y ∉ xs) :
    UseAll (Γ ∪ Θ) xs (Γ' ∪ Θ) := by
  induction h with
  | nil => exact .nil
  | @cons Γ x xs Γ' hx _ ih =>
    refine .cons (Finset.mem_union_left _ hx) ?_
    have hxΘ : x ∉ Θ := fun h => hd x h (by simp)
    have : (Γ ∪ Θ).erase x = Γ.erase x ∪ Θ := by
      ext y; by_cases hy : y = x <;> simp [hy, hxΘ]
    rw [this]; exact ih fun y hy h => hd y hy (by simp [h])

theorem LinL.sub {Γ t Δ} (h : LinL D Γ t (some Δ)) : ∀ y ∈ Δ, y ∈ Γ ∨ y ∈ bnd t := by
  generalize hΔ : some Δ = oΔ at h
  induction h generalizing Δ with
  | ops _ hu => cases hΔ; exact fun y hy => .inl (hu.sub hy)
  | letvNone => cases hΔ
  | letv _ _ ih₁ ih₂ =>
    intro y hy
    rcases ih₂ hΔ y hy with h | h
    · rcases Finset.mem_insert.1 h with rfl | h
      · exact .inr (by simp [bnd])
      · rcases ih₁ rfl y h with h | h
        · exact .inl h
        · exact .inr (by simp [bnd, h])
    · exact .inr (by simp [bnd, h])
  | letpair _ _ ih =>
    intro y hy
    rcases ih hΔ y hy with h | h
    · simp only [Finset.mem_insert, Finset.mem_erase] at h
      rcases h with rfl | rfl | ⟨_, h⟩
      · exact .inr (by simp [bnd])
      · exact .inr (by simp [bnd])
      · exact .inl h
    · exact .inr (by simp [bnd, h])
  | @case Γ s x b₁ y' b₂ Δ₁ Δ₂ Δ' _ _ _ hj ih₁ ih₂ =>
    intro y hy
    cases Δ₁ with
    | none =>
      cases Δ₂ with
      | none => simp [Join] at hj; subst hj; cases hΔ
      | some Δ₂ =>
        simp [Join] at hj; subst hj; cases hΔ
        rcases ih₂ rfl y hy with h | h
        · simp only [Finset.mem_insert, Finset.mem_erase] at h
          rcases h with rfl | ⟨_, h⟩
          · exact .inr (by simp [bnd])
          · exact .inl h
        · exact .inr (by simp [bnd, h])
    | some Δ₁ =>
      have hΔ₁ : Δ₁ = Δ := by
        cases Δ₂ with
        | none => simp [Join] at hj; subst hj; cases hΔ; rfl
        | some _ => simp [Join] at hj; obtain ⟨_, rfl⟩ := hj; cases hΔ; rfl
      subst hΔ₁
      rcases ih₁ rfl y hy with h | h
      · simp only [Finset.mem_insert, Finset.mem_erase] at h
        rcases h with rfl | ⟨_, h⟩
        · exact .inr (by simp [bnd])
        · exact .inl h
      · exact .inr (by simp [bnd, h])
  | absurd => cases hΔ
  | copy _ _ _ ih =>
    intro y hy
    rcases ih hΔ y hy with h | h
    · rcases Finset.mem_insert.1 h with rfl | h
      · exact .inr (by simp [bnd])
      · exact .inl h
    · exact .inr (by simp [bnd, h])
  | drop _ _ ih =>
    intro y hy
    rcases ih hΔ y hy with h | h
    · exact .inl (Finset.mem_of_mem_erase h)
    · exact .inr (by simpa [bnd] using h)

/-- The variables an operand-only form consumes are its operands. -/
theorem operands_bnd {t xs} (h : operands t = some xs) : bnd t = [] := by
  cases t <;> simp_all [operands, bnd]

/-- **Framing.** Owned variables that the term neither holds nor binds are left as they were. -/
theorem LinL.frame {Γ t Δ} (h : LinL D Γ t Δ) (Θ : Finset Var)
    (hΓ : ∀ y ∈ Θ, y ∉ Γ) (hb : ∀ y ∈ Θ, y ∉ bnd t) :
    LinL D (Γ ∪ Θ) t (Δ.map (· ∪ Θ)) := by
  induction h with
  | @ops Γ t xs Γ' ho hu =>
    exact .ops ho (hu.frame Θ fun y hy hxs => hΓ y hy (hu.mem y hxs))
  | letvNone _ ih =>
    exact .letvNone (ih hΓ fun y hy h => hb y hy (by simp [bnd, h]))
  | @letv Γ x e b Γ₁ Δ he hb' ih₁ ih₂ =>
    have h₁ := ih₁ hΓ fun y hy h => hb y hy (by simp [bnd, h])
    refine .letv h₁ ?_
    have := ih₂ (fun y hy h => ?_) (fun y hy h => hb y hy (by simp [bnd, h]))
    · simpa [Finset.insert_union] using this
    · rcases Finset.mem_insert.1 h with rfl | h
      · exact hb _ hy (by simp [bnd])
      · rcases he.sub y h with h | h
        · exact hΓ y hy h
        · exact hb y hy (by simp [bnd, h])
  | @letpair Γ x y q b Δ hq _ ih =>
    refine .letpair (Finset.mem_union_left _ hq) ?_
    have hqΘ : q ∉ Θ := fun h => hΓ q h hq
    have e : insert y (insert x ((Γ ∪ Θ).erase q)) = insert y (insert x (Γ.erase q)) ∪ Θ := by
      ext z; by_cases hz : z = q <;> simp [hz, hqΘ]
    rw [e]
    refine ih (fun z hz h => ?_) (fun z hz h => hb z hz (by simp [bnd, h]))
    simp only [Finset.mem_insert, Finset.mem_erase] at h
    rcases h with rfl | rfl | ⟨_, h⟩
    · exact hb _ hz (by simp [bnd])
    · exact hb _ hz (by simp [bnd])
    · exact hΓ z hz h
  | @case Γ s x b₁ y b₂ Δ₁ Δ₂ Δ hs _ _ hj ih₁ ih₂ =>
    have hsΘ : s ∉ Θ := fun h => hΓ s h hs
    have e : ∀ v, insert v ((Γ ∪ Θ).erase s) = insert v (Γ.erase s) ∪ Θ := by
      intro v; ext z; by_cases hz : z = s <;> simp [hz, hsΘ]
    refine .case (Δ₁ := Δ₁.map (· ∪ Θ)) (Δ₂ := Δ₂.map (· ∪ Θ)) (Finset.mem_union_left _ hs) ?_ ?_ ?_
    · rw [e]
      refine ih₁ (fun z hz h => ?_) (fun z hz h => hb z hz (by simp [bnd, h]))
      simp only [Finset.mem_insert, Finset.mem_erase] at h
      rcases h with rfl | ⟨_, h⟩
      · exact hb _ hz (by simp [bnd])
      · exact hΓ z hz h
    · rw [e]
      refine ih₂ (fun z hz h => ?_) (fun z hz h => hb z hz (by simp [bnd, h]))
      simp only [Finset.mem_insert, Finset.mem_erase] at h
      rcases h with rfl | ⟨_, h⟩
      · exact hb _ hz (by simp [bnd])
      · exact hΓ z hz h
    · cases Δ₁ <;> cases Δ₂ <;> simp_all [Join]
  | absurd hs => exact .absurd (Finset.mem_union_left _ hs)
  | @copy Γ x x' b Δ hx hD _ ih =>
    refine .copy (Finset.mem_union_left _ hx) hD ?_
    have := ih (fun z hz h => ?_) (fun z hz h => hb z hz (by simp [bnd, h]))
    · simpa [Finset.insert_union] using this
    · rcases Finset.mem_insert.1 h with rfl | h
      · exact hb _ hz (by simp [bnd])
      · exact hΓ z hz h
  | @drop Γ x b Δ hx _ ih =>
    refine .drop (Finset.mem_union_left _ hx) ?_
    have hxΘ : x ∉ Θ := fun h => hΓ x h hx
    have e : (Γ ∪ Θ).erase x = Γ.erase x ∪ Θ := by
      ext z; by_cases hz : z = x <;> simp [hz, hxΘ]
    rw [e]
    exact ih (fun z hz h => hΓ z hz (Finset.mem_of_mem_erase h))
      (fun z hz h => hb z hz (by simpa [bnd] using h))

/-! ### The conversion's builders -/

theorem bnd_drops (xs : List Var) (b : Tm) : bnd (drops xs b) = bnd b := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa [drops, bnd] using ih

/-- `drops xs b`: each of `xs` dropped, then `b`. -/
theorem LinL.drops {Γ xs b Δ} (hn : xs.Nodup) (hx : ∀ x ∈ xs, x ∈ Γ)
    (h : LinL D (Γ \ xs.toFinset) b Δ) : LinL D Γ (Backend2.drops xs b) Δ := by
  induction xs generalizing Γ with
  | nil => simpa [Backend2.drops] using h
  | cons x xs ih =>
    simp only [Backend2.drops, List.foldr_cons]
    refine .drop (hx x (by simp)) ?_
    refine ih (List.nodup_cons.1 hn).2 (fun y hy => ?_) ?_
    · exact Finset.mem_erase.2 ⟨fun e => (List.nodup_cons.1 hn).1 (e ▸ hy), hx y (by simp [hy])⟩
    · have : Γ.erase x \ xs.toFinset = Γ \ (x :: xs).toFinset := by
        ext y; simp; tauto
      rw [this]; exact h

/-- A closed term, or one unreachable. -/
abbrev ClosedL (D : Var → Prop) (Γ : Finset Var) (t : Tm) : Prop :=
  ∃ Δ, LinL D Γ t Δ ∧ Closed Δ

/-- **`bindTm e t k`**: `e` consuming `Γ₁` and closed, then `k x` at `Γ₂` with `x` its value.
The binder is `x`, chosen outside `Γ₂` and outside `e`'s binders. -/
theorem LinL.letv_closed {Γ₁ Γ₂ e x b} (he : ClosedL D Γ₁ e) (hb : ClosedL D (insert x Γ₂) b)
    (hd : ∀ y ∈ Γ₂, y ∉ Γ₁ ∧ y ∉ bnd e) : ClosedL D (Γ₁ ∪ Γ₂) (.letv x e b) := by
  obtain ⟨Δ, he, hc⟩ := he
  have hf := he.frame Γ₂ (fun y hy => (hd y hy).1) (fun y hy => (hd y hy).2)
  rcases hc with rfl | rfl
  · exact ⟨none, .letvNone hf, .inl rfl⟩
  · simp only [Option.map_some, Finset.empty_union] at hf
    obtain ⟨Δ', hb, hc'⟩ := hb
    exact ⟨Δ', .letv hf hb, hc'⟩

/-- A variable term that is closed consumes exactly that variable. -/
theorem LinL.var_closed {Γ x} (h : ClosedL D Γ (.var x)) : Γ = {x} := by
  obtain ⟨Δ, h, hc⟩ := h
  cases h with
  | ops ho hu =>
    simp [operands] at ho; subst ho
    cases hu with
    | cons hx hu =>
      cases hu
      rcases hc with h | h
      · cases h
      · simp only [Option.some.injEq, Finset.erase_eq_empty_iff] at h
        rcases h with h | h
        · simp [h] at hx
        · exact h

theorem bnd_bindTm_letv {e : Tm} {x : Var} {b : Tm} : bnd (.letv x e b) = x :: (bnd e ++ bnd b) := rfl

end Backend2.Spike670

namespace Backend2.Spike670
open Backend2

/-- The arity facts at every operand-only form of a term. -/
def ArOK (p : Prog) : Tm → Prop
  | .letv _ e b => ArOK p e ∧ ArOK p b
  | .letpair _ _ _ b | .copy _ _ b | .drop _ b => ArOK p b
  | .case _ _ b₁ _ b₂ => ArOK p b₁ ∧ ArOK p b₂
  | t => AritiesOK p t

theorem ArOK_ops {p : Prog} {t : Tm} {xs : List Var} (ho : operands t = some xs) (ha : ArOK p t) :
    AritiesOK p t := by
  cases t <;> simp_all [ArOK, operands]

/-- **From `LinL` to `Lin`**: binders that are distinct, new to the program and typed make the
bound set's threading go through. -/
theorem LinL.toLin {p : Prog} {D : Var → Prop} {Γ t Δ} (h : LinL D Γ t Δ) :
    ∀ {B : Finset Var}, (bnd t).Nodup → (∀ x ∈ bnd t, x ∉ B ∧ Typed p x) → Γ ⊆ B → ArOK p t →
    ∃ B', Lin p D B Γ t Δ B' ∧ B ⊆ B' ∧ B' ⊆ B ∪ (bnd t).toFinset ∧
      (∀ Δ', Δ = some Δ' → Δ' ⊆ B') := by
  induction h with
  | @ops Γ t xs Γ' ho hu =>
    intro B _ _ hΓ ha
    exact ⟨B, .ops ho (ArOK_ops ho ha) hu, le_refl _, Finset.subset_union_left, fun _ e => by
      cases e; exact hu.sub.trans hΓ⟩
  | @letvNone Γ x e b _ ih =>
    intro B hn hb hΓ ha
    simp only [bnd, List.nodup_cons, List.nodup_append, List.mem_append] at hn
    obtain ⟨B₁, l, s₁, s₂, -⟩ := ih (B := B) hn.2.1 (fun y hy => hb y (by simp [bnd, hy])) hΓ ha.1
    exact ⟨B₁, .letvNone l, s₁, s₂.trans (by intro z; simp [bnd] <;> tauto), by simp⟩
  | @letv Γ x e b Γ₁ Δ he _ ih₁ ih₂ =>
    intro B hn hb hΓ ha
    simp only [bnd, List.nodup_cons, List.nodup_append, List.mem_append, not_or] at hn
    obtain ⟨B₁, l₁, s₁, s₂, e₁⟩ := ih₁ (B := B) hn.2.1 (fun y hy => hb y (by simp [bnd, hy])) hΓ ha.1
    have hxB₁ : x ∉ B₁ := fun h => by
      have := s₂ h; simp only [Finset.mem_union, List.mem_toFinset] at this
      rcases this with h | h
      · exact (hb x (by simp [bnd])).1 h
      · exact hn.1.1 h
    obtain ⟨B₂, l₂, s₃, s₄, e₂⟩ := ih₂ (B := insert x B₁) hn.2.2.1
      (fun y hy => ⟨by
        simp only [Finset.mem_insert, not_or]
        refine ⟨fun h => hn.1.2 (h ▸ hy), fun h => ?_⟩
        have := s₂ h; simp only [Finset.mem_union, List.mem_toFinset] at this
        rcases this with h | h
        · exact (hb y (by simp [bnd, hy])).1 h
        · exact hn.2.2.2 y h y hy rfl, (hb y (by simp [bnd, hy])).2⟩)
      (Finset.insert_subset_insert _ (e₁ Γ₁ rfl)) ha.2
    refine ⟨B₂, .letv l₁ hxB₁ (hb x (by simp [bnd])).2 l₂, ?_, ?_, e₂⟩
    · exact s₁.trans ((Finset.subset_insert _ _).trans s₃)
    · intro z hz
      have h4 := s₄ hz
      simp only [Finset.mem_union, Finset.mem_insert, List.mem_toFinset] at h4
      simp only [bnd, Finset.mem_union, List.mem_toFinset, List.mem_cons, List.mem_append]
      rcases h4 with (h | h) | h
      · exact .inr (.inl h)
      · have h2 := s₂ h; simp only [Finset.mem_union, List.mem_toFinset] at h2; tauto
      · tauto
  | @letpair Γ x y q b Δ hq _ ih =>
    intro B hn hb hΓ ha
    simp only [bnd, List.nodup_cons, List.mem_cons, not_or] at hn
    have hx := hb x (by simp [bnd]); have hy := hb y (by simp [bnd])
    obtain ⟨B', l, s₁, s₂, e⟩ := ih (B := insert y (insert x B)) hn.2.2
      (fun z hz => ⟨by
        simp only [Finset.mem_insert, not_or]
        exact ⟨fun h => hn.2.1 (h ▸ hz), fun h => hn.1.2 (h ▸ hz), (hb z (by simp [bnd, hz])).1⟩,
        (hb z (by simp [bnd, hz])).2⟩)
      (fun z hz => by
        simp only [Finset.mem_insert, Finset.mem_erase] at hz ⊢
        rcases hz with rfl | rfl | ⟨_, hz⟩
        · exact .inl rfl
        · exact .inr (.inl rfl)
        · exact .inr (.inr (hΓ hz)))
      ha
    have hyxB : y ∉ insert x B := by
      simp only [Finset.mem_insert, not_or]; exact ⟨fun h => hn.1.1 h.symm, hy.1⟩
    refine ⟨B', .letpair hq hx.1 hx.2 hyxB hy.2 l, ?_, ?_, e⟩
    · exact (Finset.subset_insert _ _).trans ((Finset.subset_insert _ _).trans s₁)
    · refine s₂.trans ?_; intro z; simp [bnd] <;> tauto
  | @case Γ s x b₁ y b₂ Δ₁ Δ₂ Δ hs _ _ hj ih₁ ih₂ =>
    intro B hn hb hΓ ha
    simp only [bnd, List.nodup_cons, List.nodup_append, List.mem_append, List.mem_cons,
      not_or] at hn
    have hx := hb x (by simp [bnd]); have hy := hb y (by simp [bnd])
    obtain ⟨B₁, l₁, s₁, s₂, e₁⟩ := ih₁ (B := insert x B) hn.2.1
      (fun z hz => ⟨by
        simp only [Finset.mem_insert, not_or]
        exact ⟨fun h => hn.1.1 (h ▸ hz), (hb z (by simp [bnd, hz])).1⟩,
        (hb z (by simp [bnd, hz])).2⟩)
      (fun z hz => by
        simp only [Finset.mem_insert, Finset.mem_erase] at hz ⊢
        rcases hz with rfl | ⟨_, hz⟩
        · exact .inl rfl
        · exact .inr (hΓ hz))
      ha.1
    have hyB₁ : y ∉ B₁ := fun h => by
      have := s₂ h; simp only [Finset.mem_union, Finset.mem_insert, List.mem_toFinset] at this
      rcases this with (h | h) | h
      · exact hn.1.2.1 h.symm
      · exact hy.1 h
      · exact hn.2.2.2 y h y (by simp) rfl
    obtain ⟨B₂, l₂, s₃, s₄, e₂⟩ := ih₂ (B := insert y B₁) hn.2.2.1.2
      (fun z hz => ⟨by
        simp only [Finset.mem_insert, not_or]
        refine ⟨fun h => hn.2.2.1.1 (h ▸ hz), fun h => ?_⟩
        have := s₂ h; simp only [Finset.mem_union, Finset.mem_insert, List.mem_toFinset] at this
        rcases this with (h | h) | h
        · exact hn.1.2.2 (h ▸ hz)
        · exact (hb z (by simp [bnd, hz])).1 h
        · exact hn.2.2.2 z h z (by simp [hz]) rfl, (hb z (by simp [bnd, hz])).2⟩)
      (fun z hz => by
        simp only [Finset.mem_insert, Finset.mem_erase] at hz ⊢
        rcases hz with rfl | ⟨_, hz⟩
        · exact .inl rfl
        · exact .inr (s₁ (Finset.mem_insert_of_mem (hΓ hz))))
      ha.2
    refine ⟨B₂, .case hs hx.1 hx.2 l₁ hyB₁ hy.2 l₂ hj, ?_, ?_, ?_⟩
    · exact ((Finset.subset_insert _ _).trans s₁).trans ((Finset.subset_insert _ _).trans s₃)
    · intro z hz
      have h4 := s₄ hz
      simp only [Finset.mem_union, Finset.mem_insert, List.mem_toFinset] at h4
      simp only [bnd, Finset.mem_union, List.mem_toFinset, List.mem_cons, List.mem_append]
      rcases h4 with (h | h) | h
      · tauto
      · have h2 := s₂ h; simp only [Finset.mem_union, Finset.mem_insert, List.mem_toFinset] at h2
        tauto
      · tauto
    · intro Δ' hΔ
      subst hΔ
      cases Δ₁ with
      | none => simp [Join] at hj; exact e₂ Δ' hj.symm
      | some a =>
        cases Δ₂ with
        | none =>
          simp [Join] at hj; subst hj
          exact (e₁ _ rfl).trans ((Finset.subset_insert _ _).trans s₃)
        | some b => simp [Join] at hj; obtain ⟨rfl, rfl⟩ := hj; exact e₂ _ rfl
  | absurd hs => intro B _ _ _ _; exact ⟨B, .absurd hs, le_refl _, Finset.subset_union_left, by simp⟩
  | @copy Γ x x' b Δ hx hD _ ih =>
    intro B hn hb hΓ ha
    simp only [bnd, List.nodup_cons] at hn
    have hx' := hb x' (by simp [bnd])
    obtain ⟨B', l, s₁, s₂, e⟩ := ih (B := insert x' B) hn.2
      (fun z hz => ⟨by
        simp only [Finset.mem_insert, not_or]
        exact ⟨fun h => hn.1 (h ▸ hz), (hb z (by simp [bnd, hz])).1⟩,
        (hb z (by simp [bnd, hz])).2⟩)
      (Finset.insert_subset_insert _ hΓ) ha
    refine ⟨B', .copy hx hD hx'.1 hx'.2 l, (Finset.subset_insert _ _).trans s₁, ?_, e⟩
    refine s₂.trans ?_; intro z; simp [bnd] <;> tauto
  | @drop Γ x b Δ hx _ ih =>
    intro B hn hb hΓ ha
    obtain ⟨B', l, s₁, s₂, e⟩ := ih (B := B) hn hb ((Finset.erase_subset _ _).trans hΓ) ha
    exact ⟨B', .drop hx l, s₁, by simpa [bnd] using s₂, e⟩

end Backend2.Spike670
