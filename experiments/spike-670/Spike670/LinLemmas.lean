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
