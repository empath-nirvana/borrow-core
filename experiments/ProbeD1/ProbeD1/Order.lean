import ProbeD1.Statement0

/-!
# ProbeD1 — W's order: the shared lemmas `ExtPreW`, `FutPart`, `FutAvoidsTrans`, `FutReLend`

Statement 0's shared lemmas about the order (DESIGN §4.1, §4.2).

* `extPreW`: `WP p`'s `Ext` is a preorder. Bookkeeping: `Ext` is reflexive and transitive
  (`Ext.refl`, `Ext.trans`) and a future is a reflexive–transitive closure.
* `futPart`: a future at a resource is a future at each part of it. A step reads its resource only
  at `FutOK.below`, and a part lies in every stratum its whole does
  (`ResU.CompS.inStratum_left`).
* `futAvoidsTrans`: an entry the composite inserted was inserted by one of the two futures, and
  each future's avoidance covers its own entries.
* `futReLend`: a re-lend of a future's lifetimes splits, step by step, into the re-lend of the
  kept lifetimes and the inserted ones (`ReLend` is pointwise and in nesting order, so a sublist of
  a re-lend is a re-lend), and the inserted ones stay below the resource
  (`ResU.InStratum.mono`).

The lemmas about the stack a future gives (`FutStep.stackOK`, the lengths) are stated here because
`futReLend` reads them.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace ProbeD1
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open GhostEnd (LEnt LStack LKind extS ReLend)

/-! ### `ExtPreW` -/

/-- **W's world order is a preorder.** -/
theorem extPreW (p : Placement) : ExtPreW (ℍ := ℍ) p :=
  ⟨fun i ρ => ⟨Ext.refl i.1 ρ, Relation.ReflTransGen.refl⟩,
    fun _ _ _ _ h₁ h₂ => ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩⟩

/-! ### `FutPart` -/

/-- One step at a resource is one step at each part of it. -/
theorem FutStep.part {δ : LSub} {ρz ρn ρ : WRes} (hc : ResU.CompS ρz ρn ρ) {s s' : Stk}
    (h : FutStep δ ρ s s') : FutStep δ ρz s s' := by
  obtain ⟨k, τ, αt, N, hok, hns, h₁, h₂⟩ := h
  exact ⟨k, τ, αt, N, { hok with below := fun a ha => ResU.CompS.inStratum_left hc (hok.below a ha) },
    hns, h₁, h₂⟩

/-- **A future at a resource is a future at each of its parts.** -/
theorem futPart : FutPart := fun _ _ _ _ _ _ hc h =>
  Relation.ReflTransGen.mono (fun _ _ h' => FutStep.part hc h') _ _ h

/-! ### `FutAvoidsTrans` -/

/-- **A composite future's inserted entries avoid a type when each step's do.** -/
theorem futAvoidsTrans : FutAvoidsTrans := by
  refine ⟨fun C σ σ' σ'' h₁ h₂ e he hx => ?_, fun A σ σ' σ'' h₁ h₂ e he hx => ?_⟩
  · by_cases hx' : e.x ∈ σ'.map LEnt.x
    · obtain ⟨e', he', hxe⟩ := List.mem_map.mp hx'
      rw [← hxe] at hx ⊢
      exact h₁ e' he' hx
    · exact h₂ e he hx'
  · by_cases hx' : e.x ∈ σ'.map LEnt.x
    · obtain ⟨e', he', hxe⟩ := List.mem_map.mp hx'
      rw [← hxe] at hx ⊢
      exact h₁ e' he' hx
    · exact h₂ e he hx'

/-! ### The stack a step gives -/

theorem hideS_map_x (N : UInt32 → Bool) (σ : LStack) : (hideS N σ).map LEnt.x = σ.map LEnt.x := by
  simp [hideS, List.map_map, Function.comp_def]

theorem hideS_map_l (N : UInt32 → Bool) (σ : LStack) : (hideS N σ).map LEnt.l = σ.map LEnt.l := by
  simp [hideS, List.map_map, Function.comp_def]

theorem hideS_length (N : UInt32 → Bool) (σ : LStack) : (hideS N σ).length = σ.length := by
  simp [hideS]

/-- The outer part of a step's stack, hidden or not. -/
def outerS (k : Nat) (N : Option (UInt32 → Bool)) (σ : LStack) : LStack :=
  match N with
  | none => σ.drop k
  | some N => hideS N (σ.drop k)

theorem futS_eq (k : Nat) (τ : LStack) (N : Option (UInt32 → Bool)) (σ : LStack) :
    futS k τ N σ = σ.take k ++ τ ++ outerS k N σ := by
  cases N <;> rfl

theorem outerS_map_x (k : Nat) (N : Option (UInt32 → Bool)) (σ : LStack) :
    (outerS k N σ).map LEnt.x = (σ.drop k).map LEnt.x := by
  cases N with
  | none => rfl
  | some N => exact hideS_map_x N _

theorem outerS_map_l (k : Nat) (N : Option (UInt32 → Bool)) (σ : LStack) :
    (outerS k N σ).map LEnt.l = (σ.drop k).map LEnt.l := by
  cases N with
  | none => rfl
  | some N => exact hideS_map_l N _

theorem outerS_length (k : Nat) (N : Option (UInt32 → Bool)) (σ : LStack) :
    (outerS k N σ).length = (σ.drop k).length := by
  cases N with
  | none => rfl
  | some N => exact hideS_length N _

theorem futS_length (k : Nat) (τ : LStack) (N : Option (UInt32 → Bool)) (σ : LStack) :
    (futS k τ N σ).length = σ.length + τ.length := by
  rw [futS_eq]
  simp only [List.length_append, outerS_length, List.length_take, List.length_drop]
  omega

theorem futL_length (k : Nat) (αt αs : List Life) :
    (futL k αt αs).length = αs.length + αt.length := by
  simp only [futL, List.length_append, List.length_take, List.length_drop]
  omega

/-- The variables of a step's stack: the inner part's, the inserted ones, the outer part's. -/
theorem futS_map_x (k : Nat) (τ : LStack) (N : Option (UInt32 → Bool)) (σ : LStack) :
    (futS k τ N σ).map LEnt.x = (σ.take k).map LEnt.x ++ τ.map LEnt.x ++ (σ.drop k).map LEnt.x := by
  rw [futS_eq]; simp only [List.map_append, outerS_map_x]

theorem futS_map_l (k : Nat) (τ : LStack) (N : Option (UInt32 → Bool)) (σ : LStack) :
    (futS k τ N σ).map LEnt.l = (σ.take k).map LEnt.l ++ τ.map LEnt.l ++ (σ.drop k).map LEnt.l := by
  rw [futS_eq]; simp only [List.map_append, outerS_map_l]

/-- A variable of the stack a step gives is the stack's or an inserted entry's. -/
theorem mem_futS_x {k : Nat} {τ : LStack} {N : Option (UInt32 → Bool)} {σ : LStack} {y : LifeVar}
    (h : y ∈ (futS k τ N σ).map LEnt.x) : y ∈ σ.map LEnt.x ∨ y ∈ τ.map LEnt.x := by
  rw [futS_map_x] at h
  rcases List.mem_append.mp h with h | h
  · rcases List.mem_append.mp h with h | h
    · exact Or.inl (by rw [← List.take_append_drop k σ, List.map_append]; exact List.mem_append_left _ h)
    · exact Or.inr h
  · exact Or.inl (by rw [← List.take_append_drop k σ, List.map_append]; exact List.mem_append_right _ h)

/-- **A step keeps the stack in shape.** -/
theorem FutStep.stackOK {δ : LSub} {ρ : WRes} {s s' : Stk} (hok : StackOK s.1 s.2)
    (h : FutStep δ ρ s s') : StackOK s'.1 s'.2 := by
  obtain ⟨k, τ, αt, N, hf, -, h₁, h₂⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [h₁, h₂, futS_length, futL_length, hok.1, hf.len]
  · rw [h₂]; exact hf.chain
  · rw [h₁, futS_map_x]
    have hσ : ((s.1.take k).map LEnt.x ++ (s.1.drop k).map LEnt.x).Nodup := by
      rw [← List.map_append, List.take_append_drop]; exact hok.2.2
    have hσ' := List.nodup_append.mp hσ
    have hτσ : ∀ a ∈ τ.map LEnt.x, a ∉ s.1.map LEnt.x := fun a ha => by
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
      exact hf.vars_stack e he
    have hin : ∀ a, a ∈ (s.1.take k).map LEnt.x → a ∈ s.1.map LEnt.x := fun a ha => by
      rw [← List.take_append_drop k s.1, List.map_append]; exact List.mem_append_left _ ha
    have hout : ∀ a, a ∈ (s.1.drop k).map LEnt.x → a ∈ s.1.map LEnt.x := fun a ha => by
      rw [← List.take_append_drop k s.1, List.map_append]; exact List.mem_append_right _ ha
    refine List.nodup_append.mpr ⟨List.nodup_append.mpr ⟨hσ'.1, hf.nodup, ?_⟩, hσ'.2.1, ?_⟩
    · intro a ha b hb hab
      subst hab
      exact hτσ a hb (hin a ha)
    · intro a ha b hb hab
      subst hab
      rcases List.mem_append.mp ha with ha | ha
      · exact hσ'.2.2 a ha a hb rfl
      · exact hτσ a ha (hout a hb)

/-- **A future keeps the stack in shape.** -/
theorem Fut.stackOK {δ : LSub} {ρ : WRes} {s s' : Stk} (hok : StackOK s.1 s.2)
    (h : Fut δ ρ s s') : StackOK s'.1 s'.2 := by
  induction h with
  | refl => exact hok
  | tail _ hst ih => exact FutStep.stackOK ih hst

/-! ### `FutReLend` -/

/-- Whether the reading substitution maps a variable depends only on the stack's variables and on
how many lifetimes there are. -/
theorem extS_find_none_iff (δ : LSub) : ∀ (σ : LStack) (αs₁ αs₂ : List Life),
    αs₁.length = αs₂.length → ∀ y : LifeVar,
      ((extS δ σ αs₁).find? y = none ↔ (extS δ σ αs₂).find? y = none)
  | [], [], [], _, _ => Iff.rfl
  | [], _ :: _, _ :: _, _, _ => Iff.rfl
  | _ :: _, [], [], _, _ => Iff.rfl
  | e :: σ, α₁ :: αs₁, α₂ :: αs₂, h, y => by
      simp only [extS, find?_extend_life]
      by_cases hxy : e.x = y
      · simp [hxy]
      · simp only [hxy]
        exact extS_find_none_iff δ σ αs₁ αs₂ (by simpa using h) y
  | [], [], _ :: _, h, _ => absurd h (by simp)
  | [], _ :: _, [], h, _ => absurd h (by simp)
  | _ :: _, [], _ :: _, h, _ => absurd h (by simp)
  | _ :: _, _ :: _, [], h, _ => absurd h (by simp)

theorem forall₂_le_mem {a b : List Life} (h : List.Forall₂ (· ≤ ·) a b) :
    ∀ x ∈ a, ∃ y ∈ b, x ≤ y := by
  induction h with
  | nil => intro x hx; exact absurd hx List.not_mem_nil
  | cons hxy _ ih =>
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨_, List.mem_cons_self, hxy⟩
      · obtain ⟨y, hy, hle⟩ := ih x hx
        exact ⟨y, List.mem_cons_of_mem _ hy, hle⟩

/-- **One step, re-lent, is a step from a re-lend.** The re-lend of the step's lifetimes splits into
the re-lend of the inner part, of the inserted lifetimes, and of the outer part. The inner and outer
parts re-lend the stack's lifetimes (a sublist of a chain is a chain), and the inserted ones stay
below the resource (`ResU.InStratum.mono`). -/
theorem FutStep.reLend {δ : LSub} {ρ : WRes} {σ σ' : LStack} {αs αs' αs'' : List Life}
    (hok : StackOK σ αs) (h : FutStep δ ρ (σ, αs) (σ', αs')) (hr : ReLend αs'' αs') :
    ∃ αs₀, ReLend αs₀ αs ∧ FutStep δ ρ (σ, αs₀) (σ', αs'') := by
  obtain ⟨k, τ, αt, N, hf, hns, h₁, h₂⟩ := h
  simp only at h₁ h₂
  subst h₁ h₂
  have hkσ : k ≤ σ.length := hf.depth_le
  have hk : (αs.take k).length = k := by rw [List.length_take, hok.1]; omega
  have hr₁ := List.forall₂_take_append αs'' (αs.take k ++ αt) (αs.drop k) hr.1
  have hr₂ := List.forall₂_drop_append αs'' (αs.take k ++ αt) (αs.drop k) hr.1
  have ha := List.forall₂_take_append _ (αs.take k) αt hr₁
  have hb := List.forall₂_drop_append _ (αs.take k) αt hr₁
  set m := (αs.take k ++ αt).length
  set a := (αs''.take m).take (αs.take k).length
  set b := (αs''.take m).drop (αs.take k).length
  set c := αs''.drop m
  have hsplit : αs'' = a ++ b ++ c := by
    simp only [a, b, c, List.take_append_drop]
  have hla : a.length = k := by rw [ha.length_eq, hk]
  have hlb : b.length = αt.length := hb.length_eq
  have hac_take : (a ++ c).take k = a := by rw [← hla]; exact List.take_left
  have hac_drop : (a ++ c).drop k = c := by rw [← hla]; exact List.drop_left
  have hfutL : futL k b (a ++ c) = αs'' := by
    rw [futL, hac_take, hac_drop, hsplit]
  have hlen₀ : (a ++ c).length = αs.length := by
    rw [List.length_append, hla, hr₂.length_eq, List.length_drop, hok.1]; omega
  refine ⟨a ++ c, ⟨?_, ?_⟩, ⟨k, τ, b, N, ?_, hns, rfl, ?_⟩⟩
  · have := List.rel_append ha hr₂
    simp only at this
    rwa [List.take_append_drop] at this
  · have hc := hr.2
    rw [hsplit, List.append_assoc] at hc
    exact hc.sublist ((List.sublist_append_right b c).append_left a)
  · refine
      { len := hlb.trans hf.len
        depth_le := hkσ
        chain := by rw [hfutL]; exact hr.2
        below := fun x hx => by
          obtain ⟨y, hy, hle⟩ := forall₂_le_mem hb x hx
          exact (hf.below y hy).mono hle
        vars_stack := hf.vars_stack
        vars_sub := fun e he =>
          (extS_find_none_iff δ σ (a ++ c) αs hlen₀ e.x).mpr (hf.vars_sub e he)
        nodup := hf.nodup
        places := hf.places
        pay := fun e he y hy hn => hf.pay e he y hy
          ((extS_find_none_iff δ _ (futL k b (a ++ c)) (futL k αt αs)
            (by rw [futL_length, futL_length, hlen₀, hlb]) y).mp hn) }
  · exact hfutL.symm

/-- **A re-lend of a future is a future of a re-lend.** By induction on the future, one step at a
time from its end (`FutStep.reLend`), the stack kept in shape along it (`FutStep.stackOK`). -/
theorem futReLend : FutReLend := by
  intro δ ρ σ σ' αs αs' αs'' hok h hr
  suffices H : ∀ s', Fut δ ρ (σ, αs) s' → ∀ αs'', ReLend αs'' s'.2 →
      ∃ αs₀, ReLend αs₀ αs ∧ Fut δ ρ (σ, αs₀) (s'.1, αs'') from H _ h αs'' hr
  intro s' hs
  induction hs with
  | refl => exact fun αs'' hr => ⟨αs'', hr, Relation.ReflTransGen.refl⟩
  | @tail s₁ s₂ hs₁ hst ih =>
      intro αs₂ hr₂
      have hok₁ : StackOK s₁.1 s₁.2 := Fut.stackOK (s := (σ, αs)) hok hs₁
      obtain ⟨αs₁, hr₁, hst'⟩ := FutStep.reLend (σ := s₁.1) (αs := s₁.2) hok₁ hst hr₂
      obtain ⟨αs₀, hr₀, hfut⟩ := ih αs₁ hr₁
      exact ⟨αs₀, hr₀, hfut.tail hst'⟩

end ProbeD1

end
