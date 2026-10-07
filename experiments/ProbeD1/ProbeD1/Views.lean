import ProbeD1.Shared
import GhostEnd.Extend

/-!
# ProbeD1 — the stack a future gives: its views, its outermost lend, its reading substitution

The lemmas monotonicity at `U` turns on beyond the shared ones (DESIGN §4.3, `cbpv`: "a future's
views are its stack's, the inserted entries' flags off").

* **Drop flags at a future** (`futDs`). An entry the stack has keeps its flag; an entry a future
  inserted drops nothing. The flag is read by the entry's variable (`dsAt`), so it does not depend
  on how the future was reached, and a future of a future reads the flags the first future gave
  (`futDs_comp`).
* **The views are the stack's** (`vwS_fut`). An inserted entry with its flag off holds no view,
  and its place is new to the stack, so it shadows no kept entry (`vwS_insert`); a hidden entry's
  view does not read its row (`vwS_hide`).
* **The outermost lend** (`stratS_fut`): at a vector in nesting order, a share above the outermost
  lend is above every lend (`stratS_iff_all`), and a future's lifetimes are the stack's and inserted
  ones below the resource.
* **The reading substitution** (`extS_find_fut`): at a variable the future did not insert, the
  future's substitution reads what the stack's did.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace ProbeD1
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open GhostEnd (LEnt LStack LKind extS vwE vwS vis stratS ReLend)

/-! ### Variables and places along a future -/

theorem mem_take_x {σ : LStack} {k : Nat} {y : LifeVar} (h : y ∈ (σ.take k).map LEnt.x) :
    y ∈ σ.map LEnt.x := by
  rw [← List.take_append_drop k σ, List.map_append]; exact List.mem_append_left _ h

theorem mem_drop_x {σ : LStack} {k : Nat} {y : LifeVar} (h : y ∈ (σ.drop k).map LEnt.x) :
    y ∈ σ.map LEnt.x := by
  rw [← List.take_append_drop k σ, List.map_append]; exact List.mem_append_right _ h

theorem mem_drop_l {σ : LStack} {k : Nat} {l : BoCa.Loc} (h : l ∈ (σ.drop k).map LEnt.l) :
    l ∈ σ.map LEnt.l := by
  rw [← List.take_append_drop k σ, List.map_append]; exact List.mem_append_right _ h

/-- A step keeps every variable of the stack. -/
theorem FutStep.vars_mono {δ : LSub} {ρ : WRes} {s s' : Stk} (h : FutStep δ ρ s s') :
    ∀ y ∈ s.1.map LEnt.x, y ∈ s'.1.map LEnt.x := by
  obtain ⟨k, τ, αt, N, -, -, h₁, -⟩ := h
  intro y hy
  rw [h₁, futS_map_x]
  rw [← List.take_append_drop k s.1, List.map_append] at hy
  rcases List.mem_append.mp hy with hy | hy
  · exact List.mem_append_left _ (List.mem_append_left _ hy)
  · exact List.mem_append_right _ hy

/-- A future keeps every variable of the stack. -/
theorem Fut.vars_mono {δ : LSub} {ρ : WRes} {s s' : Stk} (h : Fut δ ρ s s') :
    ∀ y ∈ s.1.map LEnt.x, y ∈ s'.1.map LEnt.x := by
  induction h with
  | refl => exact fun _ h => h
  | tail _ hst ih => exact fun y hy => FutStep.vars_mono hst y (ih y hy)

/-! ### Drop flags at a future -/

/-- The drop flag of the entry of `σ` named `x`, `false` when `σ` has none. -/
def dsAt (σ : LStack) (ds : List Bool) (x : LifeVar) : Bool :=
  match (σ.zip ds).find? (fun p => p.1.x == x) with
  | some p => p.2
  | none => false

/-- **The drop flags at a future of the stack**: an entry the stack has keeps its flag, an entry
the future inserted drops nothing. -/
def futDs (σ : LStack) (ds : List Bool) (σ' : LStack) : List Bool := σ'.map fun e => dsAt σ ds e.x

theorem futDs_length (σ : LStack) (ds : List Bool) (σ' : LStack) :
    (futDs σ ds σ').length = σ'.length := List.length_map _

theorem dsAt_cons_self (e : LEnt) (σ : LStack) (d : Bool) (ds : List Bool) :
    dsAt (e :: σ) (d :: ds) e.x = d := by
  simp [dsAt, List.zip_cons_cons]

theorem dsAt_cons_ne {e : LEnt} {σ : LStack} {d : Bool} {ds : List Bool} {y : LifeVar}
    (h : e.x ≠ y) : dsAt (e :: σ) (d :: ds) y = dsAt σ ds y := by
  simp [dsAt, List.zip_cons_cons, h]

theorem dsAt_not_mem : ∀ {σ : LStack} {ds : List Bool} {y : LifeVar}, y ∉ σ.map LEnt.x →
    dsAt σ ds y = false
  | [], _, _, _ => by simp [dsAt]
  | _ :: _, [], _, _ => by simp [dsAt]
  | e :: σ, d :: ds, y, h => by
      have hne : e.x ≠ y := fun he => h (by simp [he])
      rw [dsAt_cons_ne hne]
      exact dsAt_not_mem (fun hm => h (List.mem_cons_of_mem _ hm))

/-- Reading a flag list made by variable from the same stack. -/
theorem dsAt_map (f : LifeVar → Bool) : ∀ (σ : LStack) (y : LifeVar),
    dsAt σ (σ.map fun e => f e.x) y = if y ∈ σ.map LEnt.x then f y else false
  | [], _ => by simp [dsAt]
  | e :: σ, y => by
      by_cases h : e.x = y
      · subst h
        rw [List.map_cons, dsAt_cons_self]
        simp
      · rw [List.map_cons, dsAt_cons_ne h, dsAt_map f σ y]
        by_cases hm : y ∈ σ.map LEnt.x
        · simp [hm]
        · have : y ∉ (e :: σ).map LEnt.x := by
            simp only [List.map_cons, List.mem_cons, not_or]; exact ⟨fun h' => h h'.symm, hm⟩
          rw [if_neg hm, if_neg this]

/-- At the stack itself the flags are the stack's own. -/
theorem futDs_self : ∀ {σ : LStack} {ds : List Bool}, (σ.map LEnt.x).Nodup →
    ds.length = σ.length → futDs σ ds σ = ds
  | [], [], _, _ => rfl
  | e :: σ, d :: ds, hn, hl => by
      have hn' : e.x ∉ σ.map LEnt.x ∧ (σ.map LEnt.x).Nodup :=
        List.nodup_cons.mp (by simpa only [List.map_cons] using hn)
      simp only [futDs, List.map_cons, dsAt_cons_self]
      congr 1
      have : σ.map (fun e' => dsAt (e :: σ) (d :: ds) e'.x) = σ.map (fun e' => dsAt σ ds e'.x) :=
        List.map_congr_left fun e' he' => dsAt_cons_ne (fun hx => hn'.1
          (List.mem_map.mpr ⟨e', he', hx.symm⟩))
      rw [this]
      exact futDs_self hn'.2 (by simpa using hl)
  | [], _ :: _, _, hl => absurd hl (by simp)
  | _ :: _, [], _, hl => absurd hl (by simp)

/-- **A future of a future reads the flags the first gave.** -/
theorem futDs_comp {σ σ₁ : LStack} (ds : List Bool) (hsub : ∀ y ∈ σ.map LEnt.x, y ∈ σ₁.map LEnt.x)
    (σ₂ : LStack) : futDs σ₁ (futDs σ ds σ₁) σ₂ = futDs σ ds σ₂ := by
  refine List.map_congr_left fun e _ => ?_
  rw [futDs, dsAt_map (fun y => dsAt σ ds y) σ₁ e.x]
  by_cases hm : e.x ∈ σ₁.map LEnt.x
  · rw [if_pos hm]
  · rw [if_neg hm]; exact (dsAt_not_mem fun h' => hm (hsub _ h')).symm

theorem futDs_hide {σ : LStack} {ds : List Bool} (N : UInt32 → Bool) (σ₂ : LStack) :
    futDs σ ds (hideS N σ₂) = futDs σ ds σ₂ := by
  simp [futDs, hideS, List.map_map, Function.comp_def]

/-- The flags one step gives: the inserted entries' off. -/
theorem futDs_futS {σ : LStack} {ds : List Bool} (hn : (σ.map LEnt.x).Nodup)
    (hl : ds.length = σ.length) {k : Nat} {τ : LStack} {N : Option (UInt32 → Bool)}
    (hτ : ∀ e ∈ τ, e.x ∉ σ.map LEnt.x) :
    futDs σ ds (futS k τ N σ) = ds.take k ++ List.replicate τ.length false ++ ds.drop k := by
  rw [futS_eq]
  have hout : futDs σ ds (outerS k N σ) = futDs σ ds (σ.drop k) := by
    cases N with
    | none => rfl
    | some N => exact futDs_hide N _
  have hτ' : futDs σ ds τ = List.replicate τ.length false := by
    rw [futDs, List.eq_replicate_iff]
    refine ⟨by simp, fun b hb => ?_⟩
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hb
    exact dsAt_not_mem (hτ e he)
  have hself := futDs_self hn hl
  have htake : futDs σ ds (σ.take k) = ds.take k := by
    rw [← congrArg (List.take k) hself, futDs, futDs, List.map_take]
  have hdrop : futDs σ ds (σ.drop k) = ds.drop k := by
    rw [← congrArg (List.drop k) hself, futDs, futDs, List.map_drop]
  simp only [futDs, List.map_append] at hout hτ' htake hdrop ⊢
  rw [hout, hτ', htake, hdrop]

/-! ### The views at a future -/

theorem emp_sep_eq (P : WProp) : (emp ⋆ P) = P := by
  funext ρ
  apply propext
  constructor
  · rintro ⟨ρ₁, ρ₂, hc, ⟨rfl, -⟩, hp⟩
    have := eq_of_compS_empty_left hc
    subst this
    exact hp
  · intro hp
    exact ⟨PMap.empty, ρ, compS_empty_left ρ, ⟨rfl, trivial⟩, hp⟩

/-- A hidden entry holds the view the entry does: views do not read rows. -/
theorem vwS_hide {δ : LSub} (N : UInt32 → Bool) : ∀ (seen : List BoCa.Loc) (σ : LStack)
    (ds : List Bool) (αs : List Life) (ls : List SRec),
    vwS δ seen (hideS N σ) ds αs ls = vwS δ seen σ ds αs ls
  | _, [], [], [], _ => rfl
  | _, [], [], _ :: _, _ => rfl
  | _, [], _ :: _, αs, _ => by cases αs <;> rfl
  | _, _ :: _, [], αs, _ => by cases αs <;> rfl
  | _, _ :: _, _ :: _, [], _ => rfl
  | seen, e :: σ, d :: ds, α :: αs, ls => by
      have ih := vwS_hide (δ := δ) N (e.l :: seen) σ ds αs ls
      simp only [hideS] at ih ⊢
      simp only [List.map_cons, vwS]
      rw [ih]
      rfl

/-- The views of a concatenation, the outer part hidden: as the outer part's own. -/
theorem vwS_append_hide {δ : LSub} (N : UInt32 → Bool) : ∀ (seen : List BoCa.Loc) (σ₁ σ₂ : LStack)
    (ds : List Bool) (αs : List Life) (ls : List SRec),
    vwS δ seen (σ₁ ++ hideS N σ₂) ds αs ls = vwS δ seen (σ₁ ++ σ₂) ds αs ls
  | seen, [], σ₂, ds, αs, ls => vwS_hide N seen σ₂ ds αs ls
  | _, _ :: _, _, [], αs, _ => by cases αs <;> rfl
  | _, _ :: _, _, _ :: _, [], _ => rfl
  | seen, e :: σ₁, σ₂, d :: ds, α :: αs, ls => by
      simp only [List.cons_append, vwS]
      rw [vwS_append_hide N (e.l :: seen) σ₁ σ₂ ds αs ls]

/-- **An inserted entry with its flag off holds no view, and shadows no kept entry**: its place is
new to the entries outside it. -/
theorem vwS_insert {δ : LSub} : ∀ (seen : List BoCa.Loc) (σ₁ τ σ₂ : LStack) (ds₁ ds₂ : List Bool)
    (αs₁ αt αs₂ : List Life) (ls : List SRec),
    ds₁.length = σ₁.length → αs₁.length = σ₁.length → αt.length = τ.length →
    (∀ e ∈ τ, e.l ∉ σ₂.map LEnt.l) →
    vwS δ seen (σ₁ ++ τ ++ σ₂) (ds₁ ++ List.replicate τ.length false ++ ds₂) (αs₁ ++ αt ++ αs₂) ls =
      vwS δ seen (σ₁ ++ σ₂) (ds₁ ++ ds₂) (αs₁ ++ αs₂) ls
  | seen, [], [], σ₂, [], ds₂, [], [], αs₂, ls, _, _, _, _ => rfl
  | seen, [], t :: τ, σ₂, [], ds₂, [], a :: αt, αs₂, ls, _, _, hlt, hτ => by
      have ih := vwS_insert (δ := δ) (t.l :: seen) [] τ σ₂ [] ds₂ [] αt αs₂ ls rfl rfl
        (by simpa using hlt) (fun e he => hτ e (List.mem_cons_of_mem _ he))
      simp only [List.nil_append, List.cons_append, List.length_cons, List.replicate_succ] at ih ⊢
      simp only [vwS]
      have hv : vis seen t false = false := by simp [vis]
      rw [hv, ih]
      show (emp ⋆ _) = _
      rw [emp_sep_eq]
      exact GhostEnd.vwS_seen_congr (fun e he => by
        simp only [List.mem_cons]
        refine ⟨fun h => h.elim (fun h' => absurd (h' ▸ List.mem_map_of_mem he) (hτ t List.mem_cons_self)) id,
          Or.inr⟩) ds₂ αs₂ ls
  | _, [], _ :: _, _, [], _, [], [], _, _, _, _, hlt, _ => absurd hlt (by simp)
  | _, [], [], _, [], _, [], _ :: _, _, _, _, _, hlt, _ => absurd hlt (by simp)
  | seen, e :: σ₁, τ, σ₂, d :: ds₁, ds₂, α :: αs₁, αt, αs₂, ls, hd, ha, hlt, hτ => by
      simp only [List.cons_append, vwS]
      rw [vwS_insert (e.l :: seen) σ₁ τ σ₂ ds₁ ds₂ αs₁ αt αs₂ ls (by simpa using hd)
        (by simpa using ha) hlt hτ]
  | _, [], _, _, _ :: _, _, _, _, _, _, hd, _, _, _ => absurd hd (by simp)
  | _, [], _, _, [], _, _ :: _, _, _, _, _, ha, _, _ => absurd ha (by simp)
  | _, _ :: _, _, _, [], _, _, _, _, _, hd, _, _, _ => absurd hd (by simp)
  | _, _ :: _, _, _, _ :: _, _, [], _, _, _, _, ha, _, _ => absurd ha (by simp)

/-- **One step's views are the stack's.** -/
theorem vwS_futStep {δ : LSub} {ρ : WRes} {σ σ' : LStack} {αs αs' : List Life}
    (hok : StackOK σ αs) (h : FutStep δ ρ (σ, αs) (σ', αs')) {ds : List Bool}
    (hl : ds.length = σ.length) (seen : List BoCa.Loc) (ls : List SRec) :
    vwS δ seen σ' (futDs σ ds σ') αs' ls = vwS δ seen σ ds αs ls := by
  obtain ⟨k, τ, αt, N, hf, -, h₁, h₂⟩ := h
  simp only at h₁ h₂
  subst h₁ h₂
  have hkσ : k ≤ σ.length := hf.depth_le
  rw [futDs_futS hok.2.2 hl hf.vars_stack, futL, futS_eq]
  have hplaces : ∀ e ∈ τ, e.l ∉ (outerS k N σ).map LEnt.l := fun e he hm =>
    hf.places e he (mem_drop_l (by rwa [outerS_map_l] at hm))
  rw [vwS_insert seen (σ.take k) τ (outerS k N σ) (ds.take k) (ds.drop k) (αs.take k) αt (αs.drop k) ls
    (by simp [List.length_take, hl]) (by simp [List.length_take, hok.1]) hf.len hplaces]
  have : vwS δ seen (σ.take k ++ outerS k N σ) (ds.take k ++ ds.drop k) (αs.take k ++ αs.drop k) ls =
      vwS δ seen (σ.take k ++ σ.drop k) (ds.take k ++ ds.drop k) (αs.take k ++ αs.drop k) ls := by
    cases N with
    | none => rfl
    | some N => exact vwS_append_hide N seen _ _ _ _ ls
  rw [this, List.take_append_drop, List.take_append_drop, List.take_append_drop]

/-- **A future's views are its stack's, the inserted entries' flags off.** -/
theorem vwS_fut {δ : LSub} {ρ : WRes} {σ σ' : LStack} {αs αs' : List Life}
    (hok : StackOK σ αs) (h : Fut δ ρ (σ, αs) (σ', αs')) {ds : List Bool}
    (hl : ds.length = σ.length) (seen : List BoCa.Loc) (ls : List SRec) :
    vwS δ seen σ' (futDs σ ds σ') αs' ls = vwS δ seen σ ds αs ls := by
  suffices H : ∀ s, Fut δ ρ (σ, αs) s → vwS δ seen s.1 (futDs σ ds s.1) s.2 ls = vwS δ seen σ ds αs ls
    from H _ h
  intro s hs
  induction hs with
  | refl => rw [futDs_self hok.2.2 hl]
  | @tail s₁ s₂ hs₁ hst ih =>
      have hok₁ : StackOK s₁.1 s₁.2 := Fut.stackOK (s := (σ, αs)) hok hs₁
      rw [← futDs_comp ds (Fut.vars_mono hs₁) s₂.1]
      rw [vwS_futStep (σ := s₁.1) (αs := s₁.2) hok₁ hst (futDs_length _ _ _) seen ls]
      exact ih

/-! ### The outermost lend at a future -/

theorem mem_le_last : ∀ {l : List Life}, List.IsChain (· < ·) l → ∀ a ∈ l, ∀ b ∈ l.getLast?, a ≤ b
  | [], _, a, ha, _, _ => absurd ha List.not_mem_nil
  | x :: xs, h, a, ha, b, hb => by
      rcases List.mem_cons.mp ha with rfl | ha
      · exact GhostEnd.head_le_last h b hb
      · cases xs with
        | nil => exact absurd ha List.not_mem_nil
        | cons y ys =>
            rw [List.getLast?_cons_cons] at hb
            exact mem_le_last (List.IsChain.tail h) a ha b hb

/-- **At a vector in nesting order, a share above the outermost lend is above every lend.** -/
theorem stratS_iff_all {αs : List Life} (hc : List.IsChain (· < ·) αs) {ρ : WRes} :
    stratS αs ρ ↔ ∀ a ∈ αs, ρ.InStratum a := by
  constructor
  · intro h a ha
    cases hl : αs.getLast? with
    | none => simp_all
    | some b => exact (h b hl).mono (mem_le_last hc a ha b hl)
  · intro h b hb
    exact h b (List.mem_of_getLast? hb)

/-- **A share above the outermost lend is above a future's**: the future's lifetimes are the
stack's and inserted ones below the holder's resource. -/
theorem stratS_fut {δ : LSub} {ρ : WRes} {s s' : Stk} (hok : StackOK s.1 s.2) (h : Fut δ ρ s s')
    (hz : stratS s.2 ρ) : stratS s'.2 ρ := by
  induction h with
  | refl => exact hz
  | @tail s₁ s₂ hs₁ hst ih =>
      have hok₁ := Fut.stackOK hok hs₁
      have hok₂ := FutStep.stackOK hok₁ hst
      obtain ⟨k, τ, αt, N, hf, -, -, h₂⟩ := hst
      rw [stratS_iff_all hok₂.2.1]
      rw [stratS_iff_all hok₁.2.1] at ih
      intro a ha
      rw [h₂, futL] at ha
      rcases List.mem_append.mp ha with ha | ha
      · rcases List.mem_append.mp ha with ha | ha
        · exact ih a (List.mem_of_mem_take ha)
        · exact hf.below a ha
      · exact ih a (List.mem_of_mem_drop ha)

/-! ### The reading substitution at a future -/

theorem extS_find_not_mem (δ : LSub) : ∀ (σ : LStack) (αs : List Life) (y : LifeVar),
    y ∉ σ.map LEnt.x → (extS δ σ αs).find? y = δ.find? y
  | [], _, _, _ => rfl
  | _ :: _, [], _, _ => rfl
  | e :: σ, α :: αs, y, h => by
      have hne : e.x ≠ y := fun he => h (by simp [he])
      simp only [extS]
      rw [find?_extend_ne _ _ hne]
      exact extS_find_not_mem δ σ αs y (fun hm => h (List.mem_cons_of_mem _ hm))

theorem extS_find_base {X X' : LSub} {y : LifeVar} (h : X.find? y = X'.find? y) :
    ∀ (σ : LStack) (αs : List Life), (extS X σ αs).find? y = (extS X' σ αs).find? y
  | [], _ => h
  | _ :: _, [] => h
  | e :: σ, α :: αs => by
      simp only [extS]
      by_cases hxy : e.x = y
      · subst hxy; rw [find?_extend_self, find?_extend_self]
      · rw [find?_extend_ne _ _ hxy, find?_extend_ne _ _ hxy]; exact extS_find_base h σ αs

theorem extS_append (δ : LSub) : ∀ (σ₁ σ₂ : LStack) (αs₁ αs₂ : List Life),
    αs₁.length = σ₁.length → extS δ (σ₁ ++ σ₂) (αs₁ ++ αs₂) = extS (extS δ σ₂ αs₂) σ₁ αs₁
  | [], _, [], _, _ => rfl
  | e :: σ₁, σ₂, α :: αs₁, αs₂, h => by
      simp only [List.cons_append, extS]
      rw [extS_append δ σ₁ σ₂ αs₁ αs₂ (by simpa using h)]
  | [], _, _ :: _, _, h => absurd h (by simp)
  | _ :: _, _, [], _, h => absurd h (by simp)

theorem extS_hideS (δ : LSub) (N : UInt32 → Bool) : ∀ (σ : LStack) (αs : List Life),
    extS δ (hideS N σ) αs = extS δ σ αs
  | [], _ => rfl
  | _ :: _, [] => rfl
  | e :: σ, α :: αs => by
      have ih := extS_hideS δ N σ αs
      simp only [hideS] at ih ⊢
      simp only [List.map_cons, extS, ih]

theorem extS_outerS (δ : LSub) (k : Nat) (N : Option (UInt32 → Bool)) (σ : LStack)
    (αs : List Life) : extS δ (outerS k N σ) αs = extS δ (σ.drop k) αs := by
  cases N with
  | none => rfl
  | some N => exact extS_hideS δ N _ αs

/-- **One step's substitution reads a variable it did not insert as the stack's did.** -/
theorem extS_find_futStep {δ : LSub} {ρ : WRes} {σ σ' : LStack} {αs αs' : List Life}
    (hok : StackOK σ αs) (h : FutStep δ ρ (σ, αs) (σ', αs')) {y : LifeVar}
    (hy : y ∈ σ'.map LEnt.x → y ∈ σ.map LEnt.x) :
    (extS δ σ' αs').find? y = (extS δ σ αs).find? y := by
  obtain ⟨k, τ, αt, N, hf, -, h₁, h₂⟩ := h
  simp only at h₁ h₂
  subst h₁ h₂
  have hkσ : k ≤ σ.length := hf.depth_le
  have hyτ : y ∉ τ.map LEnt.x := fun hm => by
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
    refine hf.vars_stack e he (hy ?_)
    rw [futS_map_x]
    exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem he))
  have hlt : (αs.take k).length = (σ.take k).length := by
    simp [List.length_take, hok.1]
  rw [futS_eq, futL, List.append_assoc, List.append_assoc,
    extS_append δ (σ.take k) (τ ++ outerS k N σ) (αs.take k) (αt ++ αs.drop k) hlt,
    extS_append δ τ (outerS k N σ) αt (αs.drop k) hf.len, extS_outerS]
  rw [extS_find_base (extS_find_not_mem _ τ αt y hyτ) (σ.take k) (αs.take k)]
  rw [← extS_append δ (σ.take k) (σ.drop k) (αs.take k) (αs.drop k) hlt,
    List.take_append_drop, List.take_append_drop]

/-- **A future's substitution reads a variable it did not insert as the stack's did.** -/
theorem extS_find_fut {δ : LSub} {ρ : WRes} {σ σ' : LStack} {αs αs' : List Life}
    (hok : StackOK σ αs) (h : Fut δ ρ (σ, αs) (σ', αs')) {y : LifeVar}
    (hy : y ∈ σ'.map LEnt.x → y ∈ σ.map LEnt.x) :
    (extS δ σ' αs').find? y = (extS δ σ αs).find? y := by
  suffices H : ∀ s, Fut δ ρ (σ, αs) s → (y ∈ s.1.map LEnt.x → y ∈ σ.map LEnt.x) →
      (extS δ s.1 s.2).find? y = (extS δ σ αs).find? y from H _ h hy
  intro s hs
  induction hs with
  | refl => exact fun _ => rfl
  | @tail s₁ s₂ hs₁ hst ih =>
      intro hy₂
      have hok₁ : StackOK s₁.1 s₁.2 := Fut.stackOK (s := (σ, αs)) hok hs₁
      have hy₁ : y ∈ s₁.1.map LEnt.x → y ∈ σ.map LEnt.x :=
        fun hm => hy₂ (FutStep.vars_mono hst y hm)
      rw [extS_find_futStep (σ := s₁.1) (αs := s₁.2) hok₁ hst
        (fun hm => Fut.vars_mono hs₁ y (hy₂ hm))]
      exact ih hy₁

end ProbeD1

end
