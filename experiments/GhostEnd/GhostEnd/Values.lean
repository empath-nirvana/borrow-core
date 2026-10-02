import GhostEnd.Descend

/-!
# GhostEnd — values carrying the lend across a stop (#262, item 2)

A frame spanning a stop may hold the lend inside a value: `z : Mut 'x T ⊗ D`, a sum of such, or
`m` itself. `StopSafe` (`Typed.lean`) admits only slots free of `'x`. This file freezes and
thaws the values of the types `LOk` admits:

    A ::= Mut 'x T | A ⊗ A | A ⊕ A | A₀        (A₀ free of 'x, outliving it)

**Freeze, by induction on the type** (`fzV_freeze`). At a lend `α`, with the resource consistent
with the table (`TabAt ℓ α`):

1. `A₀`: the value stays as it is. Its resource is in `Res_α` by 6.60 (`vC_outlives`).
2. `Mut 'x T` at `ℓ′`. The relation holds a cell at a lifetime `⊒ α`.
   * If `ℓ′ = ℓ`, the cell is the lend's. It is dropped (`dropC`), and the value is recorded as
     "the view at `ℓ`".
   * If `ℓ′ ≠ ℓ`, the table puts the cell strictly above `α`: it is a view of an outer cell, kept.
3. `⊗` and `⊕`: by parts. Two parts cannot both drop a cell, since both would be `mut` at `ℓ`
   (`dropC_disj`).

**Thaw** (`fzV_thaw`). At a later lend `α′ ⊑ α`, the re-lend hands `ℓ ↦ M_{α′}`.

* A dropped position takes it: `𝒱⟦Mut 'x T⟧_{δ[x ↦ α′]}(ℓ)` is that cell (`mutView`).
* A kept `Mut 'x T` position is a view of a cell above `α`, and it is a view at `α′` by M Vary
  (`vC_mut_vary`).
* An `A₀` position does not see `'x` (`vC_extend_of_not_free`).

The re-lend produces the cell for the one location the table records at `α`. That is
`restrat_segment`'s renaming of `'x` at the value, keyed by the lifetime as the renaming is. The
thawed resource is consistent with the table at `α′` (`tabAt_view`, `tabAt_of_inStratum`).

`lok_thaws` lifts this to a frame, which is `FrameThawsD`. `stopSafe_lok` shows it subsumes
`StopSafe`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace GhostEnd
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- The types of values that may carry the lend `m : Mut 'x T` across a stop: `Mut 'x T`, `⊗`
and `⊕` of such, and types free of `'x` that outlive it. -/
def LOk (Δ : LifeCtx) (x : LifeVar) (b : Lifetime.Life) (T : VTy) : VTy → Prop
  | .tensor A B => LOk Δ x b T A ∧ LOk Δ x b T B
  | .sum A B => LOk Δ x b T A ∧ LOk Δ x b T B
  | A => A = .mut (.var x) T ∨ (¬ VFree x A ∧ VOutlives (Δ.extend x b) (.var x) A)

/-- A value of a type that is neither `⊗` nor `⊕`, frozen at the lend `α`: the view at `ℓ`,
dropped (`d`), or the value as it stands, in `Res_α`. -/
def fzAtom (x : LifeVar) (T : VTy) (δ : LSub) (l : BoCa.Loc) (α : Life) (A : VTy)
    (ls : List SRec) (v : Val) (d : Bool) : WProp := fun ρ =>
  (d = true ∧ A = .mut (.var x) T ∧ v = Val.loc l ∧ ρ = PMap.empty) ∨
    (d = false ∧ vC true A ls (δ.extend x α) v ρ ∧ ρ.InStratum α)

/-- **A value frozen at the lend `α`**, by its type. `d` records whether a cell was dropped. -/
def fzV (x : LifeVar) (T : VTy) (δ : LSub) (l : BoCa.Loc) (α : Life) :
    VTy → List SRec → Val → Bool → WProp
  | .tensor A B, ls, v, d => fun ρ => ∃ v₁ v₂ d₁ d₂, v = .pair v₁ v₂ ∧ d = (d₁ || d₂) ∧
      ¬ (d₁ = true ∧ d₂ = true) ∧ (fzV x T δ l α A ls v₁ d₁ ⋆ fzV x T δ l α B ls v₂ d₂) ρ
  | .sum A B, ls, v, d => fun ρ => (∃ v₁, v = .inj₁ v₁ ∧ fzV x T δ l α A ls v₁ d ρ) ∨
      (∃ v₂, v = .inj₂ v₂ ∧ fzV x T δ l α B ls v₂ d ρ)
  | A, ls, v, d => fzAtom x T δ l α A ls v d

section
variable {Δ : LifeCtx} {x : LifeVar} {b : Lifetime.Life} {T : VTy} {δ : LSub} {l : BoCa.Loc}

/-- A free type that outlives `'x` is `LOk`. -/
theorem lok_of_free : ∀ (A : VTy), ¬ VFree x A → VOutlives (Δ.extend x b) (.var x) A →
    LOk Δ x b T A := by
  intro A
  cases A with
  | tensor A B =>
      intro hf ho
      cases ho with
      | tensor hA hB =>
          exact ⟨lok_of_free A (fun h => hf (Or.inl h)) hA, lok_of_free B (fun h => hf (Or.inr h)) hB⟩
  | sum A B =>
      intro hf ho
      cases ho with
      | sum hA hB =>
          exact ⟨lok_of_free A (fun h => hf (Or.inl h)) hA, lok_of_free B (fun h => hf (Or.inr h)) hB⟩
  | _ => intro hf ho; exact Or.inr ⟨hf, ho⟩

/-- A frozen atom is in `Res_α`. -/
theorem fzAtom_inStratum {α : Life} {A : VTy} {ls : List SRec} {v : Val} {d : Bool} {ρ : WRes}
    (h : fzAtom x T δ l α A ls v d ρ) : ρ.InStratum α := by
  rcases h with ⟨-, -, -, rfl⟩ | ⟨-, -, h⟩
  · exact ResU.inStratum_empty α
  · exact h

/-- A frozen value is in `Res_α`. -/
theorem fzV_inStratum {α : Life} : ∀ (A : VTy) {ls : List SRec} {v : Val} {d : Bool} {ρ : WRes},
    fzV x T δ l α A ls v d ρ → ρ.InStratum α := by
  intro A
  cases A with
  | tensor A B =>
      rintro ls v d ρ ⟨v₁, v₂, d₁, d₂, -, -, -, ρ₁, ρ₂, hc, h₁, h₂⟩
      exact (outlives_comp hc α).mpr ⟨fzV_inStratum A h₁, fzV_inStratum B h₂⟩
  | sum A B =>
      rintro ls v d ρ (⟨v₁, -, h⟩ | ⟨v₂, -, h⟩)
      · exact fzV_inStratum A h
      · exact fzV_inStratum B h
  | _ => intro ls v d ρ h; exact fzAtom_inStratum h

/-- A frozen value is Kripke along `Ext`. -/
theorem fzV_local {α : Life} : ∀ (A : VTy) {ls ls' : List SRec} {v : Val} {d : Bool}
    {ρ : WRes}, Ext ls ls' ρ → fzV x T δ l α A ls v d ρ → fzV x T δ l α A ls' v d ρ := by
  intro A
  cases A with
  | tensor A B =>
      rintro ls ls' v d ρ he ⟨v₁, v₂, d₁, d₂, hv, hd, hnd, ρ₁, ρ₂, hc, h₁, h₂⟩
      exact ⟨v₁, v₂, d₁, d₂, hv, hd, hnd, ρ₁, ρ₂, hc, fzV_local A (he.left hc) h₁,
        fzV_local B (he.right hc) h₂⟩
  | sum A B =>
      rintro ls ls' v d ρ he (⟨v₁, hv, h⟩ | ⟨v₂, hv, h⟩)
      · exact Or.inl ⟨v₁, hv, fzV_local A he h⟩
      · exact Or.inr ⟨v₂, hv, fzV_local B he h⟩
  | _ =>
      rintro ls ls' v d ρ he (h | ⟨hd, hv, hs⟩)
      · exact Or.inl h
      · exact Or.inr ⟨hd, vC_local true _ he hv, hs⟩

/-- **Freeze an atom** at the lend `α`. -/
theorem fzAtom_freeze {α : Life} (hδα : (Δ.extend x b).Models (δ.extend x α)) {A : VTy}
    (hA : A = .mut (.var x) T ∨ (¬ VFree x A ∧ VOutlives (Δ.extend x b) (.var x) A))
    {ls : List SRec} {v : Val} {ρ : WRes} (hv : vC true A ls (δ.extend x α) v ρ)
    (ht : TabAt l α ρ) :
    ∃ d ρz ρn, ResU.CompS ρz ρn ρ ∧ fzAtom x T δ l α A ls v d ρz ∧ dropC l d ρn := by
  rcases hA with rfl | ⟨-, ho⟩
  · have hv₀ := hv
    obtain ⟨α₀, hα₀, l', hs⟩ := hv
    rw [interp_ext_self] at hα₀
    cases Option.some.inj hα₀
    obtain ⟨rfl, hm⟩ := pure_sep_iff.mp hs
    obtain ⟨b', u, σ, hσ, Q, hw, ls₀, -, rfl, -⟩ := hm
    by_cases hl : l' = l
    · subst hl
      exact ⟨true, PMap.empty, _, compS_empty_left _, Or.inl ⟨rfl, rfl, rfl, rfl⟩, _, rfl, rfl⟩
    · refine ⟨false, _, PMap.empty, ResU.comp_empty_right _, Or.inr ⟨rfl, hv₀, ?_⟩,
        rfl, trivial⟩
      intro k ψ e
      by_cases hk : k = l'
      · subst hk
        exact ht.2 k ψ hl e
      · rw [ResU.single_get_ne _ hk] at e; exact absurd e (by simp)
  · refine ⟨false, ρ, PMap.empty, ResU.comp_empty_right ρ, Or.inr ⟨rfl, hv, ?_⟩, rfl, trivial⟩
    exact vC_outlives hδα (interp_ext_self δ x α) ho true ls v ρ hv

/-- **Freeze a value** at the lend `α`, by induction on its type: a part in `Res_α`, and the cell
at `ℓ` if the value holds the lend's. -/
theorem fzV_freeze {α : Life} (hδα : (Δ.extend x b).Models (δ.extend x α)) :
    ∀ (A : VTy), LOk Δ x b T A → ∀ {ls : List SRec} {v : Val} {ρ : WRes},
      vC true A ls (δ.extend x α) v ρ → TabAt l α ρ →
      ∃ d ρz ρn, ResU.CompS ρz ρn ρ ∧ fzV x T δ l α A ls v d ρz ∧ dropC l d ρn := by
  intro A
  cases A with
  | tensor A B =>
      rintro ⟨hA, hB⟩ ls v ρ ⟨v₁, v₂, hs⟩ ht
      obtain ⟨rfl, ρ₁, ρ₂, hc, h₁, h₂⟩ := pure_sep_iff.mp hs
      obtain ⟨ht₁, ht₂⟩ := (tabAt_comp hc).mp ht
      obtain ⟨d₁, ρz₁, ρn₁, hc₁, hz₁, hn₁⟩ := fzV_freeze hδα A hA h₁ ht₁
      obtain ⟨d₂, ρz₂, ρn₂, hc₂, hz₂, hn₂⟩ := fzV_freeze hδα B hB h₂ ht₂
      have hnd : ¬ (d₁ = true ∧ d₂ = true) := by
        rintro ⟨rfl, rfl⟩
        exact dropC_disj hn₁ hn₂ (ResU.CompS.comm hc₁) (ResU.CompS.comm hc₂) hc
      obtain ⟨ρz, ρn, hcz, hcn, hcρ⟩ := compS_four hc₁ hc₂ hc
      exact ⟨d₁ || d₂, ρz, ρn, hcρ, ⟨v₁, v₂, d₁, d₂, rfl, rfl, hnd, ρz₁, ρz₂, hcz, hz₁, hz₂⟩,
        dropC_join hnd hn₁ hn₂ hcn⟩
  | sum A B =>
      rintro ⟨hA, hB⟩ ls v ρ (⟨v₁, hs⟩ | ⟨v₂, hs⟩) ht
      · obtain ⟨rfl, h⟩ := pure_sep_iff.mp hs
        obtain ⟨d, ρz, ρn, hc, hz, hn⟩ := fzV_freeze hδα A hA h ht
        exact ⟨d, ρz, ρn, hc, Or.inl ⟨v₁, rfl, hz⟩, hn⟩
      · obtain ⟨rfl, h⟩ := pure_sep_iff.mp hs
        obtain ⟨d, ρz, ρn, hc, hz, hn⟩ := fzV_freeze hδα B hB h ht
        exact ⟨d, ρz, ρn, hc, Or.inr ⟨v₂, rfl, hz⟩, hn⟩
  | _ => intro hA ls v ρ hv ht; exact fzAtom_freeze hδα hA hv ht

/-- **Thaw an atom** at a later lend `α′ ⊑ α`, handed the view if it dropped one. -/
theorem fzAtom_thaw (hT : ¬ VFree x T) {α α' : Life} (hle : α' ≤ α) {A : VTy}
    (hA : A = .mut (.var x) T ∨ (¬ VFree x A ∧ VOutlives (Δ.extend x b) (.var x) A))
    {ls : List SRec} {v : Val} {d : Bool} {ρz ρv ρ : WRes}
    (hz : fzAtom x T δ l α A ls v d ρz) (hv : vwD l T δ d α' ls ρv)
    (hc : ResU.CompS ρz ρv ρ) :
    vC true A ls (δ.extend x α') v ρ ∧ TabAt l α' ρ := by
  rcases hz with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, hvz, hs⟩
  · obtain rfl := eq_of_compS_empty_left hc
    exact ⟨mutView hT hv, tabAt_view hv⟩
  · obtain ⟨rfl, -⟩ := hv
    obtain rfl := ResU.CompS.functional hc (ResU.comp_empty_right ρz)
    refine ⟨?_, tabAt_of_inStratum (hs.mono hle)⟩
    rcases hA with rfl | ⟨hf, -⟩
    · exact vC_mut_vary hT hle hvz
    · rw [vC_extend_of_not_free hf] at hvz ⊢; exact hvz

/-- **Thaw a value** at a later lend `α′ ⊑ α`: the view handed goes to the position that dropped
the cell, kept views hold at `α′` by M Vary, and the rest does not see `'x`. -/
theorem fzV_thaw (hT : ¬ VFree x T) {α α' : Life} (hle : α' ≤ α) :
    ∀ (A : VTy), LOk Δ x b T A → ∀ {ls : List SRec} {v : Val} {d : Bool} {ρz ρv ρ : WRes},
      fzV x T δ l α A ls v d ρz → vwD l T δ d α' ls ρv → ResU.CompS ρz ρv ρ →
      vC true A ls (δ.extend x α') v ρ ∧ TabAt l α' ρ := by
  intro A
  cases A with
  | tensor A B =>
      rintro ⟨hA, hB⟩ ls v d ρz ρv ρ ⟨v₁, v₂, d₁, d₂, rfl, rfl, hnd, ρz₁, ρz₂, hcz, h₁, h₂⟩ hv hc
      -- the view goes to the part that dropped the cell
      have key : ∃ ρ₁ ρ₂, ResU.CompS ρ₁ ρ₂ ρ ∧
          (vC true A ls (δ.extend x α') v₁ ρ₁ ∧ TabAt l α' ρ₁) ∧
          (vC true B ls (δ.extend x α') v₂ ρ₂ ∧ TabAt l α' ρ₂) := by
        cases d₁ with
        | true =>
            obtain rfl : d₂ = false := by cases d₂ <;> simp_all
            obtain ⟨y, hy, hcy⟩ := compS_exch hcz hc
            exact ⟨y, ρz₂, hcy, fzV_thaw hT hle A hA h₁ hv hy,
              fzV_thaw hT hle B hB h₂ ⟨rfl, trivial⟩ (ResU.comp_empty_right ρz₂)⟩
        | false =>
            obtain ⟨y, hy, hcy⟩ := compS_reassoc hcz hc
            exact ⟨ρz₁, y, hcy, fzV_thaw hT hle A hA h₁ ⟨rfl, trivial⟩ (ResU.comp_empty_right ρz₁),
              fzV_thaw hT hle B hB h₂ (by simpa using hv) hy⟩
      obtain ⟨ρ₁, ρ₂, hc', ⟨hv₁, ht₁⟩, ⟨hv₂, ht₂⟩⟩ := key
      exact ⟨⟨v₁, v₂, pure_sep_mk rfl ⟨ρ₁, ρ₂, hc', hv₁, hv₂⟩⟩, (tabAt_comp hc').mpr ⟨ht₁, ht₂⟩⟩
  | sum A B =>
      rintro ⟨hA, hB⟩ ls v d ρz ρv ρ (⟨v₁, rfl, h⟩ | ⟨v₂, rfl, h⟩) hv hc
      · obtain ⟨h', ht⟩ := fzV_thaw hT hle A hA h hv hc
        exact ⟨Or.inl ⟨v₁, pure_sep_mk rfl h'⟩, ht⟩
      · obtain ⟨h', ht⟩ := fzV_thaw hT hle B hB h hv hc
        exact ⟨Or.inr ⟨v₂, pure_sep_mk rfl h'⟩, ht⟩
  | _ => intro hA ls v d ρz ρv ρ hz hv hc; exact fzAtom_thaw hT hle hA hz hv hc

end

/-! ### Frames -/

/-- A frame frozen at the lend `α`, slot by slot as `gSepC` reads it. -/
def fzG (x : LifeVar) (T : VTy) (δ : LSub) (l : BoCa.Loc) (α : Life) :
    Ctx VTy → List Val → List SRec → Bool → WProp
  | [], _, _, d => fun ρ => d = false ∧ ρ = PMap.empty
  | _ :: _, [], _, d => fun ρ => d = false ∧ ρ = PMap.empty
  | s :: Γ, v :: γ, ls, d =>
      if s.live then fun ρ => ∃ d₁ d₂, d = (d₁ || d₂) ∧ ¬ (d₁ = true ∧ d₂ = true) ∧
        (fzV x T δ l α s.ty ls v d₁ ⋆ fzG x T δ l α Γ γ ls d₂) ρ
      else fzG x T δ l α Γ γ ls d

section
variable {Δ : LifeCtx} {x : LifeVar} {b : Lifetime.Life} {T : VTy} {δ : LSub} {l : BoCa.Loc}

theorem fzG_inStratum {α : Life} : ∀ (Γ : Ctx VTy) (γ : List Val) {ls : List SRec} {d : Bool}
    {ρ : WRes}, fzG x T δ l α Γ γ ls d ρ → ρ.InStratum α
  | [], _, _, _, _, h => by rw [h.2]; exact ResU.inStratum_empty α
  | _ :: _, [], _, _, _, h => by rw [h.2]; exact ResU.inStratum_empty α
  | s :: Γ, v :: γ, ls, d, ρ, h => by
      by_cases hs : s.live = true
      · simp only [fzG, hs, if_true] at h
        obtain ⟨d₁, d₂, -, -, ρ₁, ρ₂, hc, h₁, h₂⟩ := h
        exact (outlives_comp hc α).mpr ⟨fzV_inStratum _ h₁, fzG_inStratum Γ γ h₂⟩
      · simp only [fzG, hs] at h
        exact fzG_inStratum Γ γ h

theorem fzG_local {α : Life} : ∀ (Γ : Ctx VTy) (γ : List Val) {ls ls' : List SRec} {d : Bool}
    {ρ : WRes}, Ext ls ls' ρ → fzG x T δ l α Γ γ ls d ρ → fzG x T δ l α Γ γ ls' d ρ
  | [], _, _, _, _, _, _, h => h
  | _ :: _, [], _, _, _, _, _, h => h
  | s :: Γ, v :: γ, ls, ls', d, ρ, he, h => by
      by_cases hs : s.live = true
      · simp only [fzG, hs, if_true] at h ⊢
        obtain ⟨d₁, d₂, hd, hnd, ρ₁, ρ₂, hc, h₁, h₂⟩ := h
        exact ⟨d₁, d₂, hd, hnd, ρ₁, ρ₂, hc, fzV_local _ (he.left hc) h₁,
          fzG_local Γ γ (he.right hc) h₂⟩
      · simp only [fzG, hs] at h ⊢
        exact fzG_local Γ γ he h

/-- **Freeze a frame**, slot by slot. -/
theorem fzG_freeze {α : Life} (hδα : (Δ.extend x b).Models (δ.extend x α)) :
    ∀ (Γ : Ctx VTy), (∀ s ∈ Γ, s.live = true → LOk Δ x b T s.ty) → ∀ (γ : List Val)
      {ls : List SRec} {ρ : WRes}, gSepC ls (δ.extend x α) Γ γ ρ → TabAt l α ρ →
      ∃ d ρz ρn, ResU.CompS ρz ρn ρ ∧ fzG x T δ l α Γ γ ls d ρz ∧ dropC l d ρn
  | [], _, _, _, ρ, h, _ => by
      obtain ⟨rfl, -⟩ := h
      exact ⟨false, PMap.empty, PMap.empty, compS_empty_left _, ⟨rfl, rfl⟩, rfl, trivial⟩
  | _ :: _, _, [], _, ρ, h, _ => by
      obtain ⟨rfl, -⟩ := h
      exact ⟨false, PMap.empty, PMap.empty, compS_empty_left _, ⟨rfl, rfl⟩, rfl, trivial⟩
  | s :: Γ, hok, v :: γ, ls, ρ, h, ht => by
      have hok' : ∀ s' ∈ Γ, s'.live = true → LOk Δ x b T s'.ty :=
        fun s' hm hl => hok s' (List.mem_cons_of_mem _ hm) hl
      by_cases hs : s.live = true
      · simp only [gSepC, hs, if_true] at h
        obtain ⟨ρ₁, ρ₂, hc, h₁, h₂⟩ := h
        obtain ⟨ht₁, ht₂⟩ := (tabAt_comp hc).mp ht
        obtain ⟨d₁, ρz₁, ρn₁, hc₁, hz₁, hn₁⟩ :=
          fzV_freeze hδα s.ty (hok s List.mem_cons_self hs) h₁ ht₁
        obtain ⟨d₂, ρz₂, ρn₂, hc₂, hz₂, hn₂⟩ := fzG_freeze hδα Γ hok' γ h₂ ht₂
        have hnd : ¬ (d₁ = true ∧ d₂ = true) := by
          rintro ⟨rfl, rfl⟩
          exact dropC_disj hn₁ hn₂ (ResU.CompS.comm hc₁) (ResU.CompS.comm hc₂) hc
        obtain ⟨ρz, ρn, hcz, hcn, hcρ⟩ := compS_four hc₁ hc₂ hc
        refine ⟨d₁ || d₂, ρz, ρn, hcρ, ?_, dropC_join hnd hn₁ hn₂ hcn⟩
        simp only [fzG, hs, if_true]
        exact ⟨d₁, d₂, rfl, hnd, ρz₁, ρz₂, hcz, hz₁, hz₂⟩
      · simp only [gSepC, hs] at h
        simp only [fzG, hs]
        exact fzG_freeze hδα Γ hok' γ h ht

/-- **Thaw a frame** at a later lend `α′ ⊑ α`. -/
theorem fzG_thaw (hT : ¬ VFree x T) {α α' : Life} (hle : α' ≤ α) :
    ∀ (Γ : Ctx VTy), (∀ s ∈ Γ, s.live = true → LOk Δ x b T s.ty) → ∀ (γ : List Val)
      {ls : List SRec} {d : Bool} {ρz ρv ρ : WRes}, fzG x T δ l α Γ γ ls d ρz →
      vwD l T δ d α' ls ρv → ResU.CompS ρz ρv ρ →
      gSepC ls (δ.extend x α') Γ γ ρ ∧ TabAt l α' ρ
  | [], _, _, ls, d, ρz, ρv, ρ, h, hv, hc => by
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨rfl, -⟩ := hv
      obtain rfl := eq_of_compS_empty_left hc
      exact ⟨⟨rfl, trivial⟩, tabAt_empty l α'⟩
  | _ :: _, _, [], ls, d, ρz, ρv, ρ, h, hv, hc => by
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨rfl, -⟩ := hv
      obtain rfl := eq_of_compS_empty_left hc
      exact ⟨⟨rfl, trivial⟩, tabAt_empty l α'⟩
  | s :: Γ, hok, v :: γ, ls, d, ρz, ρv, ρ, h, hv, hc => by
      have hok' : ∀ s' ∈ Γ, s'.live = true → LOk Δ x b T s'.ty :=
        fun s' hm hl => hok s' (List.mem_cons_of_mem _ hm) hl
      by_cases hs : s.live = true
      · simp only [fzG, hs, if_true] at h
        simp only [gSepC, hs, if_true]
        obtain ⟨d₁, d₂, rfl, hnd, ρz₁, ρz₂, hcz, h₁, h₂⟩ := h
        have hok₁ := hok s List.mem_cons_self hs
        have key : ∃ ρ₁ ρ₂, ResU.CompS ρ₁ ρ₂ ρ ∧
            (vC true s.ty ls (δ.extend x α') v ρ₁ ∧ TabAt l α' ρ₁) ∧
            (gSepC ls (δ.extend x α') Γ γ ρ₂ ∧ TabAt l α' ρ₂) := by
          cases d₁ with
          | true =>
              obtain rfl : d₂ = false := by cases d₂ <;> simp_all
              obtain ⟨y, hy, hcy⟩ := compS_exch hcz hc
              exact ⟨y, ρz₂, hcy, fzV_thaw hT hle s.ty hok₁ h₁ hv hy,
                fzG_thaw hT hle Γ hok' γ h₂ ⟨rfl, trivial⟩ (ResU.comp_empty_right ρz₂)⟩
          | false =>
              obtain ⟨y, hy, hcy⟩ := compS_reassoc hcz hc
              exact ⟨ρz₁, y, hcy,
                fzV_thaw hT hle s.ty hok₁ h₁ ⟨rfl, trivial⟩ (ResU.comp_empty_right ρz₁),
                fzG_thaw hT hle Γ hok' γ h₂ (by simpa using hv) hy⟩
        obtain ⟨ρ₁, ρ₂, hc', ⟨hv₁, ht₁⟩, ⟨hv₂, ht₂⟩⟩ := key
        exact ⟨⟨ρ₁, ρ₂, hc', hv₁, hv₂⟩, (tabAt_comp hc').mpr ⟨ht₁, ht₂⟩⟩
      · simp only [fzG, hs] at h
        simp only [gSepC, hs]
        exact fzG_thaw hT hle Γ hok' γ h hv hc

end

/-! ### A frame spanning a stop -/

/-- **A frame that spans a stop thaws at a later lend**, with the table. For each closing
substitution a frozen form `Fz α d` exists: Kripke along `Ext`, in `Res_α`. The frame at a lend
`α ⊏ @bδ`, consistent with the table, freezes to it and what it drops. The frozen frame, handed
the view at a later lend `α′ ⊏ α` if it dropped a cell, is the frame at `α′`, consistent with the
table there. This is `FrameThaws` with the dropped cell reported, the table assumed and kept,
and each lend below the last. -/
def FrameThawsD (Δ : LifeCtx) (x : LifeVar) (b : Lifetime.Life) (T : VTy) (Γ : Ctx VTy)
    (ml : Bool) : Prop :=
  ∀ (δ : LSub), Δ.Models δ → ∀ (β : Life), b.interp δ = some β →
    ∀ (l : BoCa.Loc) (γ : List Val), γ.length = Γ.length →
      ∃ Fz : Life → Bool → List SRec → WProp,
      (∀ α d ls ls' ρ, Ext ls ls' ρ → Fz α d ls ρ → Fz α d ls' ρ) ∧
      (∀ α d ls ρ, Fz α d ls ρ → ρ.InStratum α) ∧
      (∀ α, α ⊏ β → ∀ ls ρ, TabAt l α ρ →
        gDenC ls (δ.extend x α) (Γ ++ [mSlot x T ml]) (γ ++ [Val.loc l]) ρ →
        ∃ d ρz ρn, ResU.CompS ρz ρn ρ ∧ Fz α d ls ρz ∧ dropC l d ρn) ∧
      (∀ α α' d ls ρv ρz ρ, α' ⊏ α → vwD l T δ d α' ls ρv → Fz α d ls ρz →
        ResU.CompS ρv ρz ρ →
        TabAt l α' ρ ∧ gDenC ls (δ.extend x α') (Γ ++ [mSlot x T ml]) (γ ++ [Val.loc l]) ρ)

/-- **Every frame of `LOk` slots thaws** (`fzG_freeze`, `fzG_thaw`). The borrow's own slot is a
`Mut 'x T` at `ℓ`. -/
theorem lok_thaws {Δ : LifeCtx} {x : LifeVar} {b : Lifetime.Life} {T : VTy}
    (hbx : b.mentions x = false) (hΔx : ∀ y u, Δ.find? y = some u → u.mentions x = false)
    (hT : ¬ VFree x T) {Γ : Ctx VTy} (hok : ∀ s ∈ Γ, s.live = true → LOk Δ x b T s.ty)
    (ml : Bool) : FrameThawsD Δ x b T Γ ml := by
  intro δ hδ β hβ l γ hlen
  have hok' : ∀ s ∈ Γ ++ [mSlot x T ml], s.live = true → LOk Δ x b T s.ty := by
    intro s hs hl
    rcases List.mem_append.mp hs with h | h
    · exact hok s h hl
    · simp at h; subst h; exact Or.inl rfl
  have hlw : ∀ ml', Ctx.LiveWithin (Γ ++ [mSlot x T ml']) (γ ++ [Val.loc l]) :=
    fun ml' => liveWithin_append Γ _ γ _ hlen
  refine ⟨fun α d ls => fzG x T δ l α (Γ ++ [mSlot x T ml]) (γ ++ [Val.loc l]) ls d,
    fun α d ls ls' ρ he h => fzG_local _ _ he h,
    fun α d ls ρ h => fzG_inStratum _ _ h, ?_, ?_⟩
  · intro α hα ls ρ ht hg
    exact fzG_freeze (models_extend hδ hbx hΔx hβ hα) _ hok' _ (gDenC_iff.mp hg).2 ht
  · intro α α' d ls ρv ρz ρ hα' hv hz hc
    obtain ⟨hg, ht⟩ := fzG_thaw hT (le_of_lt hα') _ hok' _ hz hv (ResU.CompS.comm hc)
    exact ⟨ht, gDenC_mk (hlw ml) hg⟩

/-- `StopSafe` frames are `LOk` frames. -/
theorem stopSafe_lok {Δ : LifeCtx} {x : LifeVar} {b : Lifetime.Life} {T : VTy} {Γ : Ctx VTy}
    (hs : StopSafe Δ x b Γ) : ∀ s ∈ Γ, s.live = true → LOk Δ x b T s.ty :=
  fun s hm hl => lok_of_free s.ty (hs s hm hl).1 (hs s hm hl).2

end GhostEnd
