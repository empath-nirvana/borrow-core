import ProbeD1.BinderInst

/-!
# ProbeD1 — PlaceViews in W: the guard's local bundle (`BINDER.md` §2.3–§2.4, item 1)

The guard's views (`PlaceViewsL`) as the stack's run invariant, one fact per transition of W's
semantics and per configuration the relation quantifies over.

* **Cells at any depth across `●`.** A cell of a part is a cell of the whole, an `imm` cell
  possibly as a copy inside the composite (`ImmSub`: one value and witness, its lifetimes among
  the composite's); a cell of the whole is a cell of a part, or at the top the composite of two
  `imm` copies (`ExAt.of_compS_left`, `DeepAt.of_compS_left`, `top_split`, `wit_split`).
* **Views across `●`.** A view's copy is a view, and two copies of a view compose to it
  (`vwEW_immSub`, `vwEW_compS`). This is where `AtExactly` earns its place: every lifetime of a
  copy is the entry's.
* **The facts proved here**: `PVLNil`, `PVLParts`, `PVLStart`, `PVLEnd`, `PVLHide`, `PVLResume`,
  `GuardInst`. The run facts at distinct places (`PVLUpdN`, `PVLRunsN`) are in
  `BinderPVRun.lean`; `PVLFut` is not attempted.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace ProbeD1
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open GhostEnd (LEnt LStack LKind extS vwE vwS vis stratS ReLend TabAtS)

/-! ### A copy of a cell -/

/-- **`ψ` is `ψ'`, or a copy of it**: both `imm` cells over one value and witness, `ψ`'s lifetimes
among `ψ'`'s. A part's cell is a copy of the whole's at its place. -/
def ImmSub (ψ ψ' : CellU BoCa.Loc Val) : Prop :=
  ψ = ψ' ∨ ∃ (S S' : LSet) (v : Val) (χ : WRes) (h : χ.InStratum S.join)
    (h' : χ.InStratum S'.join),
    ψ = CellU.immOf S v χ h ∧ ψ' = CellU.immOf S' v χ h' ∧ ∀ x, S.mem x → S'.mem x

theorem ImmSub.refl (ψ : CellU BoCa.Loc Val) : ImmSub ψ ψ := Or.inl rfl

theorem ImmSub.kind {ψ ψ' : CellU BoCa.Loc Val} (h : ImmSub ψ ψ') : ψ.kind = ψ'.kind := by
  rcases h with rfl | ⟨S, S', v, χ, h, h', rfl, rfl, -⟩
  · rfl
  · rfl

theorem ImmSub.wit {ψ ψ' : CellU BoCa.Loc Val} (h : ImmSub ψ ψ') : ψ.wit = ψ'.wit := by
  rcases h with rfl | ⟨S, S', v, χ, h, h', rfl, rfl, -⟩
  · rfl
  · rw [CellU.wit_immOf, CellU.wit_immOf]

theorem immSub_of_compS_left {ψ₁ ψ₂ ψ : CellU BoCa.Loc Val} (h : CellU.CompS ψ₁ ψ₂ ψ) :
    ImmSub ψ₁ ψ := by
  obtain ⟨s₁, s₂, v, χ, h₁, h₂, h₃, rfl, rfl, rfl⟩ := h
  exact Or.inr ⟨s₁, s₁ ∪ s₂, v, χ, h₁, h₃, rfl, rfl, fun x hx => Or.inl hx⟩

theorem immSub_of_compS_right {ψ₁ ψ₂ ψ : CellU BoCa.Loc Val} (h : CellU.CompS ψ₁ ψ₂ ψ) :
    ImmSub ψ₂ ψ := immSub_of_compS_left (CellU.CompS.comm h)

/-! ### Cells at any depth across `●` -/

section depth
variable {ρ₁ ρ₂ ρ : WRes} {l : BoCa.Loc} {ψ : CellU BoCa.Loc Val}

/-- A cell of `ρ` at the top: `ExAt.top` and `DeepAt.top` both. -/
theorem top_of_compS_left (hc : ResU.CompS ρ₁ ρ₂ ρ) (e : ρ₁.get l = some ψ) :
    ∃ ψ', ρ.get l = some ψ' ∧ ImmSub ψ ψ' := by
  rcases ResU.Comp.get hc l with ⟨f₁, -, -⟩ | ⟨χ, f₁, -, f⟩ | ⟨χ, f₁, -, -⟩ |
      ⟨χ₁, χ₂, χ, f₁, -, f, hC⟩
  · rw [e] at f₁; exact absurd f₁ (by simp)
  · rw [e] at f₁; obtain rfl := Option.some.inj f₁; exact ⟨_, f, ImmSub.refl _⟩
  · rw [e] at f₁; exact absurd f₁ (by simp)
  · rw [e] at f₁; obtain rfl := Option.some.inj f₁; exact ⟨χ, f, immSub_of_compS_left hC⟩

theorem ExAt.of_compS_left (hc : ResU.CompS ρ₁ ρ₂ ρ) (h : ExAt ρ₁ l ψ) :
    ∃ ψ', ExAt ρ l ψ' ∧ ImmSub ψ ψ' := by
  cases h with
  | top e =>
      obtain ⟨ψ', e', hs⟩ := top_of_compS_left hc e
      exact ⟨ψ', ExAt.top e', hs⟩
  | wit em hk hw =>
      exact ⟨ψ, ExAt.wit (ResU.CompS.get_left_of_ne_imm hc em (by rw [hk]; decide)).2 hk hw,
        ImmSub.refl _⟩

theorem ExAt.of_compS_right (hc : ResU.CompS ρ₁ ρ₂ ρ) (h : ExAt ρ₂ l ψ) :
    ∃ ψ', ExAt ρ l ψ' ∧ ImmSub ψ ψ' := ExAt.of_compS_left (ResU.CompS.comm hc) h

theorem DeepAt.of_compS_left (hc : ResU.CompS ρ₁ ρ₂ ρ) (h : DeepAt ρ₁ l ψ) :
    ∃ ψ', DeepAt ρ l ψ' ∧ ImmSub ψ ψ' := by
  cases h with
  | top e =>
      obtain ⟨ψ', e', hs⟩ := top_of_compS_left hc e
      exact ⟨ψ', DeepAt.top e', hs⟩
  | @wit _ m _ φ _ em hw =>
      obtain ⟨φ', e', -, hwit⟩ := ResU.CompS.get_left hc em
      exact ⟨ψ, DeepAt.wit e' (hwit ▸ hw), ImmSub.refl _⟩

theorem DeepAt.of_compS_right (hc : ResU.CompS ρ₁ ρ₂ ρ) (h : DeepAt ρ₂ l ψ) :
    ∃ ψ', DeepAt ρ l ψ' ∧ ImmSub ψ ψ' := DeepAt.of_compS_left (ResU.CompS.comm hc) h

/-- A top-level cell of the whole is a part's, or the composite of the two parts' copies. -/
theorem top_split (hc : ResU.CompS ρ₁ ρ₂ ρ) (e : ρ.get l = some ψ) :
    ρ₁.get l = some ψ ∨ ρ₂.get l = some ψ ∨
      ∃ ψ₁ ψ₂, ρ₁.get l = some ψ₁ ∧ ρ₂.get l = some ψ₂ ∧ CellU.CompS ψ₁ ψ₂ ψ := by
  rcases ResU.Comp.get hc l with ⟨-, -, f⟩ | ⟨χ, f₁, -, f⟩ | ⟨χ, -, f₂, f⟩ |
      ⟨χ₁, χ₂, χ, f₁, f₂, f, hC⟩
  · rw [e] at f; exact absurd f (by simp)
  · rw [e] at f; obtain rfl := Option.some.inj f; exact Or.inl f₁
  · rw [e] at f; obtain rfl := Option.some.inj f; exact Or.inr (Or.inl f₂)
  · rw [e] at f; obtain rfl := Option.some.inj f; exact Or.inr (Or.inr ⟨χ₁, χ₂, f₁, f₂, hC⟩)

/-- A nested cell of the whole is nested in one of the parts, through a cell with the same
witness. -/
theorem wit_split (hc : ResU.CompS ρ₁ ρ₂ ρ) {m : BoCa.Loc} {φ : CellU BoCa.Loc Val}
    (e : ρ.get m = some φ) :
    (∃ φ₁, ρ₁.get m = some φ₁ ∧ φ₁.wit = φ.wit ∧ φ₁.kind = φ.kind) ∨
      (∃ φ₂, ρ₂.get m = some φ₂ ∧ φ₂.wit = φ.wit ∧ φ₂.kind = φ.kind) := by
  rcases top_split hc e with e₁ | e₂ | ⟨ψ₁, ψ₂, f₁, -, hC⟩
  · exact Or.inl ⟨φ, e₁, rfl, rfl⟩
  · exact Or.inr ⟨φ, e₂, rfl, rfl⟩
  · exact Or.inl ⟨ψ₁, f₁, (CellU.CompS.wit hC).1.symm,
      (CellU.CompatS.kinds (CellU.CompS.compat hC)).1.trans (CellU.CompS.kind hC).symm⟩

end depth

/-! ### Views across `●` -/

/-- A view at an `imm` entry, unfolded. -/
theorem vwEW_imm_iff {s : LSub} {e : LEnt} {u₀ : Val} (hk : e.k = .imm u₀) {α : Life}
    {ls : List SRec} {l : BoCa.Loc} {ψ : CellU BoCa.Loc Val} :
    vwEW s e true α ls (ResU.single l ψ) ↔
      l = e.l ∧ ∃ (S : LSet) (v : Val) (χ : WRes) (h : χ.InStratum S.join),
        ψ = CellU.immOf S v χ h ∧ (∀ x, S.mem x → x = α) ∧
        ∃ ls₀ : List SRec, vC true e.T ls₀ s v χ ∧ ∀ x, x ∈ ls₀ ↔ (x ∈ ls ∧ x.2 ⊐ α) := by
  obtain ⟨el, ex, eT, ek, ecr⟩ := e
  simp only at hk
  subst hk
  constructor
  · rintro ⟨⟨S, v, χ, h, ls₀, hρ, hP, hα, hls₀⟩, hat⟩
    have hg := congrArg (fun r => PMap.get r l) hρ
    simp only [ResU.single_get_self] at hg
    have hl : l = el := by
      by_contra hne
      rw [ResU.single_get_ne _ hne] at hg
      exact absurd hg (by simp)
    subst hl
    rw [ResU.single_get_self] at hg
    obtain rfl := Option.some.inj hg
    have hmem : ∀ x, S.mem x → x = α := fun x hx =>
      (hat _ (by rw [ResU.single_get_self])).2 S rfl x hx
    have hmeet : S.meet = α := hmem _ S.meet_mem
    refine ⟨rfl, S, v, χ, h, rfl, hmem, ls₀, hP, fun x => ?_⟩
    rw [hls₀ x, hmeet]
  · rintro ⟨rfl, S, v, χ, h, rfl, hmem, ls₀, hP, hls₀⟩
    have hmeet : S.meet = α := hmem _ S.meet_mem
    refine ⟨⟨S, v, χ, h, ls₀, rfl, hP, hmeet.symm.le, fun x => ?_⟩, fun ψ hψ => ?_⟩
    · rw [hls₀ x, hmeet]
    · rw [ResU.single_get_self] at hψ
      obtain rfl := Option.some.inj hψ
      exact ⟨hmeet, fun t ht y hy => by
        simp only [CellU.lsOf, CellU.immOf, Option.some.injEq] at ht
        subst ht
        exact hmem y hy⟩

/-- A view at a `mut` entry is a `mut` cell. -/
theorem vwEW_mut_kind {s : LSub} {e : LEnt} (hk : e.k = .mut) {α : Life} {ls : List SRec}
    {l : BoCa.Loc} {ψ : CellU BoCa.Loc Val} (h : vwEW s e true α ls (ResU.single l ψ)) :
    ψ.kind = Kind.mut := by
  obtain ⟨el, ex, eT, ek, ecr⟩ := e
  simp only at hk
  subst hk
  obtain ⟨⟨b, u, χ, hχ, Q, hw, ls₀, -, hρ, -⟩, -⟩ := h
  have hg := congrArg (fun r => PMap.get r l) hρ
  simp only [ResU.single_get_self] at hg
  by_cases hl : l = el
  · subst hl; rw [ResU.single_get_self] at hg; rw [Option.some.inj hg]; rfl
  · rw [ResU.single_get_ne _ hl] at hg; exact absurd hg (by simp)

/-- **A copy of a view is a view.** -/
theorem vwEW_immSub {s : LSub} {e : LEnt} {α : Life} {ls : List SRec} {l : BoCa.Loc}
    {ψ ψ' : CellU BoCa.Loc Val} (hv : vwEW s e true α ls (ResU.single l ψ')) (hs : ImmSub ψ ψ') :
    vwEW s e true α ls (ResU.single l ψ) := by
  rcases hs with rfl | ⟨S, S', v, χ, h, h', rfl, rfl, hsub⟩
  · exact hv
  · cases hk : e.k with
    | «mut» => exact absurd (vwEW_mut_kind hk hv) (by simp)
    | imm u₀ =>
        obtain ⟨hl, S'', v', χ', h'', he, hmem, ls₀, hP, hls₀⟩ := (vwEW_imm_iff hk).mp hv
        obtain ⟨hs, hv', hχ⟩ := CellU.immOf_inj he
        subst hs hv' hχ
        refine (vwEW_imm_iff hk).mpr ⟨hl, S, v, χ, h, rfl, fun x hx => hmem x (hsub x hx), ls₀,
          hP, hls₀⟩

/-- **Two copies of one entry's view compose to its view.** -/
theorem vwEW_compS {s : LSub} {e : LEnt} {α : Life} {ls : List SRec} {l : BoCa.Loc}
    {ψ₁ ψ₂ ψ : CellU BoCa.Loc Val} (h₁ : vwEW s e true α ls (ResU.single l ψ₁))
    (h₂ : vwEW s e true α ls (ResU.single l ψ₂)) (hc : CellU.CompS ψ₁ ψ₂ ψ) :
    vwEW s e true α ls (ResU.single l ψ) := by
  obtain ⟨s₁, s₂, v, χ, k₁, k₂, k₃, rfl, rfl, rfl⟩ := hc
  cases hk : e.k with
  | «mut» => exact absurd (vwEW_mut_kind hk h₁) (by simp)
  | imm u₀ =>
      obtain ⟨hl, S₁, v₁, χ₁, hh₁, he₁, hmem₁, ls₀, hP, hls₀⟩ := (vwEW_imm_iff hk).mp h₁
      obtain ⟨-, S₂, v₂, χ₂, hh₂, he₂, hmem₂, -, -, -⟩ := (vwEW_imm_iff hk).mp h₂
      obtain ⟨hs₁, hv₁, hχ₁⟩ := CellU.immOf_inj he₁
      obtain ⟨hs₂, -, -⟩ := CellU.immOf_inj he₂
      subst hs₁ hv₁ hχ₁ hs₂
      refine (vwEW_imm_iff hk).mpr ⟨hl, s₁ ∪ s₂, v, χ, k₃, rfl, ?_, ls₀, hP, hls₀⟩
      rintro x (hx | hx)
      · exact hmem₁ x hx
      · exact hmem₂ x hx

/-- A view reads the payload type at the reading; two readings agreeing on its variables give one
view. -/
theorem vwEW_congr {s s' : LSub} {e : LEnt} (h : ∀ y, VFree y e.T → s'.find? y = s.find? y)
    {d : Bool} {α : Life} {ls : List SRec} {ρ : WRes} :
    vwEW s' e d α ls ρ ↔ vwEW s e d α ls ρ := by
  have hv : vwE s' e d α ls = vwE s e d α ls := by
    cases d with
    | false => rfl
    | true =>
        obtain ⟨el, ex, eT, ek, ecr⟩ := e
        have hC : (fun ls₀ => vC true eT ls₀ s') = fun ls₀ => vC true eT ls₀ s :=
          funext fun ls₀ => vC_congr eT h true ls₀
        cases ek with
        | «mut» => show GhostEnd.viewP el eT s' α ls = GhostEnd.viewP el eT s α ls
                   unfold GhostEnd.viewP; rw [hC]
        | imm v => show ptoImmS el α ls _ = ptoImmS el α ls _; rw [hC]
  unfold vwEW
  rw [hv]

/-! ### The innermost entry at a place -/

theorem innerAt_cons (e : LEnt) (σ : LStack) (α : Life) (αs : List Life) (l : BoCa.Loc) :
    innerAt (e :: σ) (α :: αs) l = if e.l = l then some (e, α) else innerAt σ αs l := by
  unfold innerAt
  simp only [List.zip_cons_cons, List.find?_cons]
  by_cases h : e.l = l <;> simp [h]

theorem innerAt_mem {σ : LStack} {αs : List Life} {l : BoCa.Loc} {e : LEnt} {α : Life}
    (h : innerAt σ αs l = some (e, α)) : (e, α) ∈ σ.zip αs ∧ e.l = l := by
  unfold innerAt at h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

theorem innerAt_none_of_not_mem {σ : LStack} {αs : List Life} {l : BoCa.Loc}
    (h : l ∉ σ.map LEnt.l) : innerAt σ αs l = none := by
  cases hi : innerAt σ αs l with
  | none => rfl
  | some p =>
      obtain ⟨hm, hl⟩ := innerAt_mem (e := p.1) (α := p.2) hi
      exact absurd (hl ▸ List.mem_map_of_mem (List.of_mem_zip hm).1) h

theorem mem_places_of_innerAt {σ : LStack} {αs : List Life} {l : BoCa.Loc} {e : LEnt}
    {α : Life} (h : innerAt σ αs l = some (e, α)) : l ∈ σ.map LEnt.l := by
  obtain ⟨hm, hl⟩ := innerAt_mem h
  exact hl ▸ List.mem_map_of_mem (List.of_mem_zip hm).1

theorem innerAt_some_of_mem_zip {σ : LStack} {αs : List Life} {l : BoCa.Loc} {e₁ : LEnt}
    {α₁ : Life} (hm : (e₁, α₁) ∈ σ.zip αs) (hl : e₁.l = l) :
    ∃ e α, innerAt σ αs l = some (e, α) := by
  unfold innerAt
  cases h : (σ.zip αs).find? (fun p => decide (p.1.l = l)) with
  | none =>
      exact absurd (List.find?_eq_none.mp h (e₁, α₁) hm) (by simp [hl])
  | some p => exact ⟨p.1, p.2, rfl⟩

theorem innerAt_isSome {σ : LStack} {αs : List Life} (hl : αs.length = σ.length) {l : BoCa.Loc}
    (h : l ∈ σ.map LEnt.l) : ∃ e α, innerAt σ αs l = some (e, α) := by
  induction σ generalizing αs with
  | nil => simp at h
  | cons e σ ih =>
      cases αs with
      | nil => simp at hl
      | cons α αs =>
          rw [innerAt_cons]
          by_cases he : e.l = l
          · exact ⟨e, α, if_pos he⟩
          · rw [if_neg he]
            simp only [List.map_cons, List.mem_cons] at h
            exact ih (by simpa using hl) (h.resolve_left (Ne.symm he))

/-! ### `PlaceViewsL` across `●` -/

/-- Unfolded: the guard's two conjuncts. -/
theorem placeViewsL_iff {s : LSub} {σ : LStack} {αs : List Life} {ls : List SRec} {ρ : WRes} :
    PlaceViewsL s σ αs ls ρ ↔
      (∀ l ψ, ExAt ρ l ψ → ψ.kind ≠ Kind.own → ∀ e α, innerAt σ αs l = some (e, α) →
        vwEW s e true α ls (ResU.single l ψ)) ∧
      (∀ l ψ, DeepAt ρ l ψ → ψ.kind ≠ Kind.own → l ∈ σ.map LEnt.l → ∃ e α, (e, α) ∈ σ.zip αs ∧
        e.l = l ∧ vwEW s e true α ls (ResU.single l ψ)) := Iff.rfl

section parts
variable {s : LSub} {σ : LStack} {αs : List Life} {ls : List SRec}

/-- **A part has the guard's views.** -/
theorem placeViewsL_left {ρ₁ ρ₂ ρ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ)
    (h : PlaceViewsL s σ αs ls ρ) : PlaceViewsL s σ αs ls ρ₁ := by
  refine ⟨fun l ψ hx ho e α hi => ?_, fun l ψ hd ho hl => ?_⟩
  · obtain ⟨ψ', hx', hs⟩ := ExAt.of_compS_left hc hx
    exact vwEW_immSub (h.1 l ψ' hx' (hs.kind ▸ ho) e α hi) hs
  · obtain ⟨ψ', hd', hs⟩ := DeepAt.of_compS_left hc hd
    obtain ⟨e, α, hm, hel, hv⟩ := h.2 l ψ' hd' (hs.kind ▸ ho) hl
    exact ⟨e, α, hm, hel, vwEW_immSub hv hs⟩

theorem placeViewsL_right {ρ₁ ρ₂ ρ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ)
    (h : PlaceViewsL s σ αs ls ρ) : PlaceViewsL s σ αs ls ρ₂ :=
  placeViewsL_left (ResU.CompS.comm hc) h

/-- **The parts' views give the whole's.** At the top, two copies of the innermost entry's view
compose to its view; below the top, a cell is one part's. -/
theorem placeViewsL_join {ρ₁ ρ₂ ρ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ)
    (h₁ : PlaceViewsL s σ αs ls ρ₁) (h₂ : PlaceViewsL s σ αs ls ρ₂) :
    PlaceViewsL s σ αs ls ρ := by
  have topCase : ∀ l ψ, ρ.get l = some ψ → ψ.kind ≠ Kind.own → ∀ e α,
      innerAt σ αs l = some (e, α) → vwEW s e true α ls (ResU.single l ψ) := by
    intro l ψ e' ho e α hi
    rcases top_split hc e' with e₁ | e₂ | ⟨ψ₁, ψ₂, f₁, f₂, hC⟩
    · exact h₁.1 l ψ (ExAt.top e₁) ho e α hi
    · exact h₂.1 l ψ (ExAt.top e₂) ho e α hi
    · have hk₁ : ψ₁.kind ≠ Kind.own := by
        rw [(CellU.CompatS.kinds (CellU.CompS.compat hC)).1]; decide
      have hk₂ : ψ₂.kind ≠ Kind.own := by
        rw [(CellU.CompatS.kinds (CellU.CompS.compat hC)).2]; decide
      exact vwEW_compS (h₁.1 l ψ₁ (ExAt.top f₁) hk₁ e α hi) (h₂.1 l ψ₂ (ExAt.top f₂) hk₂ e α hi) hC
  refine ⟨fun l ψ hx ho e α hi => ?_, fun l ψ hd ho hl => ?_⟩
  · cases hx with
    | top e' => exact topCase l ψ e' ho e α hi
    | @wit _ m _ φ _ em hk hw =>
        rcases ResU.CompS.get_split_of_ne_imm hc em (by rw [hk]; decide) with ⟨f₁, -⟩ | ⟨-, f₂⟩
        · exact h₁.1 l ψ (ExAt.wit f₁ hk hw) ho e α hi
        · exact h₂.1 l ψ (ExAt.wit f₂ hk hw) ho e α hi
  · cases hd with
    | top e' =>
        rcases top_split hc e' with e₁ | e₂ | ⟨ψ₁, ψ₂, f₁, -, hC⟩
        · exact h₁.2 l ψ (DeepAt.top e₁) ho hl
        · exact h₂.2 l ψ (DeepAt.top e₂) ho hl
        · have hk₁ : ψ₁.kind ≠ Kind.own := by
            rw [(CellU.CompatS.kinds (CellU.CompS.compat hC)).1]; decide
          obtain ⟨e₁, α₁, hm₁, hel₁, -⟩ := h₁.2 l ψ₁ (DeepAt.top f₁) hk₁ hl
          obtain ⟨e, α, hi⟩ := innerAt_some_of_mem_zip hm₁ hel₁
          obtain ⟨hm, hel⟩ := innerAt_mem hi
          exact ⟨e, α, hm, hel, topCase l ψ e' ho e α hi⟩
    | @wit _ m _ φ _ em hw =>
        rcases wit_split hc em with ⟨φ₁, f₁, hw₁, -⟩ | ⟨φ₂, f₂, hw₂, -⟩
        · exact h₁.2 l ψ (DeepAt.wit f₁ (hw₁ ▸ hw)) ho hl
        · exact h₂.2 l ψ (DeepAt.wit f₂ (hw₂ ▸ hw)) ho hl

end parts

/-! ### The bundle's facts that are not runs -/

theorem ExAt.toDeepAt {ρ : WRes} {l : BoCa.Loc} {ψ : CellU BoCa.Loc Val} (h : ExAt ρ l ψ) :
    DeepAt ρ l ψ := by
  induction h with
  | top e => exact DeepAt.top e
  | wit em _ _ ih => exact DeepAt.wit em ih

/-- At the empty stack no place is bound. -/
theorem pvlNil : PVLNil := fun _ _ _ =>
  ⟨fun _ _ _ _ _ _ hi => absurd hi (by simp [innerAt]), fun _ _ _ _ hl => absurd hl (by simp)⟩

/-- **Parts and whole.** -/
theorem pvlParts : PVLParts := fun _ _ _ _ _ _ _ hc =>
  ⟨fun h => ⟨placeViewsL_left hc h, placeViewsL_right hc h⟩,
    fun ⟨h₁, h₂⟩ => placeViewsL_join hc h₁ h₂⟩

/-- Pushing an entry whose place holds no cell of the resource keeps its guard's views, read at a
reading that agrees with the old one at the old entries' payload types. -/
theorem placeViewsL_push {s s' : LSub} {σ : LStack} {αs : List Life} {ls : List SRec} {e : LEnt}
    {α : Life} (hs : ∀ e' ∈ σ, ∀ y, VFree y e'.T → s'.find? y = s.find? y) {ρ : WRes}
    (h : PlaceViewsL s σ αs ls ρ) (hfree : ∀ ψ, ¬ DeepAt ρ e.l ψ) :
    PlaceViewsL s' (e :: σ) (α :: αs) ls ρ := by
  refine ⟨fun l ψ hx ho e' α' hi => ?_, fun l ψ hd ho hl => ?_⟩
  · rw [innerAt_cons] at hi
    by_cases hel : e.l = l
    · subst hel; exact absurd hx.toDeepAt (hfree ψ)
    · rw [if_neg hel] at hi
      have he' : e' ∈ σ := (List.of_mem_zip (innerAt_mem hi).1).1
      exact (vwEW_congr (hs e' he')).mpr (h.1 l ψ hx ho e' α' hi)
  · have hl' : l ∈ σ.map LEnt.l := by
      simp only [List.map_cons, List.mem_cons] at hl
      rcases hl with rfl | hl
      · exact absurd hd (hfree ψ)
      · exact hl
    obtain ⟨e', α', hm, hel, hv⟩ := h.2 l ψ hd ho hl'
    exact ⟨e', α', List.mem_cons_of_mem _ hm, hel,
      (vwEW_congr (hs e' (List.of_mem_zip hm).1)).mpr hv⟩

/-- **The start of a lend.** -/
theorem pvlStart : PVLStart := by
  intro s s' σ αs ls e α ρ a R _ _ _ hs h hfree _ ha hc
  exact placeViewsL_join hc (placeViewsL_push hs h hfree) ha

/-- Popping an entry whose place holds no cell of the resource keeps its guard's views. -/
theorem placeViewsL_pop {s s' : LSub} {σ : LStack} {αs : List Life} {ls : List SRec} {e : LEnt}
    {α : Life} (hs : ∀ e' ∈ σ, ∀ y, VFree y e'.T → s'.find? y = s.find? y) {ρ : WRes}
    (h : PlaceViewsL s' (e :: σ) (α :: αs) ls ρ) (hfree : ∀ ψ, ¬ DeepAt ρ e.l ψ) :
    PlaceViewsL s σ αs ls ρ := by
  refine ⟨fun l ψ hx ho e' α' hi => ?_, fun l ψ hd ho hl => ?_⟩
  · have hel : e.l ≠ l := fun hel => hfree ψ (hel ▸ hx.toDeepAt)
    have hi' : innerAt (e :: σ) (α :: αs) l = some (e', α') := by
      rw [innerAt_cons, if_neg hel]; exact hi
    have he' : e' ∈ σ := (List.of_mem_zip (innerAt_mem hi).1).1
    exact (vwEW_congr (hs e' he')).mp (h.1 l ψ hx ho e' α' hi')
  · obtain ⟨e', α', hm, hel, hv⟩ := h.2 l ψ hd ho (List.mem_cons_of_mem _ hl)
    rw [List.zip_cons_cons] at hm
    rcases List.mem_cons.mp hm with he | hm
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      exact absurd (hel ▸ hd) (hfree ψ)
    · exact ⟨e', α', hm, hel, (vwEW_congr (hs e' (List.of_mem_zip hm).1)).mp hv⟩

/-- **The end of a lend.** -/
theorem pvlEnd : PVLEnd := by
  intro s s' σ αs ls e α ρ' a R _ hs h hfree ha hc
  exact placeViewsL_join hc (placeViewsL_pop hs h hfree) ha

theorem innerAt_hideS (N : UInt32 → Bool) (σ : LStack) (αs : List Life) (l : BoCa.Loc) :
    innerAt (hideS N σ) αs l =
      (innerAt σ αs l).map fun p => ({ p.1 with cross := fun n => p.1.cross n && !N n }, p.2) := by
  unfold innerAt hideS
  rw [List.zip_map_left, List.find?_map]
  rfl

/-- **A handler keeps the guard's views**: they read no entry's row. -/
theorem pvlHide : PVLHide := by
  intro N s σ αs ls ρ h
  refine ⟨fun l ψ hx ho e α hi => ?_, fun l ψ hd ho hl => ?_⟩
  · rw [innerAt_hideS] at hi
    obtain ⟨⟨e₀, α₀⟩, hi₀, he⟩ := Option.map_eq_some_iff.mp hi
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    exact h.1 l ψ hx ho e₀ α₀ hi₀
  · rw [hideS_map_l] at hl
    obtain ⟨e₀, α₀, hm, hel, hv⟩ := h.2 l ψ hd ho hl
    refine ⟨{ e₀ with cross := fun n => e₀.cross n && !N n }, α₀, ?_, hel, hv⟩
    unfold hideS
    rw [List.zip_map_left, List.mem_map]
    exact ⟨(e₀, α₀), hm, rfl⟩

theorem vwSW_length {s : LSub} : ∀ {seen : List BoCa.Loc} {σ : LStack} {ds : List Bool}
    {αs : List Life} {ls : List SRec} {ρ : WRes}, vwSW s seen σ ds αs ls ρ →
    ds.length = σ.length ∧ αs.length = σ.length
  | _, [], [], [], _, _, _ => ⟨rfl, rfl⟩
  | _, _ :: _, _ :: _, _ :: _, _, _, ⟨_, _, _, _, h₂⟩ => by
      have := vwSW_length h₂; simp [this.1, this.2]
  | _, [], [], _ :: _, _, _, h => h.elim
  | _, [], _ :: _, [], _, _, h => h.elim
  | _, [], _ :: _, _ :: _, _, _, h => h.elim
  | _, _ :: _, [], [], _, _, h => h.elim
  | _, _ :: _, [], _ :: _, _, _, h => h.elim
  | _, _ :: _, _ :: _, [], _, _, h => h.elim

theorem innerAt_append_right {σi σo : LStack} {αi αo : List Life} (hl : αi.length = σi.length)
    {l : BoCa.Loc} (hn : l ∉ σi.map LEnt.l) :
    innerAt (σi ++ σo) (αi ++ αo) l = innerAt σo αo l := by
  unfold innerAt
  rw [List.zip_append hl.symm, List.find?_append]
  have : (σi.zip αi).find? (fun p => decide (p.1.l = l)) = none := by
    rw [List.find?_eq_none]
    intro p hp hpl
    have hpl' : p.1.l = l := of_decide_eq_true hpl
    exact hn (hpl' ▸ List.mem_map_of_mem (List.of_mem_zip hp).1)
  rw [this]; rfl

/-- **The resume composite keeps the guard's views.** -/
theorem pvlResume : PVLResume := by
  intro s σi σo ds αi αo ls ρz ρv ρa R R' _ _ hz hv hvl ha hfree hc hc'
  have hlen : αi.length = σi.length := (vwSW_length hv).2
  refine placeViewsL_join hc' (placeViewsL_join hc hz hvl) ⟨fun l ψ hx ho e α hi => ?_,
    fun l ψ hd ho hl => ?_⟩
  · by_cases hli : l ∈ σi.map LEnt.l
    · obtain ⟨e', he', rfl⟩ := List.mem_map.mp hli
      exact absurd hx.toDeepAt (hfree e' he' ψ)
    · rw [innerAt_append_right hlen hli] at hi
      exact ha.1 l ψ hx ho e α hi
  · by_cases hli : l ∈ σi.map LEnt.l
    · obtain ⟨e', he', rfl⟩ := List.mem_map.mp hli
      exact absurd hd (hfree e' he' ψ)
    · have hlo : l ∈ σo.map LEnt.l := by
        rw [List.map_append] at hl
        exact (List.mem_append.mp hl).resolve_left hli
      obtain ⟨e, α, hm, hel, hvw⟩ := ha.2 l ψ hd ho hlo
      refine ⟨e, α, ?_, hel, hvw⟩
      rw [List.zip_append hlen.symm]
      exact List.mem_append_right _ hm

/-! ### The instantiation: `GuardInst` -/

/-- A cell's witness lies in every stratum the cell does. -/
theorem CellU.wit_inStratum {ψ : CellU BoCa.Loc Val} {a : Life} (h : ψ.InStratum a) :
    ψ.wit.InStratum a := by
  cases ψ with
  | own v => exact ResU.inStratum_empty a
  | imm i =>
      exact (Res.toU_inStratum i.ρ).mono (le_of_lt (lt_of_lt_of_le h i.ls.meet_le_join))
  | «mut» m => exact (Res.toU_inStratum m.ρ).mono (le_of_lt h)

/-- **Every cell of a resource, at any depth, lies in the strata the resource does.** -/
theorem DeepAt.inStratum {ρ : WRes} {a : Life} (hρ : ρ.InStratum a) {l : BoCa.Loc}
    {ψ : CellU BoCa.Loc Val} (h : DeepAt ρ l ψ) : ψ.InStratum a := by
  induction h with
  | top e => exact hρ _ _ e
  | wit em _ ih => exact ih (CellU.wit_inStratum (hρ _ _ em))

/-- A view is exactly at its entry's lifetime. -/
theorem vwEW_atExactly {s : LSub} {e : LEnt} {α : Life} {ls : List SRec} {l : BoCa.Loc}
    {ψ : CellU BoCa.Loc Val} (hel : e.l = l) (h : vwEW s e true α ls (ResU.single l ψ)) :
    AtExactly α ψ := h.2 ψ (by rw [hel, ResU.single_get_self])

/-- A copy of a cell exactly at `α` is exactly at `α`. -/
theorem AtExactly.of_immSub {α : Life} {ψ ψ' : CellU BoCa.Loc Val} (h : AtExactly α ψ')
    (hs : ImmSub ψ ψ') : AtExactly α ψ := by
  rcases hs with rfl | ⟨S, S', v, χ, hh, hh', rfl, rfl, hsub⟩
  · exact h
  · have hmem : ∀ x, S.mem x → x = α := fun x hx => h.2 S' rfl x (hsub x hx)
    exact ⟨hmem _ S.meet_mem, fun t ht y hy => by
      simp only [CellU.lsOf, CellU.immOf, Option.some.injEq] at ht
      subst ht; exact hmem y hy⟩

/-- **A part strictly above the outermost lend holds no borrow cell at a bound place, at any
depth**: such a cell is a view, exactly at a lend lifetime. -/
theorem no_bound_of_stratS {s : LSub} {σ : LStack} {αs : List Life} {ls : List SRec}
    (hc : List.IsChain (· < ·) αs) {ρz ρn ρ : WRes} (hcomp : ResU.CompS ρz ρn ρ)
    (hz : stratS αs ρz) (h : PlaceViewsL s σ αs ls ρ) {l : BoCa.Loc} {ψ : CellU BoCa.Loc Val}
    (hd : DeepAt ρz l ψ) (ho : ψ.kind ≠ Kind.own) (hl : l ∈ σ.map LEnt.l) : False := by
  obtain ⟨ψ', hd', hs⟩ := DeepAt.of_compS_left hcomp hd
  obtain ⟨e, α, hm, hel, hv⟩ := h.2 l ψ' hd' (hs.kind ▸ ho) hl
  have hex : AtExactly α ψ := (vwEW_atExactly hel hv).of_immSub hs
  have hα : α ∈ αs := (List.of_mem_zip hm).2
  cases ho' : αs.getLast? with
  | none => rw [List.getLast?_eq_none_iff] at ho'; subst ho'; exact absurd hα List.not_mem_nil
  | some o =>
      have hαo : α ≤ o := le_last_of_mem hc hα ho'
      have hin : ψ.InStratum o := DeepAt.inStratum (hz o ho') hd
      have hat : o < ψ.at := by
        cases ψ with
        | own v => exact absurd rfl ho
        | imm i => exact hin
        | «mut» m => exact hin
      rw [hex.1] at hat
      exact absurd (lt_of_lt_of_le hat hαo) (lt_irrefl _)

theorem placeViewsL_of_noBound {s : LSub} {σ : LStack} {αs : List Life} {ls : List SRec}
    {ρ : WRes} (h : ∀ l ψ, DeepAt ρ l ψ → ψ.kind ≠ Kind.own → l ∈ σ.map LEnt.l → False) :
    PlaceViewsL s σ αs ls ρ :=
  ⟨fun l ψ hx ho _ _ hi => (h l ψ hx.toDeepAt ho (mem_places_of_innerAt hi)).elim,
    fun l ψ hd ho hl => (h l ψ hd ho hl).elim⟩

theorem vwEW_vwE {s : LSub} {e : LEnt} {d : Bool} {α : Life} {ls : List SRec} {ρ : WRes}
    (h : vwEW s e d α ls ρ) : vwE s e d α ls ρ := h.1

theorem vwSW_vwS {s : LSub} : ∀ {seen : List BoCa.Loc} {σ : LStack} {ds : List Bool}
    {αs : List Life} {ls : List SRec} {ρ : WRes}, vwSW s seen σ ds αs ls ρ →
    vwS s seen σ ds αs ls ρ
  | _, [], [], [], _, _, h => h
  | _, _ :: _, _ :: _, _ :: _, _, _, ⟨a, r, hc, ha, hr⟩ => ⟨a, r, hc, ha.1, vwSW_vwS hr⟩
  | _, [], [], _ :: _, _, _, h => h.elim
  | _, [], _ :: _, [], _, _, h => h.elim
  | _, [], _ :: _, _ :: _, _, _, h => h.elim
  | _, _ :: _, [], [], _, _, h => h.elim
  | _, _ :: _, [], _ :: _, _, _, h => h.elim
  | _, _ :: _, _ :: _, [], _, _, h => h.elim

/-- **The table and the guard's views at an instantiation.** -/
theorem guardInst : GuardInst := by
  intro δ σ ds αs ls ls' ρz ρn ρ ρv R ι hok hat hz _ hcomp h hv hcv
  refine ⟨tabRelend (ℍ := ℍ) (extS (ι.sub δ) σ (ι.life αs)) σ ds αs (ι.life αs) ls' ρz ρv R hok
    (instReLend σ αs ι hok hat) hz (vwSW_vwS hv.1) hcv, ?_⟩
  exact placeViewsL_join hcv
    (placeViewsL_of_noBound fun l ψ hd ho hl => no_bound_of_stratS hok.2.1 hcomp hz h hd ho hl)
    hv.2

end ProbeD1

end
