import Paper.S5_Model.Definitions
import Support.Model.Algebra
import Support.Model.Composition
import Support.Model.Prelude
import Support.Model.Walks

/-!
# Support — Model — WalkSplitting

`[about ours]`.  The pieces of Lemmas 6.18 and 6.20: the sites of a composite, the witness families of each walk and how they split across `●`, and inclusion–exclusion over shared `imm` cells.
-/

noncomputable section

namespace BoCa.Fig16
variable {Loc Val : Type}

/-- `●` returns an `imm` cell. -/
theorem CellU.CompS.kind {ψ₁ ψ₂ ψ : CellU Loc Val} (h : CellU.CompS ψ₁ ψ₂ ψ) :
    ψ.kind = Kind.imm := by
  obtain ⟨s₁, s₂, v, ρ, k₁, k₂, k₃, e₁, e₂, e₃⟩ := h
  rw [e₃]
  rfl

/-- `●` keeps the common witness:
`imm(ᾱ₁, ρ, v) ● imm(ᾱ₂, ρ, v) = imm(ᾱ₁ ∪ ᾱ₂, ρ, v)`. -/
theorem CellU.CompS.wit {ψ₁ ψ₂ ψ : CellU Loc Val} (h : CellU.CompS ψ₁ ψ₂ ψ) :
    ψ.wit = ψ₁.wit ∧ ψ.wit = ψ₂.wit := by
  obtain ⟨s₁, s₂, v, ρ, k₁, k₂, k₃, e₁, e₂, e₃⟩ := h
  subst e₁; subst e₂; subst e₃
  exact ⟨by rw [CellU.wit_immOf, CellU.wit_immOf],
    by rw [CellU.wit_immOf, CellU.wit_immOf]⟩

end BoCa.Fig16

namespace BoCa.Fig16

theorem Kind.mut_ne_imm : Kind.mut ≠ Kind.imm := by decide

end BoCa.Fig16

namespace BoCa.Fig16
variable {Loc Val : Type}

/-- A non-`imm` cell of `ρ₁` has no partner in `ρ₂`. -/
theorem ResU.CompatS.right_eq_none {ρ₁ ρ₂ : ResU Loc Val} (h : ResU.CompatS ρ₁ ρ₂)
    {l : Loc} {ψ₁ : CellU Loc Val} (e₁ : ρ₁.get l = some ψ₁)
    (hk : ψ₁.kind ≠ Kind.imm) : ρ₂.get l = none := by
  cases e₂ : ρ₂.get l with
  | none => rfl
  | some ψ₂ => exact absurd (CellU.CompatS.kinds (h l ψ₁ ψ₂ e₁ e₂)).1 hk

/-- Where `ρ₁` is defined, the composite carries a cell of the same tag over the
same witness. -/
theorem ResU.CompS.kind_wit_left {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ)
    {l : Loc} {ψ₁ ψ : CellU Loc Val} (e₁ : ρ₁.get l = some ψ₁) (e : ρ.get l = some ψ) :
    ψ.kind = ψ₁.kind ∧ ψ.wit = ψ₁.wit := by
  rcases ResU.Comp.get h l with ⟨f₁, -, -⟩ | ⟨χ, f₁, -, f⟩ | ⟨χ, f₁, -, -⟩ |
      ⟨χ₁, χ₂, χ, f₁, -, f, hC⟩
  · rw [e₁] at f₁; exact absurd f₁ (by simp)
  · rw [e₁] at f₁
    obtain rfl := Option.some.inj f₁
    rw [e] at f
    obtain rfl := Option.some.inj f
    exact ⟨rfl, rfl⟩
  · rw [e₁] at f₁; exact absurd f₁ (by simp)
  · rw [e₁] at f₁
    obtain rfl := Option.some.inj f₁
    rw [e] at f
    obtain rfl := Option.some.inj f
    exact ⟨(CellU.CompS.kind hC).trans
        (CellU.CompatS.kinds (CellU.CompS.compat hC)).1.symm,
      (CellU.CompS.wit hC).1⟩

/-- Where `ρ₁` is defined the composite is too, with a cell of the same tag over
the same witness: the form the `imm` families of [TR] 6.20 need.
`[about ours: `CellU.wit` is a projection of ours]` -/
theorem ResU.CompS.get_left {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ)
    {l : Loc} {ψ₁ : CellU Loc Val} (e₁ : ρ₁.get l = some ψ₁) :
    ∃ ψ, ρ.get l = some ψ ∧ ψ.kind = ψ₁.kind ∧ ψ.wit = ψ₁.wit := by
  rcases optSplit (ρ.get l) with e | ⟨ψ, e⟩
  · rcases ResU.Comp.get h l with ⟨f₁, -, -⟩ | ⟨χ, f₁, -, f⟩ | ⟨χ, f₁, -, -⟩ |
        ⟨χ₁, χ₂, χ, f₁, -, f, -⟩
    · rw [e₁] at f₁; exact absurd f₁ (by simp)
    · rw [e] at f; exact absurd f (by simp)
    · rw [e₁] at f₁; exact absurd f₁ (by simp)
    · rw [e] at f; exact absurd f (by simp)
  · exact ⟨ψ, e, ResU.CompS.kind_wit_left h e₁ e⟩

/-- A non-`imm` cell of `ρ₁` survives into the composite unchanged, and `ρ₂` is
undefined there. -/
theorem ResU.CompS.get_left_of_ne_imm {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ)
    {l : Loc} {ψ : CellU Loc Val} (e₁ : ρ₁.get l = some ψ) (hk : ψ.kind ≠ Kind.imm) :
    ρ₂.get l = none ∧ ρ.get l = some ψ := by
  have e₂ : ρ₂.get l = none := ResU.CompatS.right_eq_none h.1 e₁ hk
  have hp := h.2 l
  rw [e₁, e₂] at hp
  exact ⟨e₂, hp⟩

/-- A non-`imm` cell of the composite comes from exactly one side. -/
theorem ResU.CompS.get_split_of_ne_imm {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ)
    {l : Loc} {ψ : CellU Loc Val} (e : ρ.get l = some ψ) (hk : ψ.kind ≠ Kind.imm) :
    (ρ₁.get l = some ψ ∧ ρ₂.get l = none) ∨ (ρ₁.get l = none ∧ ρ₂.get l = some ψ) := by
  rcases ResU.Comp.get h l with ⟨-, -, f⟩ | ⟨χ, f₁, f₂, f⟩ | ⟨χ, f₁, f₂, f⟩ |
      ⟨χ₁, χ₂, χ, -, -, f, hC⟩
  · rw [e] at f; exact absurd f (by simp)
  · rw [e] at f
    obtain rfl := Option.some.inj f
    exact Or.inl ⟨f₁, f₂⟩
  · rw [e] at f
    obtain rfl := Option.some.inj f
    exact Or.inr ⟨f₁, f₂⟩
  · rw [e] at f
    obtain rfl := Option.some.inj f
    exact absurd (CellU.CompS.kind hC) hk

/-- `ρ|ι` is undefined where `ρ` is. -/
theorem ResU.restrict_get_none {ρ : ResU Loc Val} {k : Kind} {l : Loc}
    (e : ρ.get l = none) : (ρ.restrict k).get l = none := by
  show (ρ.get l).bind _ = none
  rw [e]
  rfl

/-- `ρ|ι` keeps a cell of tag `ι`. -/
theorem ResU.restrict_get_some {ρ : ResU Loc Val} {k : Kind} {l : Loc}
    {ψ : CellU Loc Val} (e : ρ.get l = some ψ) (hk : ψ.kind = k) :
    (ρ.restrict k).get l = some ψ :=
  ResU.restrict_eq_some.mpr ⟨e, hk⟩

/-- `ρ|ι` drops a cell of any other tag. -/
theorem ResU.restrict_get_ne {ρ : ResU Loc Val} {k : Kind} {l : Loc}
    {ψ : CellU Loc Val} (e : ρ.get l = some ψ) (hk : ψ.kind ≠ k) :
    (ρ.restrict k).get l = none := by
  show (ρ.get l).bind _ = none
  rw [e]
  exact if_neg hk

/-- `(ρ₁ ● ρ₂)|ι = ρ₁|ι ● ρ₂|ι`, as a graph, at every tag.
`[about ours: a step inside 6.18's and 6.20's proofs]` -/
theorem ResU.CompS.restrict {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ)
    (k : Kind) :
    ResU.CompS (ρ₁.restrict k) (ρ₂.restrict k) (ρ.restrict k) := by
  refine ⟨fun l χ₁ χ₂ f₁ f₂ => h.1 l χ₁ χ₂ (ResU.restrict_eq_some.mp f₁).1
    (ResU.restrict_eq_some.mp f₂).1, fun l => ?_⟩
  rcases ResU.Comp.get h l with ⟨f₁, f₂, f⟩ | ⟨χ, f₁, f₂, f⟩ | ⟨χ, f₁, f₂, f⟩ |
      ⟨χ₁, χ₂, χ, f₁, f₂, f, hC⟩
  · rw [ResU.restrict_get_none f₁, ResU.restrict_get_none f₂, ResU.restrict_get_none f]
    rfl
  · by_cases hk : χ.kind = k
    · rw [ResU.restrict_get_some f₁ hk, ResU.restrict_get_none f₂,
        ResU.restrict_get_some f hk]
      rfl
    · rw [ResU.restrict_get_ne f₁ hk, ResU.restrict_get_none f₂,
        ResU.restrict_get_ne f hk]
      rfl
  · by_cases hk : χ.kind = k
    · rw [ResU.restrict_get_none f₁, ResU.restrict_get_some f₂ hk,
        ResU.restrict_get_some f hk]
      rfl
    · rw [ResU.restrict_get_none f₁, ResU.restrict_get_ne f₂ hk,
        ResU.restrict_get_ne f hk]
      rfl
  · -- Every cell in sight is `imm`, so the three restrictions stand or fall
    -- together and `●` is the composition it already was.
    obtain ⟨k₁, k₂⟩ := CellU.CompatS.kinds (CellU.CompS.compat hC)
    have k₃ : χ.kind = Kind.imm := CellU.CompS.kind hC
    by_cases hk : k = Kind.imm
    · subst hk
      rw [ResU.restrict_get_some f₁ k₁, ResU.restrict_get_some f₂ k₂,
        ResU.restrict_get_some f k₃]
      exact ⟨χ, rfl, hC⟩
    · rw [ResU.restrict_get_ne f₁ (fun e => hk (k₁ ▸ e).symm),
        ResU.restrict_get_ne f₂ (fun e => hk (k₂ ▸ e).symm),
        ResU.restrict_get_ne f (fun e => hk (k₃ ▸ e).symm)]
      rfl

end BoCa.Fig16

namespace BoCa.Fig16

/-- A list is a permutation of its `p`-part followed by its non-`p`-part. -/
theorem List.filter_perm_append {α : Type} (p : α → Bool) (l : List α) :
    l.Perm (l.filter p ++ l.filter (fun a => !(p a))) := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons a l ih =>
      by_cases ha : p a = true
      · rw [List.filter_cons_of_pos ha, List.filter_cons_of_neg (by simp [ha])]
        exact List.Perm.cons a ih
      · have ha' : p a = false := by
          cases e : p a with
          | false => rfl
          | true => exact absurd e ha
        rw [List.filter_cons_of_neg (by simp [ha']),
          List.filter_cons_of_pos (by simp [ha'])]
        exact (List.Perm.cons a ih).trans List.perm_middle.symm

end BoCa.Fig16

namespace BoCa.Fig16
variable {Loc Val : Type}

/-- The split of a key-indexed list by a predicate on the key, characterised by
membership.  The predicate is decided classically (G8). -/
theorem List.split_by_key {α β : Type} (q : α → Prop) (w : List (α × β)) :
    ∃ w₁ w₂ : List (α × β), w.Perm (w₁ ++ w₂) ∧
      (∀ p, p ∈ w₁ ↔ (p ∈ w ∧ q p.1)) ∧ (∀ p, p ∈ w₂ ↔ (p ∈ w ∧ ¬ q p.1)) := by
  classical
  refine ⟨w.filter (fun p => decide (q p.1)), w.filter (fun p => !(decide (q p.1))),
    List.filter_perm_append _ w, fun p => ?_, fun p => ?_⟩
  · rw [List.mem_filter]
    exact ⟨fun hx => ⟨hx.1, of_decide_eq_true hx.2⟩, fun hx => ⟨hx.1, decide_eq_true hx.2⟩⟩
  · rw [List.mem_filter]
    refine ⟨fun hx => ⟨hx.1, fun hq => ?_⟩, fun hx => ⟨hx.1, ?_⟩⟩
    · rw [decide_eq_true hq] at hx
      exact absurd hx.2 (by simp)
    · simp [hx.2]

end BoCa.Fig16

namespace BoCa.Fig16
variable {Loc Val : Type}
variable {R : CellU Loc Val → CellU Loc Val → Prop}
variable {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop}

/-- The exclusive family, entry by entry. -/
theorem ExWits.iff_mem {ρ : ResU Loc Val} {w : List (Loc × ResU Loc Val)} :
    ExWits R C ρ w ↔
      ∀ p ∈ w, ∃ ψ, ρ.get p.1 = some ψ ∧ ψ.kind = Kind.mut ∧ ExW R C ψ.wit p.2 := by
  induction w with
  | nil => exact ⟨fun _ p hp => absurd hp (by simp), fun _ => ExWits.nil⟩
  | cons q w ih =>
      constructor
      · intro h p hp
        cases h with
        | cons ψ hψ hk he hw =>
            rcases List.mem_cons.mp hp with rfl | hp
            · exact ⟨ψ, hψ, hk, he⟩
            · exact ih.mp hw p hp
      · intro h
        obtain ⟨ψ, hψ, hk, he⟩ := h q (by simp)
        exact ExWits.cons ψ hψ hk he (ih.mpr fun p hp => h p (by simp [hp]))

/-- Two exclusive families over one resource concatenate. -/
theorem ExWits.append {ρ : ResU Loc Val} {w₁ w₂ : List (Loc × ResU Loc Val)}
    (h₁ : ExWits R C ρ w₁) (h₂ : ExWits R C ρ w₂) : ExWits R C ρ (w₁ ++ w₂) :=
  ExWits.iff_mem.mpr fun p hp => by
    rcases List.mem_append.mp hp with hp | hp
    · exact ExWits.iff_mem.mp h₁ p hp
    · exact ExWits.iff_mem.mp h₂ p hp

/-- `ρ₁`'s exclusive family is one of `ρ₁ ● ρ₂`'s. -/
theorem ExWits.of_compS_left {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ)
    {w : List (Loc × ResU Loc Val)} (hw : ExWits R C ρ₁ w) : ExWits R C ρ w :=
  ExWits.iff_mem.mpr fun p hp => by
    obtain ⟨ψ, hψ, hk, he⟩ := ExWits.iff_mem.mp hw p hp
    exact ⟨ψ,
      (ResU.CompS.get_left_of_ne_imm h hψ (fun e => Kind.mut_ne_imm (hk.symm.trans e))).2,
      hk, he⟩

/-- The entries of `ρ₁ ● ρ₂`'s exclusive family that lie over `ρ₁` are `ρ₁`'s
exclusive family: the cut [TR] 6.18's forward direction makes.
`[about ours: `ExWits` is the family relation of convention G6]` -/
theorem ExWits.to_compS_left {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ)
    {w w₁ : List (Loc × ResU Loc Val)} (hw : ExWits R C ρ w)
    (hsub : ∀ p ∈ w₁, p ∈ w) (hs₁ : ρ₁.Sites Kind.mut (w₁.map Prod.fst)) :
    ExWits R C ρ₁ w₁ := by
  refine ExWits.iff_mem.mpr fun p hp => ?_
  obtain ⟨ψ₁, g₁, gk₁⟩ := (hs₁.2 p.1).mp (List.mem_map.mpr ⟨p, hp, rfl⟩)
  obtain ⟨ψ, hψ, -, hwalk⟩ := ExWits.iff_mem.mp hw p (hsub p hp)
  have hg : ρ.get p.1 = some ψ₁ :=
    (ResU.CompS.get_left_of_ne_imm h g₁ (fun e => Kind.mut_ne_imm (gk₁.symm.trans e))).2
  rw [hψ] at hg
  obtain rfl := Option.some.inj hg
  exact ⟨_, g₁, gk₁, hwalk⟩

end BoCa.Fig16

namespace BoCa.Fig16
variable {Loc Val : Type}

/-- The `mut` half of the aliasable family, entry by entry. -/
theorem AgWitsM.iff_mem {ρ : ResU Loc Val} {w : List (Loc × ResU Loc Val)} :
    AgWitsM ρ w ↔
      ∀ p ∈ w, ∃ ψ, ρ.get p.1 = some ψ ∧ ψ.kind = Kind.mut ∧ AgW ψ.wit p.2 := by
  induction w with
  | nil => exact ⟨fun _ p hp => absurd hp (by simp), fun _ => AgWitsM.nil⟩
  | cons q w ih =>
      constructor
      · intro h p hp
        cases h with
        | cons ψ hψ hk he hw =>
            rcases List.mem_cons.mp hp with rfl | hp
            · exact ⟨ψ, hψ, hk, he⟩
            · exact ih.mp hw p hp
      · intro h
        obtain ⟨ψ, hψ, hk, he⟩ := h q (by simp)
        exact AgWitsM.cons ψ hψ hk he (ih.mpr fun p hp => h p (by simp [hp]))

/-- The `imm` half of the aliasable family, entry by entry. -/
theorem AgWitsI.iff_mem {ρ : ResU Loc Val} {w : List (Loc × ResU Loc Val)} :
    AgWitsI ρ w ↔
      ∀ p ∈ w, ∃ ψ, ρ.get p.1 = some ψ ∧ ψ.kind = Kind.imm ∧
        ∃ e a, ExR ψ.wit e ∧ AgW ψ.wit a ∧ ResU.CompR e a p.2 := by
  induction w with
  | nil => exact ⟨fun _ p hp => absurd hp (by simp), fun _ => AgWitsI.nil⟩
  | cons q w ih =>
      constructor
      · intro h p hp
        cases h with
        | cons ψ hψ hk e a hex hag hc hw =>
            rcases List.mem_cons.mp hp with rfl | hp
            · exact ⟨ψ, hψ, hk, e, a, hex, hag, hc⟩
            · exact ih.mp hw p hp
      · intro h
        obtain ⟨ψ, hψ, hk, e, a, hex, hag, hc⟩ := h q (by simp)
        exact AgWitsI.cons ψ hψ hk e a hex hag hc (ih.mpr fun p hp => h p (by simp [hp]))

/-- Two `mut` halves over one resource concatenate. -/
theorem AgWitsM.append {ρ : ResU Loc Val} {w₁ w₂ : List (Loc × ResU Loc Val)}
    (h₁ : AgWitsM ρ w₁) (h₂ : AgWitsM ρ w₂) : AgWitsM ρ (w₁ ++ w₂) :=
  AgWitsM.iff_mem.mpr fun p hp => by
    rcases List.mem_append.mp hp with hp | hp
    · exact AgWitsM.iff_mem.mp h₁ p hp
    · exact AgWitsM.iff_mem.mp h₂ p hp

/-- Two `imm` halves over one resource concatenate. -/
theorem AgWitsI.append {ρ : ResU Loc Val} {w₁ w₂ : List (Loc × ResU Loc Val)}
    (h₁ : AgWitsI ρ w₁) (h₂ : AgWitsI ρ w₂) : AgWitsI ρ (w₁ ++ w₂) :=
  AgWitsI.iff_mem.mpr fun p hp => by
    rcases List.mem_append.mp hp with hp | hp
    · exact AgWitsI.iff_mem.mp h₁ p hp
    · exact AgWitsI.iff_mem.mp h₂ p hp

/-- Any sub-family of the `imm` half is one. -/
theorem AgWitsI.subset {ρ : ResU Loc Val} {w w' : List (Loc × ResU Loc Val)}
    (h : AgWitsI ρ w) (hsub : ∀ p ∈ w', p ∈ w) : AgWitsI ρ w' :=
  AgWitsI.iff_mem.mpr fun p hp => AgWitsI.iff_mem.mp h p (hsub p hp)

/-- `ρ₁`'s `mut` half is one of `ρ₁ ● ρ₂`'s. -/
theorem AgWitsM.of_compS_left {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ)
    {w : List (Loc × ResU Loc Val)} (hw : AgWitsM ρ₁ w) : AgWitsM ρ w :=
  AgWitsM.iff_mem.mpr fun p hp => by
    obtain ⟨ψ, hψ, hk, he⟩ := AgWitsM.iff_mem.mp hw p hp
    exact ⟨ψ,
      (ResU.CompS.get_left_of_ne_imm h hψ (fun e => Kind.mut_ne_imm (hk.symm.trans e))).2,
      hk, he⟩

/-- `ρ₁`'s `imm` half is one of `ρ₁ ● ρ₂`'s, overlaps included. -/
theorem AgWitsI.of_compS_left {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ)
    {w : List (Loc × ResU Loc Val)} (hw : AgWitsI ρ₁ w) : AgWitsI ρ w :=
  AgWitsI.iff_mem.mpr fun p hp => by
    obtain ⟨ψ, hψ, hk, e, a, hex, hag, hc⟩ := AgWitsI.iff_mem.mp hw p hp
    obtain ⟨χ, g, gk, gw⟩ := ResU.CompS.get_left h hψ
    exact ⟨χ, g, gk.trans hk, e, a, by rw [gw]; exact hex, by rw [gw]; exact hag, hc⟩

/-- The entries of `ρ₁ ● ρ₂`'s `mut` half that lie over `ρ₁` are `ρ₁`'s. -/
theorem AgWitsM.to_compS_left {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ)
    {w w₁ : List (Loc × ResU Loc Val)} (hw : AgWitsM ρ w)
    (hsub : ∀ p ∈ w₁, p ∈ w) (hs₁ : ρ₁.Sites Kind.mut (w₁.map Prod.fst)) :
    AgWitsM ρ₁ w₁ := by
  refine AgWitsM.iff_mem.mpr fun p hp => ?_
  obtain ⟨ψ₁, g₁, gk₁⟩ := (hs₁.2 p.1).mp (List.mem_map.mpr ⟨p, hp, rfl⟩)
  obtain ⟨ψ, hψ, -, hwalk⟩ := AgWitsM.iff_mem.mp hw p (hsub p hp)
  have hg : ρ.get p.1 = some ψ₁ :=
    (ResU.CompS.get_left_of_ne_imm h g₁ (fun e => Kind.mut_ne_imm (gk₁.symm.trans e))).2
  rw [hψ] at hg
  obtain rfl := Option.some.inj hg
  exact ⟨_, g₁, gk₁, hwalk⟩

/-- The entries of `ρ₁ ● ρ₂`'s `imm` half that lie over `ρ₁` are `ρ₁`'s. -/
theorem AgWitsI.to_compS_left {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ)
    {w w₁ : List (Loc × ResU Loc Val)} (hw : AgWitsI ρ w)
    (hsub : ∀ p ∈ w₁, p ∈ w) (hs₁ : ρ₁.Sites Kind.imm (w₁.map Prod.fst)) :
    AgWitsI ρ₁ w₁ := by
  refine AgWitsI.iff_mem.mpr fun p hp => ?_
  obtain ⟨ψ₁, g₁, gk₁⟩ := (hs₁.2 p.1).mp (List.mem_map.mpr ⟨p, hp, rfl⟩)
  obtain ⟨ψ, hψ, -, e, a, hex, hag, hc⟩ := AgWitsI.iff_mem.mp hw p (hsub p hp)
  obtain ⟨χ, g, -, gw⟩ := ResU.CompS.get_left h g₁
  rw [hψ] at g
  obtain rfl := Option.some.inj g
  exact ⟨ψ₁, g₁, gk₁, e, a, by rw [← gw]; exact hex, by rw [← gw]; exact hag, hc⟩

/-- Two `▶◀`-compatible cells carry the same witness. -/
theorem CellU.CompatS.wit {ψ₁ ψ₂ : CellU Loc Val} (h : CellU.CompatS ψ₁ ψ₂) :
    ψ₁.wit = ψ₂.wit := by
  obtain ⟨s₁, s₂, v, ρ, k₁, k₂, e₁, e₂⟩ := h
  rw [e₁, e₂, CellU.wit_immOf, CellU.wit_immOf]

/-- At an overlap the two operands' cells share their witness. -/
theorem ResU.CompatS.wit_of_overlap {ρ₁ ρ₂ : ResU Loc Val} (h : ResU.CompatS ρ₁ ρ₂)
    {l : Loc} {ψ₁ ψ₂ : CellU Loc Val}
    (e₁ : ρ₁.get l = some ψ₁) (e₂ : ρ₂.get l = some ψ₂) : ψ₁.wit = ψ₂.wit :=
  CellU.CompatS.wit (h l ψ₁ ψ₂ e₁ e₂)

end BoCa.Fig16

namespace BoCa.Fig16

/-- `BoCa.Fig16.List.perm_of_keys` with same-membership of the key lists. -/
theorem List.perm_of_keys_mem {α β : Type} {w w' : List (α × β)}
    (hk : (w.map Prod.fst).Nodup) (hk' : (w'.map Prod.fst).Nodup)
    (hmem : ∀ l, l ∈ w.map Prod.fst ↔ l ∈ w'.map Prod.fst)
    (hval : ∀ p ∈ w, ∀ q ∈ w', p.1 = q.1 → p.2 = q.2) : w.Perm w' :=
  BoCa.Fig16.List.perm_of_keys hk
    ((List.perm_ext_iff_of_nodup hk hk').mpr hmem) hval

end BoCa.Fig16

end
