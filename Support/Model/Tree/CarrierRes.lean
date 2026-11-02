import Support.Model.Tree.CarrierOps

/-!
# Resources on the tree-stratified carrier: `◐`, `⨀`, the walks, `✓`, `#`

Rows 5.17–5.23, 5.26, 5.55, 5.56 written once over a cell type `X` with a tag and a witness
(the printed rows are over `CellU` only), then read at `CellUT K`. The definitions are the
printed ones with `CellU` replaced by `X`; none of them compares lifetimes. Lemmas 6.1–6.6 and
6.9, by their printed proofs (`Paper/S6_1_StandardLemmas/Lemmas.lean`,
`Support/Model/Algebra.lean`).
-/

noncomputable section

namespace BoCa.Fig16.Tree
open BoCa.Fig16

namespace G
variable {Loc X : Type}

/-- `ρ₁ ▸◁ ρ₂` (row 5.17). -/
def Compat (C : X → X → Prop) (ρ₁ ρ₂ : PMap Loc X) : Prop :=
  ∀ l ψ₁ ψ₂, ρ₁.get l = some ψ₁ → ρ₂.get l = some ψ₂ → C ψ₁ ψ₂

/-- The three pieces of `ρ₁ ◐ ρ₂` at one location (row 5.18). -/
def OptComp (C : X → X → X → Prop) : Option X → Option X → Option X → Prop
  | none, none, o => o = none
  | some ψ, none, o => o = some ψ
  | none, some ψ, o => o = some ψ
  | some ψ₁, some ψ₂, o => ∃ ψ, o = some ψ ∧ C ψ₁ ψ₂ ψ

/-- `ρ₁ ◐ ρ₂ = ρ` (row 5.18), guarded. -/
def Comp (R : X → X → Prop) (C : X → X → X → Prop) (ρ₁ ρ₂ ρ : PMap Loc X) : Prop :=
  Compat R ρ₁ ρ₂ ∧ ∀ l, OptComp C (ρ₁.get l) (ρ₂.get l) (ρ.get l)

/-- `ρ|ι` (row 5.19). -/
def restrict (kd : X → Kind) (ρ : PMap Loc X) (k : Kind) : PMap Loc X where
  get := fun l => (ρ.get l).bind fun ψ => if kd ψ = k then some ψ else none
  finite := by
    obtain ⟨d, hd⟩ := ρ.finite
    refine ⟨d, fun l hl => hd l (fun e => hl ?_)⟩
    show (ρ.get l).bind _ = none
    rw [e]; rfl

/-- `d` lists the locations carrying a cell of tag `k` (row 5.55). -/
def Sites (kd : X → Kind) (ρ : PMap Loc X) (k : Kind) (d : List Loc) : Prop :=
  d.Nodup ∧ ∀ l, l ∈ d ↔ ∃ ψ, ρ.get l = some ψ ∧ kd ψ = k

/-- `⨀_◐` (row 5.56). -/
inductive BigComp (R : X → X → Prop) (C : X → X → X → Prop) :
    List (PMap Loc X) → PMap Loc X → Prop where
  | nil : BigComp R C [] PMap.empty
  | cons {σ τ ρ : PMap Loc X} {σs : List (PMap Loc X)} :
      BigComp R C σs τ → Comp R C σ τ ρ → BigComp R C (σ :: σs) ρ

variable (kd : X → Kind) (wt : X → PMap Loc X)

mutual

/-- `ex(ρ)_◐ = σ` (row 5.20). -/
inductive ExW (R : X → X → Prop) (C : X → X → X → Prop) : PMap Loc X → PMap Loc X → Prop where
  | mk {ρ σ nm b : PMap Loc X} {w : List (Loc × PMap Loc X)}
      (hs : Sites kd ρ Kind.mut (w.map Prod.fst))
      (hw : ExWits R C ρ w)
      (hb : BigComp R C (w.map Prod.snd) b)
      (hnm : Comp R C (restrict kd ρ Kind.own) (restrict kd ρ Kind.mut) nm)
      (hσ : Comp R C nm b σ) :
      ExW R C ρ σ

/-- The family `{ex(ρ′)_◐ | ∃ℓ. ρ(ℓ) = mut(_,_,ρ′,_)}`. -/
inductive ExWits (R : X → X → Prop) (C : X → X → X → Prop) :
    PMap Loc X → List (Loc × PMap Loc X) → Prop where
  | nil {ρ : PMap Loc X} : ExWits R C ρ []
  | cons {ρ e : PMap Loc X} {l : Loc} {w : List (Loc × PMap Loc X)}
      (ψ : X) (hψ : ρ.get l = some ψ) (hk : kd ψ = Kind.mut)
      (he : ExW R C (wt ψ) e) (hw : ExWits R C ρ w) :
      ExWits R C ρ ((l, e) :: w)

end

variable (RR : X → X → Prop) (CR : X → X → X → Prop)

mutual

/-- `ag(ρ) = σ` (row 5.21), at `○`. -/
inductive AgW : PMap Loc X → PMap Loc X → Prop where
  | mk {ρ σ a bm bi : PMap Loc X} {wm wi : List (Loc × PMap Loc X)}
      (hsm : Sites kd ρ Kind.mut (wm.map Prod.fst))
      (hsi : Sites kd ρ Kind.imm (wi.map Prod.fst))
      (hwm : AgWitsM ρ wm)
      (hwi : AgWitsI ρ wi)
      (hbm : BigComp RR CR (wm.map Prod.snd) bm)
      (hbi : BigComp RR CR (wi.map Prod.snd) bi)
      (ha : Comp RR CR (restrict kd ρ Kind.imm) bm a)
      (hσ : Comp RR CR a bi σ) :
      AgW ρ σ

/-- `{ag(ρ′) | ∃ℓ. ρ(ℓ) = mut(_,_,ρ′,_)}`. -/
inductive AgWitsM : PMap Loc X → List (Loc × PMap Loc X) → Prop where
  | nil {ρ : PMap Loc X} : AgWitsM ρ []
  | cons {ρ e : PMap Loc X} {l : Loc} {w : List (Loc × PMap Loc X)}
      (ψ : X) (hψ : ρ.get l = some ψ) (hk : kd ψ = Kind.mut)
      (he : AgW (wt ψ) e) (hw : AgWitsM ρ w) :
      AgWitsM ρ ((l, e) :: w)

/-- `{ex(ρ′)_○ ○ ag(ρ′) | ∃ℓ. ρ(ℓ) = imm(_,_,ρ′)}`. -/
inductive AgWitsI : PMap Loc X → List (Loc × PMap Loc X) → Prop where
  | nil {ρ : PMap Loc X} : AgWitsI ρ []
  | cons {ρ p : PMap Loc X} {l : Loc} {w : List (Loc × PMap Loc X)}
      (ψ : X) (hψ : ρ.get l = some ψ) (hk : kd ψ = Kind.imm)
      (e a : PMap Loc X) (hex : ExW kd wt RR CR (wt ψ) e) (hag : AgW (wt ψ) a)
      (hp : Comp RR CR e a p) (hw : AgWitsI ρ w) :
      AgWitsI ρ ((l, p) :: w)

end

variable (RS : X → X → Prop) (CS : X → X → X → Prop)

/-- `⦇ρ⦈ = σ` (row 5.22). -/
def Flat (ρ σ : PMap Loc X) : Prop :=
  ∃ e a, ExW kd wt RS CS ρ e ∧ AgW kd wt RR CR ρ a ∧ Comp RS CS e a σ

/-- `✓ρ` (row 5.23). -/
def Valid (ρ : PMap Loc X) : Prop := ∃ σ, Flat kd wt RR CR RS CS ρ σ

/-- `ρ₁ # ρ₂` (row 5.26). -/
def Hash (ρ₁ ρ₂ : PMap Loc X) : Prop :=
  Compat RS ρ₁ ρ₂ ∧ ∃ ρ, Comp RS CS ρ₁ ρ₂ ρ ∧ Valid kd wt RR CR RS CS ρ

end G

/-! ### The schema's laws, by the printed proofs -/

namespace G
variable {Loc X : Type} {R : X → X → Prop} {C : X → X → X → Prop}

theorem optSplit {A : Type} (o : Option A) : o = none ∨ ∃ a, o = some a := by
  cases o
  · exact Or.inl rfl
  · exact Or.inr ⟨_, rfl⟩

theorem Compat.comm (hC : ∀ ψ₁ ψ₂, R ψ₁ ψ₂ → R ψ₂ ψ₁) {ρ₁ ρ₂ : PMap Loc X}
    (h : Compat R ρ₁ ρ₂) : Compat R ρ₂ ρ₁ :=
  fun l ψ₁ ψ₂ e₁ e₂ => hC _ _ (h l ψ₂ ψ₁ e₂ e₁)

theorem Compat.of_disjoint {ρ₁ ρ₂ : PMap Loc X} (h : ∀ l, ρ₁.get l = none ∨ ρ₂.get l = none) :
    Compat R ρ₁ ρ₂ := by
  intro l ψ₁ ψ₂ e₁ e₂
  rcases h l with e | e
  · rw [e] at e₁; exact absurd e₁ (by simp)
  · rw [e] at e₂; exact absurd e₂ (by simp)

/-- The four shapes a location can take in a composite. -/
theorem Comp.get {ρ₁ ρ₂ ρ : PMap Loc X} (h : Comp R C ρ₁ ρ₂ ρ) (l : Loc) :
    (ρ₁.get l = none ∧ ρ₂.get l = none ∧ ρ.get l = none)
    ∨ (∃ ψ, ρ₁.get l = some ψ ∧ ρ₂.get l = none ∧ ρ.get l = some ψ)
    ∨ (∃ ψ, ρ₁.get l = none ∧ ρ₂.get l = some ψ ∧ ρ.get l = some ψ)
    ∨ (∃ ψ₁ ψ₂ ψ, ρ₁.get l = some ψ₁ ∧ ρ₂.get l = some ψ₂ ∧ ρ.get l = some ψ ∧
        C ψ₁ ψ₂ ψ) := by
  have hp := h.2 l
  rcases optSplit (ρ₁.get l) with e₁ | ⟨ψ₁, e₁⟩ <;>
    rcases optSplit (ρ₂.get l) with e₂ | ⟨ψ₂, e₂⟩ <;> rw [e₁, e₂] at hp
  · exact Or.inl ⟨e₁, e₂, hp⟩
  · exact Or.inr (Or.inr (Or.inl ⟨ψ₂, e₁, e₂, hp⟩))
  · exact Or.inr (Or.inl ⟨ψ₁, e₁, e₂, hp⟩)
  · obtain ⟨χ, hχ, hC⟩ := hp
    exact Or.inr (Or.inr (Or.inr ⟨ψ₁, ψ₂, χ, e₁, e₂, hχ, hC⟩))

/-- `[TR]` Lemma 6.2 over the schema: Lemma 6.1 for composability, then cell commutativity. -/
theorem Comp.comm (hR : ∀ ψ₁ ψ₂, R ψ₁ ψ₂ → R ψ₂ ψ₁) (hC : ∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → C ψ₂ ψ₁ ψ)
    {ρ₁ ρ₂ ρ : PMap Loc X} (h : Comp R C ρ₁ ρ₂ ρ) : Comp R C ρ₂ ρ₁ ρ := by
  refine ⟨Compat.comm hR h.1, fun l => ?_⟩
  rcases h.get l with ⟨e₁, e₂, e⟩ | ⟨ψ, e₁, e₂, e⟩ | ⟨ψ, e₁, e₂, e⟩ |
      ⟨ψ₁, ψ₂, ψ, e₁, e₂, e, hC'⟩ <;> rw [e₁, e₂]
  · exact e
  · exact e
  · exact e
  · exact ⟨ψ, e, hC _ _ _ hC'⟩

/-- `[TR]` Lemma 6.3 at one location, left to right. -/
theorem OptComp.assoc_left
    (hC : ∀ ψ₁ ψ₂ ψ₃ ω, (∃ χ, C ψ₂ ψ₃ χ ∧ C ψ₁ χ ω) → (∃ υ, C ψ₁ ψ₂ υ ∧ C υ ψ₃ ω))
    {o₁ o₂ o₃ ox ow : Option X}
    (h₂₃ : OptComp C o₂ o₃ ox) (h₁x : OptComp C o₁ ox ow) :
    ∃ oy, OptComp C o₁ o₂ oy ∧ OptComp C oy o₃ ow := by
  cases o₁ with
  | none =>
      cases o₂ with
      | none =>
          cases o₃ with
          | none =>
              have e : ox = none := h₂₃
              subst e
              have f : ow = none := h₁x
              subst f
              exact ⟨none, rfl, rfl⟩
          | some ψ₃ =>
              have e : ox = some ψ₃ := h₂₃
              subst e
              have f : ow = some ψ₃ := h₁x
              subst f
              exact ⟨none, rfl, rfl⟩
      | some ψ₂ =>
          cases o₃ with
          | none =>
              have e : ox = some ψ₂ := h₂₃
              subst e
              have f : ow = some ψ₂ := h₁x
              subst f
              exact ⟨some ψ₂, rfl, rfl⟩
          | some ψ₃ =>
              obtain ⟨χ, e, hc⟩ : ∃ χ, ox = some χ ∧ C ψ₂ ψ₃ χ := h₂₃
              subst e
              have f : ow = some χ := h₁x
              subst f
              exact ⟨some ψ₂, rfl, ⟨χ, rfl, hc⟩⟩
  | some ψ₁ =>
      cases o₂ with
      | none =>
          cases o₃ with
          | none =>
              have e : ox = none := h₂₃
              subst e
              have f : ow = some ψ₁ := h₁x
              subst f
              exact ⟨some ψ₁, rfl, rfl⟩
          | some ψ₃ =>
              have e : ox = some ψ₃ := h₂₃
              subst e
              obtain ⟨ω', f, hc⟩ : ∃ ω', ow = some ω' ∧ C ψ₁ ψ₃ ω' := h₁x
              subst f
              exact ⟨some ψ₁, rfl, ⟨ω', rfl, hc⟩⟩
      | some ψ₂ =>
          cases o₃ with
          | none =>
              have e : ox = some ψ₂ := h₂₃
              subst e
              obtain ⟨ω', f, hc⟩ : ∃ ω', ow = some ω' ∧ C ψ₁ ψ₂ ω' := h₁x
              subst f
              exact ⟨some ω', ⟨ω', rfl, hc⟩, rfl⟩
          | some ψ₃ =>
              obtain ⟨χ, e, hc₁⟩ : ∃ χ, ox = some χ ∧ C ψ₂ ψ₃ χ := h₂₃
              subst e
              obtain ⟨ω', f, hc₂⟩ : ∃ ω', ow = some ω' ∧ C ψ₁ χ ω' := h₁x
              subst f
              obtain ⟨υ, k₁, k₂⟩ := hC ψ₁ ψ₂ ψ₃ ω' ⟨χ, hc₁, hc₂⟩
              exact ⟨some υ, ⟨υ, rfl, k₁⟩, ⟨ω', rfl, k₂⟩⟩

/-- `[TR]` Lemma 6.3 at the resource level, left to right. -/
theorem Comp.assoc_left (hR : ∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → R ψ₁ ψ₂)
    (hC : ∀ ψ₁ ψ₂ ψ₃ ω, (∃ χ, C ψ₂ ψ₃ χ ∧ C ψ₁ χ ω) → (∃ υ, C ψ₁ ψ₂ υ ∧ C υ ψ₃ ω))
    {ρ₁ ρ₂ ρ₃ x w : PMap Loc X}
    (h₂₃ : Comp R C ρ₂ ρ₃ x) (h₁x : Comp R C ρ₁ x w) :
    ∃ y, Comp R C ρ₁ ρ₂ y ∧ Comp R C y ρ₃ w := by
  have key : ∀ l, ∃ o, OptComp C (ρ₁.get l) (ρ₂.get l) o ∧
      OptComp C o (ρ₃.get l) (w.get l) :=
    fun l => OptComp.assoc_left hC (h₂₃.2 l) (h₁x.2 l)
  have choice : ∃ f : Loc → Option X, ∀ l,
      OptComp C (ρ₁.get l) (ρ₂.get l) (f l) ∧ OptComp C (f l) (ρ₃.get l) (w.get l) :=
    ⟨fun l => (key l).choose, fun l => (key l).choose_spec⟩
  obtain ⟨f, hf⟩ := choice
  have fin : FinDom f := by
    obtain ⟨d₁, k₁⟩ := ρ₁.finite
    obtain ⟨d₂, k₂⟩ := ρ₂.finite
    refine ⟨d₁ ++ d₂, fun l hl => ?_⟩
    cases e₁ : ρ₁.get l with
    | some ψ => exact List.mem_append.mpr (Or.inl (k₁ l (by rw [e₁]; simp)))
    | none =>
        cases e₂ : ρ₂.get l with
        | some ψ => exact List.mem_append.mpr (Or.inr (k₂ l (by rw [e₂]; simp)))
        | none =>
            have h := (hf l).1
            rw [e₁, e₂] at h
            exact absurd (show f l = none from h) hl
  refine ⟨⟨f, fin⟩, ⟨?_, fun l => (hf l).1⟩, ⟨?_, fun l => (hf l).2⟩⟩
  · intro l ψ₁ ψ₂ e₁ e₂
    have h := (hf l).1
    rw [e₁, e₂] at h
    obtain ⟨ψ, -, hc⟩ : ∃ ψ, f l = some ψ ∧ C ψ₁ ψ₂ ψ := h
    exact hR _ _ _ hc
  · intro l ψ ψ₃ e e₃
    have h := (hf l).2
    have e' : f l = some ψ := e
    rw [e', e₃] at h
    obtain ⟨ω, -, hc⟩ : ∃ ω, w.get l = some ω ∧ C ψ ψ₃ ω := h
    exact hR _ _ _ hc

theorem OptComp.swap (o₁ o₂ o : Option X) :
    OptComp (fun a b c => C b a c) o₁ o₂ o ↔ OptComp C o₂ o₁ o := by
  cases o₁ <;> cases o₂ <;> exact Iff.rfl

theorem Comp.swap (ρ₁ ρ₂ ρ : PMap Loc X) :
    Comp (fun a b => R b a) (fun a b c => C b a c) ρ₁ ρ₂ ρ ↔ Comp R C ρ₂ ρ₁ ρ := by
  constructor
  · exact fun h => ⟨fun l ψ₁ ψ₂ e₁ e₂ => h.1 l ψ₂ ψ₁ e₂ e₁,
      fun l => (OptComp.swap _ _ _).mp (h.2 l)⟩
  · exact fun h => ⟨fun l ψ₁ ψ₂ e₁ e₂ => h.1 l ψ₂ ψ₁ e₂ e₁,
      fun l => (OptComp.swap _ _ _).mpr (h.2 l)⟩

/-- `[TR]` Lemma 6.3 over the schema, as a Kleene equality. -/
theorem Comp.assoc (hR : ∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → R ψ₁ ψ₂)
    (hC : ∀ ψ₁ ψ₂ ψ₃ ω, (∃ χ, C ψ₂ ψ₃ χ ∧ C ψ₁ χ ω) ↔ (∃ υ, C ψ₁ ψ₂ υ ∧ C υ ψ₃ ω))
    (ρ₁ ρ₂ ρ₃ w : PMap Loc X) :
    (∃ x, Comp R C ρ₂ ρ₃ x ∧ Comp R C ρ₁ x w) ↔
    (∃ y, Comp R C ρ₁ ρ₂ y ∧ Comp R C y ρ₃ w) := by
  constructor
  · rintro ⟨x, h₂₃, h₁x⟩
    exact Comp.assoc_left hR (fun a b c d => (hC a b c d).mp) h₂₃ h₁x
  · rintro ⟨y, h₁₂, hy₃⟩
    obtain ⟨x, hx, hw⟩ :=
      Comp.assoc_left (R := fun a b => R b a) (C := fun a b c => C b a c)
        (fun ψ₁ ψ₂ ψ h => hR ψ₂ ψ₁ ψ h)
        (fun ψ₁ ψ₂ ψ₃ ω h => (hC ψ₃ ψ₂ ψ₁ ω).mpr h)
        ((Comp.swap _ _ _).mpr h₁₂) ((Comp.swap _ _ _).mpr hy₃)
    exact ⟨x, (Comp.swap _ _ _).mp hx, (Comp.swap _ _ _).mp hw⟩

/-- `[TR]` Lemma 6.4 over the schema: `dom(ρ) ∩ ∅ = ∅`. -/
theorem comp_empty_right (ρ : PMap Loc X) : Comp R C ρ PMap.empty ρ := by
  refine ⟨Compat.of_disjoint (fun _ => Or.inr rfl), fun l => ?_⟩
  show OptComp C (ρ.get l) none (ρ.get l)
  cases e : ρ.get l with
  | none => rfl
  | some ψ => rfl

theorem Comp.functional (hC : ∀ ψ₁ ψ₂ ψ ψ', C ψ₁ ψ₂ ψ → C ψ₁ ψ₂ ψ' → ψ = ψ')
    {ρ₁ ρ₂ ρ ρ' : PMap Loc X} (h : Comp R C ρ₁ ρ₂ ρ) (h' : Comp R C ρ₁ ρ₂ ρ') : ρ = ρ' := by
  refine PMap.ext fun l => ?_
  have h₁ := h.2 l
  have h₂ := h'.2 l
  cases e₁ : ρ₁.get l <;> cases e₂ : ρ₂.get l <;> rw [e₁, e₂] at h₁ h₂
  · rw [h₁, h₂]
  · rw [h₁, h₂]
  · rw [h₁, h₂]
  · obtain ⟨ψa, ha, hCa⟩ := h₁
    obtain ⟨ψb, hb, hCb⟩ := h₂
    rw [ha, hb, hC _ _ _ _ hCa hCb]

/-- The three-way union at one location, as a function of the guard. -/
def optCompF (f : (ψ₁ ψ₂ : X) → R ψ₁ ψ₂ → X) : (o₁ o₂ : Option X) →
    (∀ ψ₁ ψ₂, o₁ = some ψ₁ → o₂ = some ψ₂ → R ψ₁ ψ₂) → Option X
  | none, none, _ => none
  | some ψ, none, _ => some ψ
  | none, some ψ, _ => some ψ
  | some ψ₁, some ψ₂, h => some (f ψ₁ ψ₂ (h ψ₁ ψ₂ rfl rfl))

/-- `ρ₁ ◐ ρ₂` as a function of its guard. -/
def compF (f : (ψ₁ ψ₂ : X) → R ψ₁ ψ₂ → X) (ρ₁ ρ₂ : PMap Loc X) (h : Compat R ρ₁ ρ₂) :
    PMap Loc X where
  get := fun l => optCompF f (ρ₁.get l) (ρ₂.get l) (fun ψ₁ ψ₂ e₁ e₂ => h l ψ₁ ψ₂ e₁ e₂)
  finite := by
    obtain ⟨d₁, k₁⟩ := ρ₁.finite
    obtain ⟨d₂, k₂⟩ := ρ₂.finite
    refine ⟨d₁ ++ d₂, fun l hl => ?_⟩
    cases e₁ : ρ₁.get l with
    | none =>
        cases e₂ : ρ₂.get l with
        | none =>
            exfalso; apply hl
            show optCompF f (ρ₁.get l) (ρ₂.get l) _ = none
            generalize (fun ψ₁ ψ₂ (e₁' : ρ₁.get l = some ψ₁) (e₂' : ρ₂.get l = some ψ₂) =>
              h l ψ₁ ψ₂ e₁' e₂') = k
            revert k
            rw [e₁, e₂]
            intro k
            rfl
        | some ψ => exact List.mem_append.mpr (Or.inr (k₂ l (by rw [e₂]; simp)))
    | some ψ => exact List.mem_append.mpr (Or.inl (k₁ l (by rw [e₁]; simp)))

theorem compF_spec (f : (ψ₁ ψ₂ : X) → R ψ₁ ψ₂ → X) (hf : ∀ ψ₁ ψ₂ h, C ψ₁ ψ₂ (f ψ₁ ψ₂ h))
    (ρ₁ ρ₂ : PMap Loc X) (h : Compat R ρ₁ ρ₂) : Comp R C ρ₁ ρ₂ (compF f ρ₁ ρ₂ h) := by
  refine ⟨h, fun l => ?_⟩
  show OptComp C (ρ₁.get l) (ρ₂.get l) (optCompF f (ρ₁.get l) (ρ₂.get l) _)
  generalize (fun ψ₁ ψ₂ (e₁ : ρ₁.get l = some ψ₁) (e₂ : ρ₂.get l = some ψ₂) =>
    h l ψ₁ ψ₂ e₁ e₂) = k
  revert k
  cases ρ₁.get l <;> cases ρ₂.get l <;> intro k
  · rfl
  · rfl
  · rfl
  · exact ⟨_, rfl, hf _ _ _⟩

end G

/-! ### At the tree-stratified carrier -/

variable {Loc Val : Type} {K : WCactus}

/-- `ρ₁ ▶◀ ρ₂`. -/
abbrev ResUT.CompatS (ρ₁ ρ₂ : ResUT Loc Val K) : Prop := G.Compat CellUT.CompatS ρ₁ ρ₂
/-- `ρ₁ ● ρ₂ = ρ`. -/
abbrev ResUT.CompS (ρ₁ ρ₂ ρ : ResUT Loc Val K) : Prop :=
  G.Comp CellUT.CompatS CellUT.CompS ρ₁ ρ₂ ρ
/-- `ρ₁ ⋈ ρ₂`. -/
abbrev ResUT.CompatR (ρ₁ ρ₂ : ResUT Loc Val K) : Prop := G.Compat CellUT.CompatR ρ₁ ρ₂
/-- `ρ₁ ○ ρ₂ = ρ`. -/
abbrev ResUT.CompR (ρ₁ ρ₂ ρ : ResUT Loc Val K) : Prop :=
  G.Comp CellUT.CompatR CellUT.CompR ρ₁ ρ₂ ρ

/-- `ex(ρ)_●`. -/
abbrev ExST (ρ σ : ResUT Loc Val K) : Prop :=
  G.ExW CellUT.kind CellUT.wit CellUT.CompatS CellUT.CompS ρ σ
/-- `ex(ρ)_○`. -/
abbrev ExRT (ρ σ : ResUT Loc Val K) : Prop :=
  G.ExW CellUT.kind CellUT.wit CellUT.CompatR CellUT.CompR ρ σ
/-- `ag(ρ)`. -/
abbrev AgWT (ρ σ : ResUT Loc Val K) : Prop :=
  G.AgW CellUT.kind CellUT.wit CellUT.CompatR CellUT.CompR ρ σ
/-- `⦇ρ⦈ = σ`. -/
abbrev ResUT.Flat (ρ σ : ResUT Loc Val K) : Prop :=
  G.Flat CellUT.kind CellUT.wit CellUT.CompatR CellUT.CompR CellUT.CompatS CellUT.CompS ρ σ
/-- `✓ρ`. -/
abbrev ResUT.Valid (ρ : ResUT Loc Val K) : Prop :=
  G.Valid CellUT.kind CellUT.wit CellUT.CompatR CellUT.CompR CellUT.CompatS CellUT.CompS ρ
/-- `ρ₁ # ρ₂`. -/
abbrev ResUT.Hash (ρ₁ ρ₂ : ResUT Loc Val K) : Prop :=
  G.Hash CellUT.kind CellUT.wit CellUT.CompatR CellUT.CompR CellUT.CompatS CellUT.CompS ρ₁ ρ₂

/-- The cell-level facts the schema rests on: single-valuedness and the cell halves of 6.2,
6.3 (as `ResU.CompLaws`). -/
structure CompLawsT (C : CellUT Loc Val K → CellUT Loc Val K → CellUT Loc Val K → Prop) :
    Prop where
  functional : ∀ ψ₁ ψ₂ ψ ψ', C ψ₁ ψ₂ ψ → C ψ₁ ψ₂ ψ' → ψ = ψ'
  comm : ∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → C ψ₂ ψ₁ ψ
  assoc : ∀ ψ₁ ψ₂ ψ₃ ω, (∃ χ, C ψ₂ ψ₃ χ ∧ C ψ₁ χ ω) ↔ (∃ υ, C ψ₁ ψ₂ υ ∧ C υ ψ₃ ω)

/-- The laws at `●`. -/
theorem compLawsST : CompLawsT (Loc := Loc) (Val := Val) (K := K) CellUT.CompS where
  functional := fun _ _ _ _ a b => CellUT.CompS.functional a b
  comm := fun _ _ _ a => a.comm
  assoc := CellUT.compS_assoc

/-- The laws at `○`, clause 3 restated. -/
theorem compLawsRT : CompLawsT (Loc := Loc) (Val := Val) (K := K) CellUT.CompR where
  functional := fun _ _ _ _ a b => CellUT.CompR.functional a b
  comm := fun _ _ _ a => a.comm
  assoc := CellUT.compR_assoc

/-- `[TR]` Lemma 6.1 at `▶◀`. -/
theorem ResUT.compatS_comm_iff (ρ₁ ρ₂ : ResUT Loc Val K) :
    ResUT.CompatS ρ₁ ρ₂ ↔ ResUT.CompatS ρ₂ ρ₁ :=
  ⟨G.Compat.comm (fun _ _ a => a.symm), G.Compat.comm (fun _ _ a => a.symm)⟩

/-- `[TR]` Lemma 6.1 at `⋈`. -/
theorem ResUT.compatR_comm_iff (ρ₁ ρ₂ : ResUT Loc Val K) :
    ResUT.CompatR ρ₁ ρ₂ ↔ ResUT.CompatR ρ₂ ρ₁ :=
  ⟨G.Compat.comm (fun _ _ a => a.symm), G.Compat.comm (fun _ _ a => a.symm)⟩

/-- `[TR]` Lemma 6.2 at `●`. -/
theorem ResUT.CompS.comm {ρ₁ ρ₂ ρ : ResUT Loc Val K} (h : ResUT.CompS ρ₁ ρ₂ ρ) :
    ResUT.CompS ρ₂ ρ₁ ρ :=
  G.Comp.comm (fun _ _ a => a.symm) (fun _ _ _ a => a.comm) h

/-- `[TR]` Lemma 6.2 at `○`. -/
theorem ResUT.CompR.comm {ρ₁ ρ₂ ρ : ResUT Loc Val K} (h : ResUT.CompR ρ₁ ρ₂ ρ) :
    ResUT.CompR ρ₂ ρ₁ ρ :=
  G.Comp.comm (fun _ _ a => a.symm) (fun _ _ _ a => a.comm) h

/-- `[TR]` Lemma 6.3 at `●`. -/
theorem ResUT.CompS.assoc (ρ₁ ρ₂ ρ₃ w : ResUT Loc Val K) :
    (∃ x, ResUT.CompS ρ₂ ρ₃ x ∧ ResUT.CompS ρ₁ x w) ↔
    (∃ y, ResUT.CompS ρ₁ ρ₂ y ∧ ResUT.CompS y ρ₃ w) :=
  G.Comp.assoc (fun _ _ _ h => h.compat) CellUT.compS_assoc ρ₁ ρ₂ ρ₃ w

/-- `[TR]` Lemma 6.3 at `○`. -/
theorem ResUT.CompR.assoc (ρ₁ ρ₂ ρ₃ w : ResUT Loc Val K) :
    (∃ x, ResUT.CompR ρ₂ ρ₃ x ∧ ResUT.CompR ρ₁ x w) ↔
    (∃ y, ResUT.CompR ρ₁ ρ₂ y ∧ ResUT.CompR y ρ₃ w) :=
  G.Comp.assoc (fun _ _ _ h => ⟨_, h⟩) CellUT.compR_assoc ρ₁ ρ₂ ρ₃ w

/-- `[TR]` Lemma 6.4 at `●`. -/
theorem ResUT.compS_empty_right (ρ : ResUT Loc Val K) : ResUT.CompS ρ PMap.empty ρ :=
  G.comp_empty_right ρ

/-- `[TR]` Lemma 6.4 at `○`. -/
theorem ResUT.compR_empty_right (ρ : ResUT Loc Val K) : ResUT.CompR ρ PMap.empty ρ :=
  G.comp_empty_right ρ

/-- `[TR]` Lemma 6.5: "immediate by definition". -/
theorem ResUT.hash_empty_right {ρ : ResUT Loc Val K} (h : ResUT.Valid ρ) :
    ResUT.Hash ρ PMap.empty :=
  ⟨G.Compat.of_disjoint (fun _ => Or.inr rfl), ρ, ResUT.compS_empty_right ρ, h⟩

/-- `[TR]` Lemma 6.6, one direction: from Lemma 6.2. -/
theorem ResUT.hash_symm {ρ₁ ρ₂ : ResUT Loc Val K} (h : ResUT.Hash ρ₁ ρ₂) :
    ResUT.Hash ρ₂ ρ₁ := by
  obtain ⟨hc, ρ, hcomp, hv⟩ := h
  exact ⟨(ResUT.compatS_comm_iff _ _).mp hc, ρ, ResUT.CompS.comm hcomp, hv⟩

/-- `[TR]` Lemma 6.6. -/
theorem ResUT.hash_symm_iff (ρ₁ ρ₂ : ResUT Loc Val K) :
    ResUT.Hash ρ₁ ρ₂ ↔ ResUT.Hash ρ₂ ρ₁ := ⟨ResUT.hash_symm, ResUT.hash_symm⟩

/-- `[TR]` Lemma 6.9: `ρ₁ ▶◀ ρ₂` iff `ρ₁ ● ρ₂` is defined. -/
theorem ResUT.compS_defined_iff (ρ₁ ρ₂ : ResUT Loc Val K) :
    (∃ ρ, ResUT.CompS ρ₁ ρ₂ ρ) ↔ ResUT.CompatS ρ₁ ρ₂ :=
  ⟨fun ⟨_, h⟩ => h.1, fun h => ⟨_, G.compF_spec _ CellUT.compS_spec ρ₁ ρ₂ h⟩⟩

theorem ResUT.CompS.functional {ρ₁ ρ₂ ρ ρ' : ResUT Loc Val K}
    (h : ResUT.CompS ρ₁ ρ₂ ρ) (h' : ResUT.CompS ρ₁ ρ₂ ρ') : ρ = ρ' :=
  G.Comp.functional (R := CellUT.CompatS) (C := CellUT.CompS)
    (fun _ _ _ _ a b => CellUT.CompS.functional a b) h h'

theorem ResUT.CompR.functional {ρ₁ ρ₂ ρ ρ' : ResUT Loc Val K}
    (h : ResUT.CompR ρ₁ ρ₂ ρ) (h' : ResUT.CompR ρ₁ ρ₂ ρ') : ρ = ρ' :=
  G.Comp.functional (R := CellUT.CompatR) (C := CellUT.CompR)
    (fun _ _ _ _ a b => CellUT.CompR.functional a b) h h'

/-- `ρ ○ ρ = ρ`, clause (1) read pointwise. -/
theorem ResUT.compR_self (ρ : ResUT Loc Val K) : ResUT.CompR ρ ρ ρ := by
  refine ⟨fun l ψ₁ ψ₂ e₁ e₂ => ?_, fun l => ?_⟩
  · rw [e₁] at e₂
    cases Option.some.inj e₂
    exact ⟨_, CellUT.CompR.same _⟩
  · show G.OptComp CellUT.CompR (ρ.get l) (ρ.get l) (ρ.get l)
    cases e : ρ.get l with
    | none => rfl
    | some ψ => exact ⟨ψ, rfl, CellUT.CompR.same ψ⟩

end BoCa.Fig16.Tree

end
