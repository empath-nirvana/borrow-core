import Support.Model.Tree.CarrierGraftEx

/-!
# The printed resource vocabulary at the tree-stratified carrier

The names the printed proofs of `[TR]` §6 use (`ResU.Comp`, `ExW`, `AgW`, `ρ∣ι`, `ℓ ↦ ψ`, the
index sets) read at `CellUT K`, so that the files under `Tree/Port/` carry the printed proofs
over with their text. Each is the generic row of `Tree/CarrierRes.lean` at `CellUT K`; nothing
here compares lifetimes.
-/

noncomputable section

namespace BoCa.Fig16.Tree
open BoCa.Fig16

variable {Loc Val : Type} {K : WCactus}

/-- `ρ₁ ◐ ρ₂ = ρ` (row 5.18). -/
abbrev ResUT.Comp (R : CellUT Loc Val K → CellUT Loc Val K → Prop)
    (C : CellUT Loc Val K → CellUT Loc Val K → CellUT Loc Val K → Prop)
    (ρ₁ ρ₂ ρ : ResUT Loc Val K) : Prop := G.Comp R C ρ₁ ρ₂ ρ

/-- `ρ₁ ▸◁ ρ₂` (row 5.17). -/
abbrev ResUT.Compat (C : CellUT Loc Val K → CellUT Loc Val K → Prop)
    (ρ₁ ρ₂ : ResUT Loc Val K) : Prop := G.Compat C ρ₁ ρ₂

/-- The three pieces of `◐` at one location. -/
abbrev OptCompT (C : CellUT Loc Val K → CellUT Loc Val K → CellUT Loc Val K → Prop) :
    Option (CellUT Loc Val K) → Option (CellUT Loc Val K) → Option (CellUT Loc Val K) → Prop :=
  G.OptComp C

/-- `⨀_◐` (row 5.56). -/
abbrev BigCompT (R : CellUT Loc Val K → CellUT Loc Val K → Prop)
    (C : CellUT Loc Val K → CellUT Loc Val K → CellUT Loc Val K → Prop) :
    List (ResUT Loc Val K) → ResUT Loc Val K → Prop := G.BigComp R C

/-- `ex(ρ)_◐ = σ` (row 5.20). -/
abbrev ExWT (R : CellUT Loc Val K → CellUT Loc Val K → Prop)
    (C : CellUT Loc Val K → CellUT Loc Val K → CellUT Loc Val K → Prop) :
    ResUT Loc Val K → ResUT Loc Val K → Prop := G.ExW CellUT.kind CellUT.wit R C

abbrev ExWitsT (R : CellUT Loc Val K → CellUT Loc Val K → Prop)
    (C : CellUT Loc Val K → CellUT Loc Val K → CellUT Loc Val K → Prop) :
    ResUT Loc Val K → List (Loc × ResUT Loc Val K) → Prop := G.ExWits CellUT.kind CellUT.wit R C

abbrev AgWitsMT : ResUT Loc Val K → List (Loc × ResUT Loc Val K) → Prop :=
  G.AgWitsM CellUT.kind CellUT.wit CellUT.CompatR CellUT.CompR

abbrev AgWitsIT : ResUT Loc Val K → List (Loc × ResUT Loc Val K) → Prop :=
  G.AgWitsI CellUT.kind CellUT.wit CellUT.CompatR CellUT.CompR

/-- `ρ∣ι` (row 5.19). -/
abbrev ResUT.restrict (ρ : ResUT Loc Val K) (k : Kind) : ResUT Loc Val K :=
  G.restrict CellUT.kind ρ k

/-- The index set of a tag (row 5.55). -/
abbrev ResUT.Sites (ρ : ResUT Loc Val K) (k : Kind) (d : List Loc) : Prop :=
  G.Sites CellUT.kind ρ k d

/-- `dom(ρ)` as a list (row 5.55). -/
def ResUT.Dom (ρ : ResUT Loc Val K) (d : List Loc) : Prop :=
  d.Nodup ∧ ∀ l, l ∈ d ↔ ∃ ψ, ρ.get l = some ψ

/-- `ρ∣ῑ` for a set of tags (row 5.51). -/
def ResUT.restrictOn (ρ : ResUT Loc Val K) (p : Kind → Bool) : ResUT Loc Val K where
  get := fun l => (ρ.get l).bind fun ψ => if p ψ.kind then some ψ else none
  finite := by
    obtain ⟨d, hd⟩ := ρ.finite
    refine ⟨d, fun l hl => hd l (fun e => hl ?_)⟩
    show (ρ.get l).bind _ = none
    rw [e]; rfl

/-- `ℓ ↦ ψ` (row 5.52). -/
abbrev ResUT.single (l : Loc) (ψ : CellUT Loc Val K) : ResUT Loc Val K := PMap.sng l ψ

open Classical in
@[simp] theorem ResUT.single_get_self (l : Loc) (ψ : CellUT Loc Val K) :
    (ResUT.single l ψ).get l = some ψ := if_pos rfl

open Classical in
/-- `ρ/ℓ` (row 5.53). -/
noncomputable def ResUT.del (ρ : ResUT Loc Val K) (l : Loc) : ResUT Loc Val K where
  get := fun l' => if l' = l then none else ρ.get l'
  finite := by
    obtain ⟨d, hd⟩ := ρ.finite
    refine ⟨d, fun l' h => hd l' (fun e => h ?_)⟩
    show (if l' = l then none else ρ.get l') = none
    by_cases f : l' = l
    · exact if_pos f
    · rw [if_neg f]; exact e

open Classical in
@[simp] theorem ResUT.del_get_self (ρ : ResUT Loc Val K) (l : Loc) :
    (ρ.del l).get l = none := if_pos rfl

theorem ResUT.restrict_eq_some {ρ : ResUT Loc Val K} {k : Kind} {l : Loc}
    {ψ : CellUT Loc Val K} :
    (G.restrict CellUT.kind ρ k).get l = some ψ ↔ (ρ.get l = some ψ ∧ ψ.kind = k) := by
  have hdef : (G.restrict CellUT.kind ρ k).get l
      = (ρ.get l).bind (fun ψ => if ψ.kind = k then some ψ else none) := rfl
  rw [hdef]
  cases hf : ρ.get l with
  | none => simp
  | some ψ' =>
      simp only [Option.bind_some]
      by_cases hk : ψ'.kind = k
      · rw [if_pos hk]
        exact ⟨fun he => by cases Option.some.inj he; exact ⟨rfl, hk⟩, fun he => he.1⟩
      · rw [if_neg hk]
        refine ⟨fun he => absurd he (by simp), fun he => ?_⟩
        cases Option.some.inj he.1
        exact absurd he.2 hk

theorem optRestrictT_eq_none {o : Option (CellUT Loc Val K)} (k : Kind) (e : o = none) :
    (o.bind fun ψ => if ψ.kind = k then some ψ else none) = none := by subst e; rfl

/-- `ρ ≤ ρ′` (row 5.54). -/
def ResUT.Le (ρ σ : ResUT Loc Val K) : Prop := ∃ τ, ResUT.CompS ρ τ σ

/-- `⦇ρ⦈(ℓ) = ψ` (row 5.60). -/
def ResUT.FlatAt (ρ : ResUT Loc Val K) (l : Loc) (ψ : CellUT Loc Val K) : Prop :=
  ∃ σ, ResUT.Flat ρ σ ∧ σ.get l = some ψ

/-- `○` as a function of its guard. -/
noncomputable def CellUT.compR (ψ₁ ψ₂ : CellUT Loc Val K) (h : ψ₁.CompatR ψ₂) :
    CellUT Loc Val K := h.choose

theorem CellUT.compR_spec (ψ₁ ψ₂ : CellUT Loc Val K) (h : ψ₁.CompatR ψ₂) :
    CellUT.CompR ψ₁ ψ₂ (CellUT.compR ψ₁ ψ₂ h) := h.choose_spec

/-- `ρ₁ ⋈ ρ₂` iff `ρ₁ ○ ρ₂` is defined. -/
theorem ResUT.compR_defined_iff (ρ₁ ρ₂ : ResUT Loc Val K) :
    (∃ ρ, ResUT.CompR ρ₁ ρ₂ ρ) ↔ ResUT.CompatR ρ₁ ρ₂ :=
  ⟨fun ⟨_, h⟩ => h.1, fun h => ⟨_, G.compF_spec _ CellUT.compR_spec ρ₁ ρ₂ h⟩⟩

/-- `⟦ρ⟧ = m` (row 5.25), guarded by `✓ρ` through the existential. -/
def ResUT.Lower (ρ : ResUT Loc Val K) (m : Loc → Option Val) : Prop :=
  ∃ σ, ResUT.Flat ρ σ ∧ ∀ l, m l = (σ.get l).map CellUT.erase

/-- `ρ ○ ρ` is `ρ`. -/
theorem ResUT.comp_self_R (ρ : ResUT Loc Val K) : ResUT.CompR ρ ρ ρ := ResUT.compR_self ρ

/-! ### The schema's laws under the printed names -/

/-- A cell relation that is symmetric: `▶◀` and `⋈`. -/
class G.SymmRel {X : Type} (C : X → X → Prop) : Prop where
  symm : ∀ a b, C a b → C b a

instance : G.SymmRel (CellUT.CompatS (Loc := Loc) (Val := Val) (K := K)) := ⟨fun _ _ h => h.symm⟩
instance : G.SymmRel (CellUT.CompatR (Loc := Loc) (Val := Val) (K := K)) := ⟨fun _ _ h => h.symm⟩

/-- `ρ₁ ▸◁ ρ₂` is symmetric (Lemma 6.1), for dot notation on the unfolded form. -/
theorem G.Compat.symm {X : Type} {C : X → X → Prop} [G.SymmRel C] {ρ₁ ρ₂ : PMap Loc X}
    (h : G.Compat C ρ₁ ρ₂) : G.Compat C ρ₂ ρ₁ :=
  G.Compat.comm (fun a b => G.SymmRel.symm a b) h

section
variable {R : CellUT Loc Val K → CellUT Loc Val K → Prop}
variable {C : CellUT Loc Val K → CellUT Loc Val K → CellUT Loc Val K → Prop}

theorem ResUT.Compat.comm (hC : ∀ ψ₁ ψ₂, R ψ₁ ψ₂ → R ψ₂ ψ₁) {ρ₁ ρ₂ : ResUT Loc Val K}
    (h : ResUT.Compat R ρ₁ ρ₂) : ResUT.Compat R ρ₂ ρ₁ := G.Compat.comm hC h

theorem ResUT.Compat.of_disjoint {ρ₁ ρ₂ : ResUT Loc Val K}
    (h : ∀ l, ρ₁.get l = none ∨ ρ₂.get l = none) : ResUT.Compat R ρ₁ ρ₂ :=
  G.Compat.of_disjoint h

theorem ResUT.Comp.get {ρ₁ ρ₂ ρ : ResUT Loc Val K} (h : ResUT.Comp R C ρ₁ ρ₂ ρ) (l : Loc) :
    (ρ₁.get l = none ∧ ρ₂.get l = none ∧ ρ.get l = none)
    ∨ (∃ ψ, ρ₁.get l = some ψ ∧ ρ₂.get l = none ∧ ρ.get l = some ψ)
    ∨ (∃ ψ, ρ₁.get l = none ∧ ρ₂.get l = some ψ ∧ ρ.get l = some ψ)
    ∨ (∃ ψ₁ ψ₂ ψ, ρ₁.get l = some ψ₁ ∧ ρ₂.get l = some ψ₂ ∧ ρ.get l = some ψ ∧
        C ψ₁ ψ₂ ψ) := G.Comp.get h l

theorem ResUT.Comp.comm (hR : ∀ ψ₁ ψ₂, R ψ₁ ψ₂ → R ψ₂ ψ₁)
    (hC : ∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → C ψ₂ ψ₁ ψ) {ρ₁ ρ₂ ρ : ResUT Loc Val K}
    (h : ResUT.Comp R C ρ₁ ρ₂ ρ) : ResUT.Comp R C ρ₂ ρ₁ ρ := G.Comp.comm hR hC h

theorem ResUT.Comp.functional (hC : ∀ ψ₁ ψ₂ ψ ψ', C ψ₁ ψ₂ ψ → C ψ₁ ψ₂ ψ' → ψ = ψ')
    {ρ₁ ρ₂ ρ ρ' : ResUT Loc Val K} (h : ResUT.Comp R C ρ₁ ρ₂ ρ)
    (h' : ResUT.Comp R C ρ₁ ρ₂ ρ') : ρ = ρ' := G.Comp.functional hC h h'

theorem ResUT.Comp.assoc_left (hR : ∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → R ψ₁ ψ₂)
    (hC : ∀ ψ₁ ψ₂ ψ₃ ω, (∃ χ, C ψ₂ ψ₃ χ ∧ C ψ₁ χ ω) → (∃ υ, C ψ₁ ψ₂ υ ∧ C υ ψ₃ ω))
    {ρ₁ ρ₂ ρ₃ x w : ResUT Loc Val K}
    (h₂₃ : ResUT.Comp R C ρ₂ ρ₃ x) (h₁x : ResUT.Comp R C ρ₁ x w) :
    ∃ y, ResUT.Comp R C ρ₁ ρ₂ y ∧ ResUT.Comp R C y ρ₃ w := G.Comp.assoc_left hR hC h₂₃ h₁x

theorem ResUT.Comp.assoc (hR : ∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → R ψ₁ ψ₂)
    (hC : ∀ ψ₁ ψ₂ ψ₃ ω, (∃ χ, C ψ₂ ψ₃ χ ∧ C ψ₁ χ ω) ↔ (∃ υ, C ψ₁ ψ₂ υ ∧ C υ ψ₃ ω))
    (ρ₁ ρ₂ ρ₃ w : ResUT Loc Val K) :
    (∃ x, ResUT.Comp R C ρ₂ ρ₃ x ∧ ResUT.Comp R C ρ₁ x w) ↔
    (∃ y, ResUT.Comp R C ρ₁ ρ₂ y ∧ ResUT.Comp R C y ρ₃ w) := G.Comp.assoc hR hC ρ₁ ρ₂ ρ₃ w

theorem ResUT.Comp.swap (ρ₁ ρ₂ ρ : ResUT Loc Val K) :
    ResUT.Comp (fun a b => R b a) (fun a b c => C b a c) ρ₁ ρ₂ ρ ↔ ResUT.Comp R C ρ₂ ρ₁ ρ :=
  G.Comp.swap ρ₁ ρ₂ ρ

theorem ResUT.comp_empty_right (ρ : ResUT Loc Val K) : ResUT.Comp R C ρ PMap.empty ρ :=
  G.comp_empty_right ρ

theorem OptCompT.assoc_left
    (hC : ∀ ψ₁ ψ₂ ψ₃ ω, (∃ χ, C ψ₂ ψ₃ χ ∧ C ψ₁ χ ω) → (∃ υ, C ψ₁ ψ₂ υ ∧ C υ ψ₃ ω))
    {o₁ o₂ o₃ ox ow : Option (CellUT Loc Val K)}
    (h₂₃ : OptCompT C o₂ o₃ ox) (h₁x : OptCompT C o₁ ox ow) :
    ∃ oy, OptCompT C o₁ o₂ oy ∧ OptCompT C oy o₃ ow := G.OptComp.assoc_left hC h₂₃ h₁x

end

theorem ResUT.CompatS.symm {ρ₁ ρ₂ : ResUT Loc Val K} (h : ResUT.CompatS ρ₁ ρ₂) :
    ResUT.CompatS ρ₂ ρ₁ := G.Compat.comm (fun _ _ a => a.symm) h

theorem ResUT.CompatR.symm {ρ₁ ρ₂ : ResUT Loc Val K} (h : ResUT.CompatR ρ₁ ρ₂) :
    ResUT.CompatR ρ₂ ρ₁ := G.Compat.comm (fun _ _ a => a.symm) h

theorem ResUT.compS_spec (ρ₁ ρ₂ : ResUT Loc Val K) (h : ResUT.CompatS ρ₁ ρ₂) :
    ResUT.CompS ρ₁ ρ₂ (G.compF CellUT.compS ρ₁ ρ₂ h) :=
  G.compF_spec _ CellUT.compS_spec ρ₁ ρ₂ h

end BoCa.Fig16.Tree

end
