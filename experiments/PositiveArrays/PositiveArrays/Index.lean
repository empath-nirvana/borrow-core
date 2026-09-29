import Core

/-!
# PositiveArrays — the indexed tensor over a finite set of places

`⊗_{i ∈ I} A_i`, read at the model, is the iterated separating conjunction of its leaves over
the places `I` names. `sepList P ls = P ℓ₁ ⋆ … ⋆ P ℓ_k` for a list `ls = [ℓ₁, …, ℓ_k]` of
locations is that conjunction for any finite index set. Two instances matter:

- **a run-time range**, `rangeLocs ℓ n = [ℓ, …, ℓ + n − 1]`: an array or a slice `(ℓ, n)`, whose
  relation is `sepRange` (`sepRange_eq_sepList`);
- **a static list of leaves**: a struct's block (`experiments/LeafPlaces`, SPEC §5), or any
  static subset of its fields.

A partition of the index set is a split of the list (`sepList_append`, `sepList_perm`): a
contiguous run-time split is `rangeLocs_append`, a static subset of fields is a sublist up to
permutation, and a stride is `rangeLocs` of a stepped range (not built).
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core.PositiveArrays
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo

/-- `⊛_{ℓ ∈ ls} P ℓ`. -/
def sepList (P : Loc → WProp) : List Loc → WProp
  | [] => emp
  | ℓ :: ls => sep (P ℓ) (sepList P ls)

/-- `[ℓ, ℓ + 1, …, ℓ + n − 1]`. -/
def rangeLocs : Loc → Nat → List Loc
  | _, 0 => []
  | ℓ, n + 1 => ℓ :: rangeLocs (ℓ + 1) n

/-- An array's relation is the indexed tensor over its range. -/
theorem sepRange_eq_sepList (P : Loc → WProp) : ∀ (ℓ : Loc) (n : Nat),
    sepRange P ℓ n = sepList P (rangeLocs ℓ n)
  | _, 0 => rfl
  | ℓ, n + 1 => by
      show sep (P ℓ) (sepRange P (ℓ + 1) n) = sep (P ℓ) (sepList P (rangeLocs (ℓ + 1) n))
      rw [sepRange_eq_sepList P (ℓ + 1) n]

theorem rangeLocs_append : ∀ (ℓ : Loc) (i k : Nat),
    rangeLocs ℓ (i + k) = rangeLocs ℓ i ++ rangeLocs (ℓ + i) k
  | ℓ, 0, k => by simp [rangeLocs]
  | ℓ, i + 1, k => by
      rw [show i + 1 + k = (i + k) + 1 by omega]
      simp only [rangeLocs, List.cons_append]
      rw [rangeLocs_append (ℓ + 1) i k, show ℓ + 1 + i = ℓ + (i + 1) by ring]

/-- A split of the index set is a split of the tensor. -/
theorem sepList_append {P : Loc → WProp} :
    ∀ (l₁ l₂ : List Loc) (ρ : WRes),
      sepList P (l₁ ++ l₂) ρ ↔ (sepList P l₁ ⋆ sepList P l₂) ρ
  | [], l₂, ρ => by
      constructor
      · intro h; exact ⟨PMap.empty, ρ, compS_empty_left ρ, ⟨rfl, trivial⟩, h⟩
      · rintro ⟨ρ₁, ρ₂, hc, ⟨rfl, -⟩, h⟩
        rw [eq_of_compS_empty_left hc] at *; exact h
  | ℓ :: l₁, l₂, ρ => by
      constructor
      · rintro ⟨ρa, ρb, hc, ha, hb⟩
        obtain ⟨ρ₁, ρ₂, hc', h₁, h₂⟩ := (sepList_append l₁ l₂ ρb).mp hb
        obtain ⟨x, hx, hρ⟩ := compS_reassoc' hc' hc
        exact ⟨x, ρ₂, hρ, ⟨ρa, ρ₁, hx, ha, h₁⟩, h₂⟩
      · rintro ⟨ρ₁, ρ₂, hc, ⟨ρa, ρb, hab, ha, hb⟩, h₂⟩
        obtain ⟨x, hx, hρ⟩ := compS_reassoc hab hc
        exact ⟨ρa, x, hρ, ha, (sepList_append l₁ l₂ x).mpr ⟨ρb, ρ₂, hx, hb, h₂⟩⟩

/-- The order of the index set does not matter. -/
theorem sepList_perm {P : Loc → WProp} {l₁ l₂ : List Loc} (hp : l₁.Perm l₂) :
    ∀ ρ, sepList P l₁ ρ → sepList P l₂ ρ := by
  induction hp with
  | nil => exact fun _ h => h
  | cons x _ ih =>
      rintro ρ ⟨ρ₁, ρ₂, hc, h₁, h₂⟩
      exact ⟨ρ₁, ρ₂, hc, h₁, ih ρ₂ h₂⟩
  | swap x y l =>
      rintro ρ ⟨ρ₁, ρ₂, hc, h₁, ρ₃, ρ₄, hc', h₃, h₄⟩
      obtain ⟨z, hz, hρ⟩ := compS_lcomm hc' hc
      exact ⟨ρ₃, z, hρ, h₃, ρ₁, ρ₄, hz, h₁, h₄⟩
  | trans _ _ ih₁ ih₂ => exact fun ρ h => ih₂ ρ (ih₁ ρ h)

/-- A property closed under `●` and holding at `∅` holds of a tensor whose leaves have it. -/
theorem sepList_closed {R : WRes → Prop} (h0 : R PMap.empty)
    (hc : ∀ ρ₁ ρ₂ ρ, ResU.CompS ρ₁ ρ₂ ρ → R ρ₁ → R ρ₂ → R ρ) {P : Loc → WProp}
    (hP : ∀ m ρ, P m ρ → R ρ) : ∀ {l : List Loc} {ρ : WRes}, sepList P l ρ → R ρ
  | [], _, ⟨rfl, _⟩ => h0
  | _ :: _, _, ⟨_, _, hcρ, h₁, h₂⟩ => hc _ _ _ hcρ (hP _ _ h₁) (sepList_closed h0 hc hP h₂)

/-- Leafwise entailment under a property inherited by parts. -/
theorem sepList_mono_down {R : WRes → Prop}
    (hR : ∀ a₁ a₂ a, ResU.CompS a₁ a₂ a → R a → R a₁ ∧ R a₂) {P Q : Loc → WProp}
    (h : ∀ m σ, R σ → P m σ → Q m σ) :
    ∀ {l : List Loc} {ρ : WRes}, R ρ → sepList P l ρ → sepList Q l ρ
  | [], _, _, hP => hP
  | _ :: _, _, hρ, ⟨ρ₁, ρ₂, hc, h₁, h₂⟩ =>
      ⟨ρ₁, ρ₂, hc, h _ _ (hR _ _ _ hc hρ).1 h₁, sepList_mono_down hR h (hR _ _ _ hc hρ).2 h₂⟩

theorem sepList_mono' {P Q : Loc → WProp} (h : ∀ m ρ, P m ρ → Q m ρ) {l : List Loc}
    {ρ : WRes} (hP : sepList P l ρ) : sepList Q l ρ :=
  sepList_mono_down (R := fun _ => True) (fun _ _ _ _ _ => ⟨trivial, trivial⟩)
    (fun m σ _ h' => h m σ h') trivial hP

end BoCa.Fig16.LogRel.Core.PositiveArrays

end
