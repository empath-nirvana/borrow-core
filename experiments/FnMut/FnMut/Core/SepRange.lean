import Paper.S5_Model.Definitions
import Support.Model.Notation
import Support.Model.Propositions
import Support.Model.UpdateFrame
import Support.Model.Update
import Support.Model.Algebra

/-!
# Core — the iterated separating conjunction over a range of locations  `[spec §9]`

`sepRange P ℓ n = P ℓ ⋆ P (ℓ+1) ⋆ … ⋆ P (ℓ+n−1)`, the resource of an array `(ℓ, n)` whose leaf
at `ℓ + i` satisfies `P`. The lemmas are those the relation's clause at `[L]` needs: monotonicity,
properties of resources closed under `●` and holding at `∅`, and the split of a range at one
index.
-/

noncomputable section

namespace BoCa.Fig16.BoLo
open BoCa

/-- `⊛_{i<n} P (ℓ + i)`.  `[spec §9]` -/
def sepRange (P : Loc → WProp) : Loc → Nat → WProp
  | _, 0 => emp
  | ℓ, n + 1 => sep (P ℓ) (sepRange P (ℓ + 1) n)

@[simp] theorem sepRange_zero (P : Loc → WProp) (ℓ : Loc) : sepRange P ℓ 0 = emp := rfl

theorem sepRange_succ (P : Loc → WProp) (ℓ : Loc) (n : Nat) :
    sepRange P ℓ (n + 1) = sep (P ℓ) (sepRange P (ℓ + 1) n) := rfl

/-- Pointwise entailment on the range lifts to the range. -/
theorem sepRange_mono {P Q : Loc → WProp} :
    ∀ {ℓ : Loc} {n : Nat}, (∀ m : Nat, ℓ ≤ m → m < ℓ + n → ∀ ρ, P m ρ → Q m ρ) →
      ∀ ρ, sepRange P ℓ n ρ → sepRange Q ℓ n ρ
  | _, 0, _, _, h => h
  | ℓ, n + 1, hPQ, _, ⟨ρ₁, ρ₂, hc, h₁, h₂⟩ => by
      have hl : (ℓ : Nat) < ℓ + (n + 1) := Nat.lt_add_of_pos_right (Nat.succ_pos n)
      refine ⟨ρ₁, ρ₂, hc, hPQ ℓ (Nat.le_refl _) hl ρ₁ h₁,
        sepRange_mono (fun m hm hm' => hPQ m ?_ ?_) ρ₂ h₂⟩
      · exact Nat.le_of_succ_le hm
      · have : (ℓ : Nat) + 1 + n = ℓ + (n + 1) := by ring
        exact this ▸ hm'

/-- Pointwise entailment everywhere lifts to the range. -/
theorem sepRange_mono' {P Q : Loc → WProp} (h : ∀ m ρ, P m ρ → Q m ρ) {ℓ : Loc} {n : Nat}
    {ρ : WRes} (hP : sepRange P ℓ n ρ) : sepRange Q ℓ n ρ :=
  sepRange_mono (fun m _ _ => h m) ρ hP

/-- Pointwise entailment under a property of resources inherited by parts. -/
theorem sepRange_mono_down {R : WRes → Prop}
    (hR : ∀ a₁ a₂ a, ResU.CompS a₁ a₂ a → R a → R a₁ ∧ R a₂) {P Q : Loc → WProp}
    (h : ∀ m σ, R σ → P m σ → Q m σ) :
    ∀ {ℓ : Loc} {n : Nat} {ρ : WRes}, R ρ → sepRange P ℓ n ρ → sepRange Q ℓ n ρ
  | _, 0, _, _, hP => hP
  | _, _ + 1, _, hρ, ⟨ρ₁, ρ₂, hc, h₁, h₂⟩ =>
      ⟨ρ₁, ρ₂, hc, h _ _ (hR _ _ _ hc hρ).1 h₁, sepRange_mono_down hR h (hR _ _ _ hc hρ).2 h₂⟩

/-- Two ranges over the same locations, read leaf by leaf: a leaf of the first and the
corresponding leaf of the second give a leaf of the output, at the image of the second
resource under a map that preserves `●` and `∅`. Properties inherited by parts may be assumed
of each leaf. -/
theorem sepRange_zip {P Q Z : Loc → WProp} {RA RB : WRes → Prop} {f : WRes → WRes}
    (hRA : ∀ a₁ a₂ a, ResU.CompS a₁ a₂ a → RA a → RA a₁ ∧ RA a₂)
    (hRB : ∀ a₁ a₂ a, ResU.CompS a₁ a₂ a → RB a → RB a₁ ∧ RB a₂)
    (hf : ∀ a₁ a₂ a, ResU.CompS a₁ a₂ a → ResU.CompS (f a₁) (f a₂) (f a))
    (hf0 : f PMap.empty = PMap.empty) :
    ∀ {ℓ : Loc} {n : Nat} {A B : WRes},
      (∀ m : Nat, ℓ ≤ m → m < ℓ + n → ∀ a b, RA a → RB b → P m a → Q m b → Z m (f b)) →
      RA A → RB B → sepRange P ℓ n A → sepRange Q ℓ n B → sepRange Z ℓ n (f B)
  | _, 0, _, _, _, _, _, _, ⟨e, _⟩ => by subst e; rw [hf0]; exact ⟨rfl, trivial⟩
  | ℓ, n + 1, _, _, h, hA, hB, ⟨a₁, a₂, hca, ha₁, ha₂⟩, ⟨b₁, b₂, hcb, hb₁, hb₂⟩ => by
      have hl : (ℓ : Nat) < ℓ + (n + 1) := Nat.lt_add_of_pos_right (Nat.succ_pos n)
      refine ⟨f b₁, f b₂, hf _ _ _ hcb,
        h ℓ (Nat.le_refl _) hl a₁ b₁ (hRA _ _ _ hca hA).1 (hRB _ _ _ hcb hB).1 ha₁ hb₁, ?_⟩
      refine sepRange_zip hRA hRB hf hf0 (fun m hm hm' => h m ?_ ?_)
        (hRA _ _ _ hca hA).2 (hRB _ _ _ hcb hB).2 ha₂ hb₂
      · exact Nat.le_of_succ_le hm
      · have : (ℓ : Nat) + 1 + n = ℓ + (n + 1) := by ring
        exact this ▸ hm'

/-- A property of resources that holds at `∅` and is closed under `●` holds of a range whose
every leaf has it. -/
theorem sepRange_closed {R : WRes → Prop} (h0 : R PMap.empty)
    (hc : ∀ ρ₁ ρ₂ ρ, ResU.CompS ρ₁ ρ₂ ρ → R ρ₁ → R ρ₂ → R ρ) {P : Loc → WProp}
    (hP : ∀ m ρ, P m ρ → R ρ) : ∀ {ℓ : Loc} {n : Nat} {ρ : WRes}, sepRange P ℓ n ρ → R ρ
  | _, 0, _, ⟨rfl, _⟩ => h0
  | _, _ + 1, _, ⟨_, _, hcρ, h₁, h₂⟩ => hc _ _ _ hcρ (hP _ _ h₁) (sepRange_closed h0 hc hP h₂)

/-- Two adjacent ranges make one. -/
theorem sepRange_append {P : Loc → WProp} :
    ∀ {ℓ : Loc} {i k : Nat} {ρ₁ ρ₂ ρ : WRes}, ResU.CompS ρ₁ ρ₂ ρ →
      sepRange P ℓ i ρ₁ → sepRange P (ℓ + i) k ρ₂ → sepRange P ℓ (i + k) ρ
  | ℓ, 0, k, ρ₁, ρ₂, ρ, hc, ⟨e, _⟩, h₂ => by
      subst e
      rw [eq_of_compS_empty_left hc, Nat.zero_add]
      simpa using h₂
  | ℓ, i + 1, k, ρ₁, ρ₂, ρ, hc, ⟨σ₁, σ₂, hσ, h₁, h₂⟩, h₃ => by
      obtain ⟨τ, hτ, hρ⟩ := compS_reassoc hσ hc
      have e : ℓ + (i + 1) = ℓ + 1 + i := by ring
      rw [e] at h₃
      have := sepRange_append hτ h₂ h₃
      rw [show i + 1 + k = (i + k) + 1 by ring]
      exact ⟨σ₁, τ, hρ, h₁, this⟩

/-- A range splits at a length `i ≤ n`. -/
theorem sepRange_split {P : Loc → WProp} :
    ∀ {ℓ : Loc} {i k : Nat} {ρ : WRes}, sepRange P ℓ (i + k) ρ →
      ∃ ρ₁ ρ₂, ResU.CompS ρ₁ ρ₂ ρ ∧ sepRange P ℓ i ρ₁ ∧ sepRange P (ℓ + i) k ρ₂
  | ℓ, 0, k, ρ, h => ⟨PMap.empty, ρ, compS_empty_left ρ, ⟨rfl, trivial⟩, by simpa using h⟩
  | ℓ, i + 1, k, ρ, h => by
      rw [show i + 1 + k = (i + k) + 1 by ring] at h
      obtain ⟨σ₁, σ₂, hσ, h₁, h₂⟩ := h
      obtain ⟨τ₁, τ₂, hτ, h₃, h₄⟩ := sepRange_split (ℓ := ℓ + 1) (i := i) h₂
      obtain ⟨x, hx, hρ⟩ := compS_reassoc' hτ hσ
      refine ⟨x, τ₂, hρ, ⟨σ₁, τ₁, hx, h₁, h₃⟩, ?_⟩
      rwa [show ℓ + (i + 1) = ℓ + 1 + i by ring]

/-- The leaf at `ℓ + i`, with the rest of the range framed: the range is `P (ℓ+i)` beside the
two ranges on either side. -/
theorem sepRange_pick {P : Loc → WProp} {ℓ : Loc} {n i : Nat} (hi : i < n) {ρ : WRes}
    (h : sepRange P ℓ n ρ) :
    ∃ ρi ρr, ResU.CompS ρi ρr ρ ∧ P (ℓ + i) ρi ∧
      ∀ σ ρ', ResU.CompS σ ρr ρ' → P (ℓ + i) σ → sepRange P ℓ n ρ' := by
  have hn : n = i + ((n - i - 1) + 1) := by omega
  rw [hn] at h
  obtain ⟨ρa, ρb, hab, ha, ρi, ρc, hic, hi', hc⟩ := sepRange_split h
  obtain ⟨ρr, hr, hρ⟩ := compS_lcomm hic hab
  refine ⟨ρi, ρr, hρ, hi', fun σ ρ' hσ hP => ?_⟩
  obtain ⟨σc, hσc, hρ'⟩ := compS_lcomm hr hσ
  rw [hn]
  exact sepRange_append hρ' ha ⟨σ, ρc, hσc, hP, hc⟩

/-- The leaf at `ℓ + i` is a part of the range. -/
theorem sepRange_le {P : Loc → WProp} {ℓ : Loc} {n i : Nat} (hi : i < n) {ρ : WRes}
    (h : sepRange P ℓ n ρ) : ∃ ρi, P (ℓ + i) ρi ∧ ResU.Le ρi ρ := by
  obtain ⟨ρi, ρr, hc, hP, -⟩ := sepRange_pick hi h
  exact ⟨ρi, hP, ρr, hc⟩

/-- A cell of a range is a cell of one of its leaves. -/
theorem sepRange_get {P : Loc → WProp} :
    ∀ {ℓ : Loc} {n : Nat} {ρ : WRes}, sepRange P ℓ n ρ → ∀ {m : Loc} {ψ : CellU Loc Val},
      ρ.get m = some ψ →
      ∃ i, i < n ∧ ∃ ρi ψi, P (ℓ + i) ρi ∧ ρi.get m = some ψi ∧ ResU.Le ρi ρ
  | _, 0, _, ⟨e0, _⟩, m, ψ, e => by subst e0; simp at e
  | ℓ, n + 1, ρ, ⟨ρ₁, ρ₂, hc, h₁, h₂⟩, m, ψ, e => by
      rcases ResU.Comp.get hc m with ⟨-, -, e'⟩ | ⟨ζ, e₁, -, -⟩ | ⟨ζ, -, e₂, -⟩ |
          ⟨ζ₁, ζ₂, ζ, e₁, -, -, -⟩
      · rw [e'] at e; cases e
      · exact ⟨0, Nat.succ_pos n, ρ₁, _, by simpa using h₁, e₁, ρ₂, hc⟩
      · obtain ⟨i, hi, ρi, ψi, hP, hg, hle⟩ := sepRange_get h₂ e₂
        refine ⟨i + 1, Nat.succ_lt_succ hi, ρi, ψi, ?_, hg,
          hle.trans ⟨ρ₁, ResU.CompS.comm hc⟩⟩
        rwa [show ℓ + (i + 1) = ℓ + 1 + i by ring]
      · exact ⟨0, Nat.succ_pos n, ρ₁, _, by simpa using h₁, e₁, ρ₂, hc⟩

/-- Two distinct leaves of a range compose, within the range. -/
theorem sepRange_pick2 {P : Loc → WProp} {ℓ : Loc} {n i j : Nat} (hij : i < j) (hj : j < n)
    {ρ : WRes} (h : sepRange P ℓ n ρ) :
    ∃ ρi ρj X, P (ℓ + i) ρi ∧ P (ℓ + j) ρj ∧ ResU.CompS ρi ρj X ∧ ResU.Le X ρ := by
  obtain ⟨k, rfl⟩ : ∃ k, n = (i + 1) + k := ⟨n - (i + 1), by omega⟩
  obtain ⟨j', rfl⟩ : ∃ j', j = (i + 1) + j' := ⟨j - (i + 1), by omega⟩
  have hj' : j' < k := by omega
  obtain ⟨ρa, ρb, hab, ha, hb⟩ := sepRange_split h
  obtain ⟨ρa₁, ρa₂, ha₁₂, -, ρi, ρe, hie, hPi, he⟩ := sepRange_split (i := i) (k := 1) ha
  obtain ⟨ρj, hPj, Y₂, hY₂⟩ := sepRange_le hj' hb
  have hρe : ρe = PMap.empty := he.1
  rw [hρe] at hie
  have hie' : ρa₂ = ρi := ResU.CompS.functional hie (ResU.comp_empty_right ρi)
  rw [hie'] at ha₁₂
  have hY₁ : ResU.CompS ρi ρa₁ ρa := ResU.CompS.comm ha₁₂
  obtain ⟨bc, hbc, hB₁⟩ := compS_reassoc hY₁ hab
  obtain ⟨yb, hyb, hbc'⟩ := compS_reassoc' hY₂ hbc
  obtain ⟨z, hz, hbc''⟩ := compS_reassoc (ResU.CompS.comm hyb) hbc'
  obtain ⟨X, hX, hR⟩ := compS_reassoc' hbc'' hB₁
  refine ⟨ρi, ρj, X, hPi, ?_, hX, z, hR⟩
  have e : ℓ + (i + 1) + j' = ℓ + (i + 1 + j') := by ring
  rwa [e] at hPj

end BoCa.Fig16.BoLo

end
