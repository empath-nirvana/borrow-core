import Core.Chain.SI.LoanX.ErwpX
/-! Owned registry claims and frame-preserving updates for loan return [spec §62]. -/
noncomputable section
namespace BoCa.Fig16.LogRel.Core.Chain.SI.OwnedLoan
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel.Core
open Classical
abbrev Registry := Loc → Option Ret
@[simp] theorem pos_indicator (p : Prop) [Decidable p] :
    0 < (if p then 1 else 0 : Nat) ↔ p := by
  by_cases h : p <;> simp [h]

def reg (m : Registry) : GRes := { (0 : GRes) with auth := fun m' => if m' = m then 1 else 0 }
def claim (γ : Loc) (d : Ret) : GRes :=
  { (0 : GRes) with tokF := fun a r => if a = γ ∧ r = d then 1 else 0 }
def permit (γ : Loc) (d : Ret) : GRes :=
  { (0 : GRes) with wrF := fun a r => if a = γ ∧ r = d then 1 else 0 }
def put (m : Registry) (γ : Loc) (d : Ret) : Registry := fun a => if a = γ then some d else m a

def FP (g h : GRes) : Prop := ∀ f, (f + g).Valid → (f + h).Valid

@[simp] theorem reg_tok (m : Registry) (a : Life) : (reg m).tok a = 0 := rfl
@[simp] theorem claim_tok (γ : Loc) (d : Ret) (a : Life) : (claim γ d).tok a = 0 := rfl
@[simp] theorem permit_tok (γ : Loc) (d : Ret) (a : Life) : (permit γ d).tok a = 0 := rfl

/-- A frame beside the sole authority owns no authoritative component itself. -/
theorem frame_auth_zero {m : Registry} {f : GRes} (hv : (f + reg m).Valid) :
    ∀ m', f.auth m' = 0 := by
  intro m'
  have hz : f.auth m = 0 := by
    have h := hv.auth_le m
    simp [reg] at h
    exact h
  by_contra hn
  have he : m' = m := hv.auth_one m' m (by
    simp only [GRes.auth_add]; exact lt_of_lt_of_le (Nat.pos_of_ne_zero hn) (Nat.le_add_right _ _))
    (by simp [reg])
  exact hn (he ▸ hz)

theorem frame_tok_agree {m : Registry} {f : GRes} (hv : (f + reg m).Valid)
    {a : Loc} {d : Ret} (hp : 0 < f.tokF a d) : m a = some d :=
  hv.tokF_agree m a d (by simp [reg]) (by simpa [reg] using hp)

theorem frame_wr_agree {m : Registry} {f : GRes} (hv : (f + reg m).Valid)
    {a : Loc} {d : Ret} (hp : 0 < f.wrF a d) : m a = some d :=
  hv.wrF_agree m a d (by simp [reg]) (by simpa [reg] using hp)

/-- Fresh allocation creates the lender and borrower halves together. -/
theorem allocate (m : Registry) (γ : Loc) (d : Ret) (hfresh : m γ = none) :
    FP (reg m) (reg (put m γ d) + claim γ d + permit γ d) := by
  intro f hv
  have ha := frame_auth_zero hv
  have hft : ∀ r, f.tokF γ r = 0 := by
    intro r
    by_contra hn
    have hh := frame_tok_agree hv (Nat.pos_of_ne_zero hn)
    rw [hfresh] at hh
    cases hh
  have hfw : ∀ r, f.wrF γ r = 0 := by
    intro r
    by_contra hn
    have hh := frame_wr_agree hv (Nat.pos_of_ne_zero hn)
    rw [hfresh] at hh
    cases hh
  have hvf := GRes.Valid.left hv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a; simpa [reg, claim, permit] using hvf.tok a
  · intro a; simpa [reg, claim, permit] using hvf.xm a
  · intro m'; simp [reg, claim, permit, ha]; split <;> omega
  · intro m₁ m₂ h₁ h₂
    simp [reg, claim, permit, ha] at h₁ h₂
    exact h₁.trans h₂.symm
  · intro a r
    by_cases he : a = γ
    · subst a; simp [reg, claim, permit, hft]; split <;> omega
    · simpa [reg, claim, permit, he] using hvf.tokF_le a r
  · intro a r r' h₁ h₂
    by_cases he : a = γ
    · subst a
      have h₁' : r = d := by simpa [reg, claim, permit, hft] using h₁
      have h₂' : r' = d := by simpa [reg, claim, permit, hft] using h₂
      exact h₁'.trans h₂'.symm
    · exact hvf.tokF_one a r r' (by simpa [reg, claim, permit, he] using h₁)
        (by simpa [reg, claim, permit, he] using h₂)
  · intro a r
    by_cases he : a = γ
    · subst a; simp [reg, claim, permit, hfw]; split <;> omega
    · simpa [reg, claim, permit, he] using hvf.wrF_le a r
  · intro a r r' h₁ h₂
    by_cases he : a = γ
    · subst a
      have h₁' : r = d := by simpa [reg, claim, permit, hfw] using h₁
      have h₂' : r' = d := by simpa [reg, claim, permit, hfw] using h₂
      exact h₁'.trans h₂'.symm
    · exact hvf.wrF_one a r r' (by simpa [reg, claim, permit, he] using h₁)
        (by simpa [reg, claim, permit, he] using h₂)
  · intro m' a r hm hr
    have hm' : m' = put m γ d := by simpa [reg, claim, permit, ha] using hm
    subst m'
    by_cases he : a = γ
    · subst a
      have hr' : r = d := by simpa [reg, claim, permit, hft] using hr
      subst r; simp [put]
    · have hr' : 0 < f.tokF a r := by simpa [reg, claim, permit, he] using hr
      simpa [put, he] using frame_tok_agree hv hr'
  · intro m' a r hm hr
    have hm' : m' = put m γ d := by simpa [reg, claim, permit, ha] using hm
    subst m'
    by_cases he : a = γ
    · subst a
      have hr' : r = d := by simpa [reg, claim, permit, hfw] using hr
      subst r; simp [put]
    · have hr' : 0 < f.wrF a r := by simpa [reg, claim, permit, he] using hr
      simpa [put, he] using frame_wr_agree hv hr'
  · simpa [reg, claim, permit] using hvf.fin

theorem reg_valid (m : Registry) : (reg m).Valid := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a; simp [reg]
  · intro a; simp [reg]
  · intro m'; simp [reg]; split <;> omega
  · intro m₁ m₂ h₁ h₂
    have he₁ : m₁ = m := by simpa [reg] using h₁
    have he₂ : m₂ = m := by simpa [reg] using h₂
    exact he₁.trans he₂.symm
  · intro a r; simp [reg]
  · intro a r r' h; simp [reg] at h
  · intro a r; simp [reg]
  · intro a r r' h; simp [reg] at h
  · intro m' a r _ h; simp [reg] at h
  · intro m' a r _ h; simp [reg] at h
  · simp [reg]

theorem registered_valid (m : Registry) (γ : Loc) (d : Ret) (hm : m γ = some d) :
    (reg m + claim γ d + permit γ d).Valid := by
  let old : Registry := fun a => if a = γ then none else m a
  have he : put old γ d = m := by
    funext a
    by_cases ha : a = γ
    · subst a; simpa [put, old] using hm.symm
    · simp [put, old, ha]
  have hh := allocate old γ d (by simp [old]) 0 (by simpa using reg_valid old)
  simpa [he] using hh

/-- Both halves are necessary to retire an entry while retaining the authority. -/
theorem close (m : Registry) (γ : Loc) (d : Ret) :
    FP (reg m + claim γ d + permit γ d) (reg (put m γ [])) := by
  intro f hv
  have hvR : (f + reg m).Valid := GRes.Valid.left
    (show ((f + reg m) + (claim γ d + permit γ d)).Valid by
      simpa only [GRes.add_assoc] using hv)
  have ha := frame_auth_zero hvR
  have hvf := GRes.Valid.left hv
  have hft : ∀ r, f.tokF γ r = 0 := by
    intro r
    by_cases he : r = d
    · subst r
      have h := hv.tokF_le γ d
      simp [reg, claim, permit] at h
      exact h
    · by_contra hn
      have hh := hv.tokF_one γ r d (by
        simpa [reg, claim, permit, he] using Nat.pos_of_ne_zero hn) (by simp [reg, claim, permit])
      exact he hh
  have hfw : ∀ r, f.wrF γ r = 0 := by
    intro r
    by_cases he : r = d
    · subst r
      have h := hv.wrF_le γ d
      simp [reg, claim, permit] at h
      exact h
    · by_contra hn
      have hh := hv.wrF_one γ r d (by
        simpa [reg, claim, permit, he] using Nat.pos_of_ne_zero hn) (by simp [reg, claim, permit])
      exact he hh
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a; simpa [reg] using hvf.tok a
  · intro a; simpa [reg] using hvf.xm a
  · intro m'; simp [reg, ha]; split <;> omega
  · intro m₁ m₂ h₁ h₂
    have he₁ : m₁ = put m γ [] := by simpa [reg, ha] using h₁
    have he₂ : m₂ = put m γ [] := by simpa [reg, ha] using h₂
    exact he₁.trans he₂.symm
  · intro a r; simpa [reg] using hvf.tokF_le a r
  · intro a r r' h₁ h₂
    exact hvf.tokF_one a r r' (by simpa [reg] using h₁) (by simpa [reg] using h₂)
  · intro a r; simpa [reg] using hvf.wrF_le a r
  · intro a r r' h₁ h₂
    exact hvf.wrF_one a r r' (by simpa [reg] using h₁) (by simpa [reg] using h₂)
  · intro m' a r hm hr
    have hm' : m' = put m γ [] := by simpa [reg, ha] using hm
    subst m'
    have hr' : 0 < f.tokF a r := by simpa [reg] using hr
    have hne : a ≠ γ := by intro he; subst a; rw [hft] at hr'; omega
    simpa [put, hne] using frame_tok_agree hvR hr'
  · intro m' a r hm hr
    have hm' : m' = put m γ [] := by simpa [reg, ha] using hm
    subst m'
    have hr' : 0 < f.wrF a r := by simpa [reg] using hr
    have hne : a ≠ γ := by intro he; subst a; rw [hfw] at hr'; omega
    simpa [put, hne] using frame_wr_agree hvR hr'
  · simpa [reg] using hvf.fin

theorem FP.frame {g h : GRes} (hf : FP g h) (b : GRes) : FP (g + b) (h + b) := by
  intro f hv
  have hh := hf (f + b) (by simpa only [GRes.add_assoc, GRes.add_comm, GRes.add_left_comm] using hv)
  simpa only [GRes.add_assoc, GRes.add_comm, GRes.add_left_comm] using hh

/-- Registry agreement couples κ's lender fragment to the returned borrower fragment. -/
theorem match_return {m : Registry} {γ : Loc} {d d' : Ret}
    (hv : (reg m + claim γ d + permit γ d').Valid) : d = d' := by
  have ht := hv.tokF_agree m γ d (by simp [reg, claim, permit]) (by simp [reg, claim, permit])
  have hw := hv.wrF_agree m γ d' (by simp [reg, claim, permit]) (by simp [reg, claim, permit])
  exact Option.some.inj (ht.symm.trans hw)

/-- A pending lender fragment cannot coexist with the authoritative retired entry,
including when the fragment was hidden in garbage. -/
theorem no_pending_after_close (m : Registry) (γ : Loc) (d : Ret) (hd : d ≠ []) :
    ¬ (reg (put m γ []) + claim γ d).Valid := by
  intro hv
  have ht := hv.tokF_agree (put m γ []) γ d
    (by simp [reg, claim]) (by simp [reg, claim])
  have he : ([] : Ret) = d := Option.some.inj (by simpa [put] using ht)
  exact hd he.symm

theorem future_family {m : Registry} {γ : Loc} {d : Ret}
    (hv : (reg m + claim γ d).Valid) : m γ = some d :=
  hv.tokF_agree m γ d (by simp [reg, claim]) (by simp [reg, claim])

/-- Without the borrower permission an adversarial frame prevents authoritative close. -/
theorem close_without_return_impossible (m : Registry) (γ : Loc) (d : Ret)
    (hm : m γ = some d) (hd : d ≠ []) :
    ¬ FP (reg m + claim γ d) (reg (put m γ [])) := by
  intro hf
  have hv := hf (permit γ d) (by
    simpa only [GRes.add_assoc, GRes.add_comm, GRes.add_left_comm] using registered_valid m γ d hm)
  have hw := hv.wrF_agree (put m γ []) γ d
    (by simp [reg, permit]) (by simp [reg, permit])
  have he : ([] : Ret) = d := Option.some.inj (by simpa [put] using hw)
  exact hd he.symm

/-- A fresh registry slot can be added while any existing κ fragments remain in the frame. -/
theorem extend (m : Registry) (γ : Loc) (d : Ret) (hfresh : m γ = none) :
    FP (reg m) (reg (put m γ d)) := by
  intro f hv
  have hh := allocate m γ d hfresh f hv
  exact GRes.Valid.left (show ((f + reg (put m γ d)) + (claim γ d + permit γ d)).Valid by
    simpa only [GRes.add_assoc] using hh)

#print axioms future_family
#print axioms close_without_return_impossible
#print axioms extend
#print axioms allocate
#print axioms close
#print axioms registered_valid
#print axioms match_return
#print axioms no_pending_after_close
end BoCa.Fig16.LogRel.Core.Chain.SI.OwnedLoan
