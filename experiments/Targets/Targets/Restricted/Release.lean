import Targets.Statements.Soundness

/-!
# Targets — exactly-once release on complete no-reuse runs (DESIGN D9)

On a run that starts from the empty memory and ends with the memory empty, follow one location
`ℓ`: it is vacant at both ends.  An allocation of `ℓ` is a step from vacant to occupied, a release
a step from occupied to vacant.  So every allocation is followed by a release (`fall_between`)
and every release is preceded by an allocation (`rise_between`); and two releases of `ℓ` have an
allocation of `ℓ` between them, which `NoReuse` forbids.  This is `releasedOnce_of_ends`.

* `releasedOnceOfSound : ReleasedOnceOfSound`: the machine lemma of D9.  PROVED; its `SafeRuns`
  and `Terminates` premises are not used.
* `releasedOnceAll : ∀ J, ReleasedOnceAll J`.  PROVED (generic): the conjunct's run premises carry
  `Final` at the run's end and the empty memory at its start, which is all the argument reads, so
  it holds of every typing system.  Its typing content is T1's: `Terminates` (every run continues
  to a final configuration) and `SafeRuns`.  `[prog]`
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap)

section Occupancy
variable {P : Platform} (cs : List (Conf P)) (ℓ : Loc)

/-- `ℓ` is occupied at the run's `k`-th configuration. -/
def Occ (k : Nat) : Prop := ∃ c, cs[k]? = some c ∧ (c.μ ℓ).isSome

/-- `ℓ` is vacant at the run's `k`-th configuration. -/
def Vac (k : Nat) : Prop := ∃ c, cs[k]? = some c ∧ c.μ ℓ = none

variable {cs ℓ}

theorem not_occ_vac {k : Nat} (h₁ : Occ cs ℓ k) (h₂ : Vac cs ℓ k) : False := by
  obtain ⟨c, hc, hs⟩ := h₁
  obtain ⟨c', hc', hn⟩ := h₂
  rw [hc] at hc'; cases hc'; simp [hn] at hs

theorem getElem?_pred {k : Nat} {c : Conf P} (h : cs[k + 1]? = some c) :
    ∃ c', cs[k]? = some c' := by
  have hk : k + 1 < cs.length := (List.getElem?_eq_some_iff.mp h).1
  exact ⟨cs[k], List.getElem?_eq_getElem (by omega)⟩

/-- Between a vacancy and a later occupancy, an allocation. -/
theorem rise_between {a : Nat} : ∀ {b : Nat}, Vac cs ℓ a → Occ cs ℓ b → a ≤ b →
    ∃ k, a ≤ k ∧ k < b ∧ Allocated cs k ℓ
  | 0, ha, hb, hab => by
      obtain rfl : a = 0 := by omega
      exact (not_occ_vac hb ha).elim
  | b + 1, ha, hb, hab => by
      by_cases he : a = b + 1
      · subst he; exact (not_occ_vac hb ha).elim
      obtain ⟨c', hc', hs⟩ := hb
      obtain ⟨c, hc⟩ := getElem?_pred hc'
      cases hcb : c.μ ℓ with
      | none => exact ⟨b, by omega, by omega, c, c', hc, hc', hcb, hs⟩
      | some v =>
          obtain ⟨k, h₁, h₂, h₃⟩ := rise_between ha ⟨c, hc, by simp [hcb]⟩ (by omega)
          exact ⟨k, h₁, by omega, h₃⟩

/-- Between an occupancy and a later vacancy, a release. -/
theorem fall_between {a : Nat} : ∀ {b : Nat}, Occ cs ℓ a → Vac cs ℓ b → a ≤ b →
    ∃ j, a ≤ j ∧ j < b ∧ Released cs j ℓ
  | 0, ha, hb, hab => by
      obtain rfl : a = 0 := by omega
      exact (not_occ_vac ha hb).elim
  | b + 1, ha, hb, hab => by
      by_cases he : a = b + 1
      · subst he; exact (not_occ_vac ha hb).elim
      obtain ⟨c', hc', hn⟩ := hb
      obtain ⟨c, hc⟩ := getElem?_pred hc'
      cases hcb : c.μ ℓ with
      | none =>
          obtain ⟨j, h₁, h₂, h₃⟩ := fall_between ha ⟨c, hc, hcb⟩ (by omega)
          exact ⟨j, h₁, by omega, h₃⟩
      | some v => exact ⟨b, by omega, by omega, c, c', hc, hc', by simp [hcb], hn⟩

end Occupancy

/-- **Exactly-once release** on a run vacant everywhere at both ends that reuses no location. -/
theorem releasedOnce_of_ends {P : Platform} {cs : List (Conf P)}
    (h₀ : ∀ c, cs[0]? = some c → ∀ ℓ, c.μ ℓ = none)
    (hN : ∀ c, cs.getLast? = some c → ∀ ℓ, c.μ ℓ = none) (hR : NoReuse cs) :
    ReleasedOnce cs := by
  refine ⟨fun ℓ k hk => ?_, fun ℓ j hj => ?_⟩
  · obtain ⟨c, c', hc, hc', -, hs⟩ := hk
    have hlen : k + 1 < cs.length := (List.getElem?_eq_some_iff.mp hc').1
    have hlast : cs[cs.length - 1]? = cs.getLast? := by
      rw [List.getLast?_eq_getElem?]
    obtain ⟨d, hd⟩ : ∃ d, cs.getLast? = some d := by
      cases h : cs.getLast? with
      | none => simp at h; subst h; simp at hlen
      | some d => exact ⟨d, rfl⟩
    obtain ⟨j, -, -, hj⟩ := fall_between (cs := cs) (ℓ := ℓ) (a := k + 1) (b := cs.length - 1)
      ⟨c', hc', hs⟩ ⟨d, by rw [hlast, hd], hN d hd ℓ⟩ (by omega)
    refine ⟨j, hj, fun j' hj' => ?_⟩
    by_contra hne
    have key : ∀ {j₁ j₂ : Nat}, j₁ < j₂ → Released cs j₁ ℓ → Released cs j₂ ℓ → False := by
      intro j₁ j₂ hlt h₁ h₂
      obtain ⟨-, e₁, -, he₁, -, hn₁⟩ := id h₁
      obtain ⟨e₂, -, he₂, -, hs₂, -⟩ := id h₂
      obtain ⟨k', hk₁, hk₂, hk⟩ := rise_between (cs := cs) (ℓ := ℓ) ⟨e₁, he₁, hn₁⟩ ⟨e₂, he₂, hs₂⟩
        (by omega)
      exact hR j₁ k' ℓ (by omega) h₁ hk
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact key h hj' hj
    · exact key h hj hj'
  · obtain ⟨c, -, hc, -, hs, -⟩ := hj
    obtain ⟨c₀, hc₀⟩ : ∃ c₀, cs[0]? = some c₀ := by
      have : j < cs.length := (List.getElem?_eq_some_iff.mp hc).1
      exact ⟨cs[0], List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨k, -, hk, hA⟩ := rise_between (cs := cs) (ℓ := ℓ) (a := 0) ⟨c₀, hc₀, h₀ c₀ hc₀ ℓ⟩
      ⟨c, hc, hs⟩ (Nat.zero_le _)
    exact ⟨k, hk, hA⟩

theorem init_vacant {P : Platform} (e : Expr) (cs : List (Conf P)) :
    ∀ c, (init P e :: cs)[0]? = some c → ∀ ℓ, c.μ ℓ = none := by
  intro c hc ℓ
  simp only [List.getElem?_cons_zero, Option.some.injEq] at hc
  subst hc; rfl

theorem final_vacant {P : Platform} {A : VTy} {cs : List (Conf P)}
    (hF : ∀ c, cs.getLast? = some c → Final P A c) :
    ∀ c, cs.getLast? = some c → ∀ ℓ, c.μ ℓ = none := by
  intro c hc ℓ
  obtain ⟨-, -, -, hμ⟩ := hF c hc
  rw [hμ]; rfl

/-- **`ReleasedOnceOfSound`** (D9's machine lemma). -/
theorem releasedOnceOfSound : ReleasedOnceOfSound (ℍ := ℍ) := by
  intro P A e _ _ cs _ hR hF
  exact releasedOnce_of_ends (init_vacant e cs) (final_vacant hF) hR

/-- **`ReleasedOnceAll J`**, at every typing system. -/
theorem releasedOnceAll (J : TypingJ) : ReleasedOnceAll (ℍ := ℍ) J := by
  intro P _ Γ γ S A e _ _ _ _ cs _ hR hF
  exact releasedOnce_of_ends (init_vacant _ cs) (final_vacant hF) hR

end Targets

end
