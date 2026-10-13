import Core.Stdio
import Core.EffPrograms
import Targets.Base.Machine

/-!
# Base — first-order data in Core's relation (RESTRUCTURE §4.5)

`vC_data`: at a closed data
type, Core's relation is exactly data at the empty resource (forward by `vC_ind`, backward by
induction on `DataVal` with `vC_roll`).  `[Core σ=[]]`
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

theorem dataB_rename : ∀ {k : Nat} {A : VTy}, VTy.DataB k A → ∀ {k' : Nat} (r : Nat → Nat),
    (∀ n, n < k → r n < k') → VTy.DataB k' (A.rename r) := by
  intro k A h
  induction h with
  | unit k => intro _ _ _; exact .unit _
  | zero k => intro _ _ _; exact .zero _
  | int k w => intro _ _ _; exact .int _ _
  | tvar hn => intro _ r hr; exact .tvar (hr _ hn)
  | tensor _ _ ihA ihB => intro _ r hr; exact .tensor (ihA r hr) (ihB r hr)
  | sum _ _ ihA ihB => intro _ r hr; exact .sum (ihA r hr) (ihB r hr)
  | mu _ ih =>
      intro k' r hr
      refine .mu (ih (VTy.upR r) fun n hn => ?_)
      cases n with
      | zero => show 0 < k' + 1; omega
      | succ n => show r n + 1 < k' + 1; have := hr n (by omega); omega

theorem dataB_subst : ∀ {k : Nat} {A : VTy}, VTy.DataB k A → ∀ {j : Nat} (σ : Nat → VTy),
    (∀ n, n < k → VTy.DataB j (σ n)) → VTy.DataB j (A.subst σ) := by
  intro k A h
  induction h with
  | unit k => intro _ _ _; exact .unit _
  | zero k => intro _ _ _; exact .zero _
  | int k w => intro _ _ _; exact .int _ _
  | tvar hn => intro _ σ hσ; exact hσ _ hn
  | tensor _ _ ihA ihB => intro _ σ hσ; exact .tensor (ihA σ hσ) (ihB σ hσ)
  | sum _ _ ihA ihB => intro _ σ hσ; exact .sum (ihA σ hσ) (ihB σ hσ)
  | mu _ ih =>
      intro j σ hσ
      refine .mu (ih (VTy.upS σ) fun n hn => ?_)
      cases n with
      | zero => exact .tvar (by omega)
      | succ n =>
          exact dataB_rename (hσ n (by omega)) Nat.succ (fun m hm => by omega)

/-- The unrolling of a closed data `μ` is data. -/
theorem data_inst {A : VTy} (h : (VTy.mu A).Data) : (VTy.inst (.mu A) A).Data := by
  cases h with
  | mu hA =>
      refine dataB_subst hA _ fun n hn => ?_
      cases n with
      | zero => exact .mu hA
      | succ n => omega

theorem dataB_cl : ∀ {k : Nat} {A : VTy}, VTy.DataB k A → A.Cl k := by
  intro k A h
  induction h with
  | unit | zero | int => trivial
  | tvar hn => exact hn
  | tensor _ _ ihA ihB => exact ⟨ihA, ihB⟩
  | sum _ _ ihA ihB => exact ⟨ihA, ihB⟩
  | mu _ ih => exact ih

theorem dataB_noMut : ∀ {k : Nat} {A : VTy}, VTy.DataB k A → ∀ n, A.NoMut n := by
  intro k A h
  induction h with
  | unit | zero | int => intro _; trivial
  | tvar _ => intro _; trivial
  | tensor _ _ ihA ihB => intro n; exact ⟨ihA n, ihB n⟩
  | sum _ _ ihA ihB => intro n; exact ⟨ihA n, ihB n⟩
  | mu _ ih => intro n; exact ih (n + 1)

/-- A value of a closed data type is data, and holds nothing. -/
theorem vC_data_mp {δ : LSub} : ∀ (b : Bool) (A : VTy) (ls : List SRec) (v : Val) (ρ : WRes),
    vCE (ℍ := ℍ) none b A ls δ v ρ → A.Data → ρ = PMap.empty ∧ DataVal A v := by
  refine vC_ind δ (fun _ A _ v ρ => A.Data → ρ = PMap.empty ∧ DataVal A v) ?_
  intro b T ls v ρ hF hT
  cases T with
  | unit =>
      obtain ⟨rfl, rfl⟩ := hF
      exact ⟨rfl, .unit⟩
  | int w =>
      obtain ⟨rfl, hv⟩ := hF
      exact ⟨rfl, .int hv⟩
  | tensor A B =>
      cases hT with
      | tensor hA hB =>
          obtain ⟨v₁, v₂, ρ₀, ρ₃, hc, ⟨rfl, rfl⟩, ρ₁, ρ₂, hc', ⟨-, h₁⟩, ⟨-, h₂⟩⟩ := hF
          obtain ⟨rfl, hd₁⟩ := h₁ hA
          obtain ⟨rfl, hd₂⟩ := h₂ hB
          rw [← eq_of_compS_empty_left hc', ← eq_of_compS_empty_left hc]
          exact ⟨rfl, .pair hd₁ hd₂⟩
  | sum A B =>
      cases hT with
      | sum hA hB =>
          rcases hF with ⟨v₁, ρ₀, ρ₁, hc, ⟨rfl, rfl⟩, ⟨-, h₁⟩⟩ | ⟨v₂, ρ₀, ρ₂, hc, ⟨rfl, rfl⟩, ⟨-, h₂⟩⟩
          · obtain ⟨rfl, hd⟩ := h₁ hA
            rw [← eq_of_compS_empty_left hc]
            exact ⟨rfl, .inj₁ hd⟩
          · obtain ⟨rfl, hd⟩ := h₂ hB
            rw [← eq_of_compS_empty_left hc]
            exact ⟨rfl, .inj₂ hd⟩
  | zero => exact hF.elim
  | tvar n => exact hF.elim
  | mu A =>
      obtain ⟨-, -, -, h⟩ := hF
      obtain ⟨rfl, hd⟩ := h (data_inst hT)
      exact ⟨rfl, .roll hd⟩
  | thunk _ | ref _ | imm _ _ | «mut» _ _ | box _ _ | bang _ | unk | opq _ | fam _ =>
      cases hT

/-- Data values are in the relation at the empty resource. -/
theorem vC_of_dataVal {δ : LSub} {ls : List SRec} :
    ∀ {A : VTy} {v : Val}, DataVal A v → A.Data → ∀ b, vCE (ℍ := ℍ) none b A ls δ v PMap.empty := by
  intro A v h
  induction h with
  | unit => intro _ _; exact ⟨rfl, rfl⟩
  | int hv => intro _ _; exact ⟨rfl, hv⟩
  | pair _ _ ih₁ ih₂ =>
      intro hT b
      cases hT with
      | tensor hA hB =>
          exact ⟨_, _, PMap.empty, PMap.empty, ResU.comp_empty_right _, ⟨rfl, rfl⟩,
            PMap.empty, PMap.empty, ResU.comp_empty_right _, ih₁ hA b, ih₂ hB b⟩
  | inj₁ _ ih =>
      intro hT b
      cases hT with
      | sum hA _ => exact Or.inl ⟨_, PMap.empty, PMap.empty, ResU.comp_empty_right _, ⟨rfl, rfl⟩, ih hA b⟩
  | inj₂ _ ih =>
      intro hT b
      cases hT with
      | sum _ hB => exact Or.inr ⟨_, PMap.empty, PMap.empty, ResU.comp_empty_right _, ⟨rfl, rfl⟩, ih hB b⟩
  | roll _ ih =>
      intro hT b
      cases hT with
      | mu hA => exact vC_roll (dataB_noMut hA 0) (dataB_cl (.mu hA)) (ih (data_inst (.mu hA)) b)

/-- **`vC_data`**: at a closed data type, the relation is exactly data at the empty resource. -/
theorem vC_data {A : VTy} (hA : A.Data) {b : Bool} {ls : List SRec} {δ : LSub} {v : Val}
    {ρ : WRes} : vCE (ℍ := ℍ) none b A ls δ v ρ ↔ ρ = PMap.empty ∧ DataVal A v :=
  ⟨fun h => vC_data_mp b A ls v ρ h hA, fun ⟨hρ, hv⟩ => hρ ▸ vC_of_dataVal hv hA b⟩


end Targets

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.EffPrograms
open BoCa.Fig16.LogRel.Core.EffExamples

theorem flag_data : VTy.Data Flag := .sum (.unit 0) (.unit 0)

theorem err_data : VTy.Data (.sum .zero .unit) := .sum (.zero 0) (.unit 0)

end Targets

end
