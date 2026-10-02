import Paper.S5_Model.Definitions
import Paper.S6_5_NonStandardEntailments.Lemmas
import Support.LogicalRelation.Facts
import Support.Model.Notation
import FnMut.Core.World
import FnMut.Core.FrameRecords

/-!
# Core — the shape relation at `μ`  `[spec §6]`

`vShapeE` reads a type variable at its environment entry and `μX. A` at the least fixed point
`⋂{P | A[P/X] ⊆ P}`.  This file proves what the typed world needs of it:

* the environment of a closed type is the empty one read explicitly (`vShapeE_some`);
* renaming and substitution move into the environment (`vShapeE_rename`, `vShapeE_subst`);
* the relation is monotone in the environment's candidates (`vShapeE_mono`);
* **the unroll equation** `vShape (μX. A) ↔ vShape (A[μX. A/X])` at a closed `μ`
  (`vShape_mu_iff`, with `vShape_unfold`/`vShape_roll`);
* **the induction principle** of the least fixed point read at every type (`vShape_ind`): a
  property closed under one unfolding of every clause (`sF`) holds of `vShape`;
* `δ`-congruence (`vShapeE_congr`) and `TyEq`-invariance (`vShapeE_tyEq`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### The environment -/

theorem sEnvP_eq (η : Option (Nat → SEnt)) (n : Nat) (v : Val) : sEnvP η n v = (sEnv η n).P v := by
  cases η <;> rfl

theorem sClose_eq (η : Option (Nat → SEnt)) (A : VTy) :
    sClose η A = A.subst (fun n => (sEnv η n).ty) := by
  cases η with
  | none => exact (VTy.subst_id A).symm
  | some η => rfl

/-- The relation reads its environment only through `sEnv`. -/
theorem vShapeE_some (η : Option (Nat → SEnt)) :
    ∀ A : VTy, vShapeE η A = vShapeE (some (sEnv η)) A := by
  intro A
  induction A using VTy.recV with
  | unit => rfl
  | int w => rfl
  | opq k => rfl
  | tensor A B ihA ihB => funext δ v; simp only [vShapeE, ihA, ihB]
  | zero => rfl
  | sum A B ihA ihB => funext δ v; simp only [vShapeE, ihA, ihB]
  | thunk _ => rfl
  | ref A ih => funext δ v; simp only [vShapeE, ih]
  | fam L ih => funext δ v; simp only [vShapeE, ih]
  | imm a A ih => funext δ v; simp only [vShapeE, ih]
  | «mut» a A ih => funext δ v; simp only [vShapeE, ih]
  | box a A ih => funext δ v; simp only [vShapeE, ih]
  | bang A _ => rfl
  | unk => rfl
  | tvar n => funext δ v; simp only [vShapeE, sEnvP_eq]; rfl
  | mu A _ =>
      funext δ v
      have e : sClose η (.mu A) = sClose (some (sEnv η)) (.mu A) := by rw [sClose_eq]; rfl
      simp only [vShapeE, e]
      rfl

/-- The environment of a closed type. -/
abbrev sNil : Nat → SEnt := sEnv none

theorem vShape_eq_some : vShape = vShapeE (some sNil) := funext (vShapeE_some none)

/-! ### Renaming and substitution -/

theorem SEnt.ext' {a b : SEnt} (h₁ : a.ty = b.ty) (h₂ : a.P = b.P) : a = b := by
  cases a; cases b; simp only at h₁ h₂; subst h₁; subst h₂; rfl

theorem scons_comp_upR {α : Type} (x : α) (ρ : Nat → α) (r : Nat → Nat) :
    VTy.scons x ρ ∘ VTy.upR r = VTy.scons x (ρ ∘ r) := by
  funext n; cases n <;> rfl

theorem vShapeE_rename : ∀ (A : VTy) (ρ : Nat → SEnt) (r : Nat → Nat),
    vShapeE (some ρ) (A.rename r) = vShapeE (some (ρ ∘ r)) A := by
  intro A
  induction A using VTy.recV with
  | unit => intro ρ r; rfl
  | int w => intro ρ r; rfl
  | opq k => intro ρ r; rfl
  | tensor A B ihA ihB => intro ρ r; funext δ v; simp only [VTy.rename, vShapeE, ihA, ihB]
  | zero => intro ρ r; rfl
  | sum A B ihA ihB => intro ρ r; funext δ v; simp only [VTy.rename, vShapeE, ihA, ihB]
  | thunk _ => intro ρ r; rfl
  | ref A ih => intro ρ r; funext δ v; simp only [VTy.rename, vShapeE, ih]
  | fam L ih => intro ρ r; funext δ v; simp only [VTy.rename, vShapeE, ih]
  | imm a A ih => intro ρ r; funext δ v; simp only [VTy.rename, vShapeE, ih]
  | «mut» a A ih => intro ρ r; funext δ v; simp only [VTy.rename, vShapeE, ih]
  | box a A ih => intro ρ r; funext δ v; simp only [VTy.rename, vShapeE, ih]
  | bang A _ => intro ρ r; rfl
  | unk => intro ρ r; rfl
  | tvar n => intro ρ r; rfl
  | mu A ih =>
      intro ρ r
      funext δ v
      have e : sClose (some ρ) ((VTy.mu A).rename r) = sClose (some (ρ ∘ r)) (.mu A) := by
        simp only [sClose, VTy.subst_rename]; rfl
      have e' : sClose (some ρ) (.mu (A.rename (VTy.upR r))) = sClose (some (ρ ∘ r)) (.mu A) := e
      simp only [VTy.rename, vShapeE, e', sEnv, ih, scons_comp_upR]

theorem vShapeE_subst : ∀ (A : VTy) (ρ : Nat → SEnt) (σ : Nat → VTy) (δ : LSub),
    vShapeE (some ρ) (A.subst σ) δ
      = vShapeE (some (fun n => ⟨(σ n).subst (fun k => (ρ k).ty), vShapeE (some ρ) (σ n) δ⟩)) A δ := by
  intro A
  induction A using VTy.recV with
  | unit => intro ρ σ δ; rfl
  | int w => intro ρ σ δ; rfl
  | opq k => intro ρ σ δ; rfl
  | tensor A B ihA ihB => intro ρ σ δ; funext v; simp only [VTy.subst, vShapeE, ihA, ihB]
  | zero => intro ρ σ δ; rfl
  | sum A B ihA ihB => intro ρ σ δ; funext v; simp only [VTy.subst, vShapeE, ihA, ihB]
  | thunk _ => intro ρ σ δ; rfl
  | ref A ih => intro ρ σ δ; funext v; simp only [VTy.subst, vShapeE, ih]
  | fam L ih => intro ρ σ δ; funext v; simp only [VTy.subst, vShapeE, ih]
  | imm a A ih => intro ρ σ δ; funext v; simp only [VTy.subst, vShapeE, ih]
  | «mut» a A ih => intro ρ σ δ; funext v; simp only [VTy.subst, vShapeE, ih]
  | box a A ih => intro ρ σ δ; funext v; simp only [VTy.subst, vShapeE, ih]
  | bang A _ => intro ρ σ δ; rfl
  | unk => intro ρ σ δ; rfl
  | tvar n => intro ρ σ δ; rfl
  | mu A ih =>
      intro ρ σ δ
      funext v
      have eM : sClose (some ρ) (.mu (A.subst (VTy.upS σ)))
          = sClose (some (fun n => (⟨(σ n).subst (fun k => (ρ k).ty),
              vShapeE (some ρ) (σ n) δ⟩ : SEnt))) (.mu A) := by
        simp only [sClose]
        rw [show VTy.mu (A.subst (VTy.upS σ)) = (VTy.mu A).subst σ from rfl, VTy.subst_subst]
      simp only [VTy.subst, vShapeE, eM, sEnv]
      congr 1
      funext ρ₀
      congr 1
      apply propext
      refine forall_congr' fun P => ?_
      refine imp_congr ?_ Iff.rfl
      rw [ih]
      have eenv : (fun n => (⟨(VTy.upS σ n).subst (fun k => (VTy.scons
            (⟨sClose (some (fun n => (⟨(σ n).subst (fun k => (ρ k).ty),
              vShapeE (some ρ) (σ n) δ⟩ : SEnt))) (.mu A), P⟩ : SEnt) ρ k).ty),
            vShapeE (some (VTy.scons (⟨sClose (some (fun n => (⟨(σ n).subst (fun k => (ρ k).ty),
              vShapeE (some ρ) (σ n) δ⟩ : SEnt))) (.mu A), P⟩ : SEnt) ρ)) (VTy.upS σ n) δ⟩ : SEnt))
          = VTy.scons (⟨sClose (some (fun n => (⟨(σ n).subst (fun k => (ρ k).ty),
              vShapeE (some ρ) (σ n) δ⟩ : SEnt))) (.mu A), P⟩ : SEnt)
              (fun n => ⟨(σ n).subst (fun k => (ρ k).ty), vShapeE (some ρ) (σ n) δ⟩) := by
        funext n
        cases n with
        | zero => rfl
        | succ n =>
            refine SEnt.ext' ?_ ?_
            · show (VTy.rename Nat.succ (σ n)).subst _ = _
              rw [VTy.subst_rename]; rfl
            · show vShapeE _ (VTy.rename Nat.succ (σ n)) δ = _
              rw [vShapeE_rename]; rfl
      rw [eenv]

/-! ### Monotonicity -/

/-- `vShapeE` is monotone in its environment's candidates. -/
theorem vShapeE_mono : ∀ (A : VTy) (η₁ η₂ : Nat → SEnt), (∀ n, (η₁ n).ty = (η₂ n).ty) →
    (∀ n v ρ, (η₁ n).P v ρ → (η₂ n).P v ρ) →
    ∀ δ v ρ, vShapeE (some η₁) A δ v ρ → vShapeE (some η₂) A δ v ρ := by
  intro A
  induction A using VTy.recV with
  | unit => intro _ _ _ _ _ _ _ h; exact h
  | int w => intro _ _ _ _ _ _ _ h; exact h
  | opq k => intro _ _ _ _ _ _ _ h; exact h
  | tensor A B ihA ihB =>
      intro η₁ η₂ ht hP δ v ρ h
      obtain ⟨v₁, v₂, ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', h₁, h₂⟩ := h
      exact ⟨v₁, v₂, ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', ihA η₁ η₂ ht hP δ v₁ ρ₁ h₁,
        ihB η₁ η₂ ht hP δ v₂ ρ₂ h₂⟩
  | zero => intro _ _ _ _ _ _ _ h; exact h
  | sum A B ihA ihB =>
      intro η₁ η₂ ht hP δ v ρ h
      rcases h with ⟨v₁, ρ₀, ρ₁, hc, hp, h₁⟩ | ⟨v₂, ρ₀, ρ₂, hc, hp, h₂⟩
      · exact Or.inl ⟨v₁, ρ₀, ρ₁, hc, hp, ihA η₁ η₂ ht hP δ v₁ ρ₁ h₁⟩
      · exact Or.inr ⟨v₂, ρ₀, ρ₂, hc, hp, ihB η₁ η₂ ht hP δ v₂ ρ₂ h₂⟩
  | thunk _ => intro _ _ _ _ _ _ _ h; exact h
  | ref A ih =>
      intro η₁ η₂ ht hP δ v ρ h
      obtain ⟨ℓ, v', ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', ho, h₂⟩ := h
      exact ⟨ℓ, v', ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', ho, ih η₁ η₂ ht hP δ v' ρ₂ h₂⟩
  | fam L ih =>
      intro η₁ η₂ ht hP δ v ρ h
      obtain ⟨ℓ, c, ρ₀, ρ₁, hc, hp, hs⟩ := h
      exact ⟨ℓ, c, ρ₀, ρ₁, hc, hp, sepRange_mono' (fun m σ hm => ih η₁ η₂ ht hP δ _ σ hm) hs⟩
  | imm a A ih =>
      intro η₁ η₂ ht hP δ v ρ h
      obtain ⟨α, hα, ℓ, ρ₀, ρ₁, hc, hp, hpto⟩ := h
      exact ⟨α, hα, ℓ, ρ₀, ρ₁, hc, hp,
        ptoImm_mono (fun u σ hu => ih η₁ η₂ ht hP δ u σ hu) ρ₁ hpto⟩
  | «mut» a A ih =>
      intro η₁ η₂ ht hP δ v ρ h
      obtain ⟨α, hα, ℓ, ρ₀, ρ₁, hc, hp, Q, hQ, hsub⟩ := h
      exact ⟨α, hα, ℓ, ρ₀, ρ₁, hc, hp, Q, hQ, fun u σ hu => ih η₁ η₂ ht hP δ u σ (hsub u σ hu)⟩
  | box a A ih =>
      intro η₁ η₂ ht hP δ v ρ h
      obtain ⟨α, hα, hb, ho⟩ := h
      exact ⟨α, hα, ih η₁ η₂ ht hP δ v ρ hb, ho⟩
  | bang A _ => intro _ _ _ _ _ _ _ h; exact h
  | unk => intro _ _ _ _ _ _ _ h; exact h
  | tvar n => intro η₁ η₂ _ hP δ v ρ h; exact hP n v ρ h
  | mu A ih =>
      intro η₁ η₂ ht hP δ v ρ h
      have eM : sClose (some η₁) (.mu A) = sClose (some η₂) (.mu A) := by
        simp only [sClose]; congr 1; funext n; exact ht n
      obtain ⟨hcl, hlfp⟩ := h
      refine ⟨eM ▸ hcl, fun P hPre => hlfp P (fun v' ρ' h' => hPre v' ρ' ?_)⟩
      refine ih _ _ (fun n => ?_) (fun n => ?_) δ v' ρ' h'
      · cases n with
        | zero => exact eM
        | succ n => exact ht n
      · cases n with
        | zero => exact fun _ _ h => h
        | succ n => exact hP n

/-! ### The unroll equation -/

/-- One unfolding of `μX. A` at the candidate `P`. -/
def sBody (A : VTy) (δ : LSub) (P : Val → WProp) : Val → WProp :=
  vShapeE (some (VTy.scons ⟨.mu A, P⟩ sNil)) A δ

theorem vShape_mu_eq (A : VTy) (δ : LSub) (v : Val) (ρ : WRes) :
    vShape (.mu A) δ v ρ ↔ (VTy.mu A).Cl 0 ∧
      ∀ P : Val → WProp, (∀ v' ρ', sBody A δ P v' ρ' → P v' ρ') → P v ρ := Iff.rfl

/-- `A[μX. A/X]` is the body at `vShape (μX. A)`. -/
theorem vShape_inst (A : VTy) (δ : LSub) :
    vShape (VTy.inst (.mu A) A) δ = sBody A δ (vShape (.mu A) δ) := by
  rw [vShape_eq_some, VTy.inst, vShapeE_subst, sBody]
  congr 2
  funext n
  cases n with
  | zero =>
      refine SEnt.ext' ?_ ?_
      · exact VTy.subst_id _
      · rfl
  | succ n => rfl

theorem sBody_mono (A : VTy) (δ : LSub) {P Q : Val → WProp} (h : ∀ v ρ, P v ρ → Q v ρ) :
    ∀ v ρ, sBody A δ P v ρ → sBody A δ Q v ρ :=
  vShapeE_mono A _ _ (fun n => by cases n <;> rfl)
    (fun n => by cases n with
      | zero => exact h
      | succ n => exact fun _ _ h => h) δ

/-- `roll` at the shape relation. -/
theorem vShape_roll {A : VTy} {δ : LSub} {v : Val} {ρ : WRes} (hc : (VTy.mu A).Cl 0)
    (h : vShape (VTy.inst (.mu A) A) δ v ρ) : vShape (.mu A) δ v ρ := by
  rw [vShape_inst] at h
  exact ⟨hc, fun P hP => hP v ρ (sBody_mono A δ (fun v' ρ' h' => h'.2 P hP) v ρ h)⟩

/-- `unroll` at the shape relation. -/
theorem vShape_unfold {A : VTy} {δ : LSub} {v : Val} {ρ : WRes} (h : vShape (.mu A) δ v ρ) :
    (VTy.mu A).Cl 0 ∧ vShape (VTy.inst (.mu A) A) δ v ρ := by
  refine ⟨h.1, ?_⟩
  rw [vShape_inst]
  exact h.2 (sBody A δ (vShape (.mu A) δ)) (fun v' ρ' h' =>
    sBody_mono A δ (fun v'' ρ'' h'' => vShape_roll h.1 (by rw [vShape_inst]; exact h''))
      v' ρ' h')

/-- **The unroll equation.** -/
theorem vShape_mu_iff {A : VTy} {δ : LSub} {v : Val} {ρ : WRes} :
    vShape (.mu A) δ v ρ ↔ (VTy.mu A).Cl 0 ∧ vShape (VTy.inst (.mu A) A) δ v ρ :=
  ⟨vShape_unfold, fun ⟨hc, h⟩ => vShape_roll hc h⟩

/-! ### The induction principle -/

/-- One unfolding of the shape relation at every type, with `S` at the positions the clauses
recurse to; at `μX. A` the unrolling `A[μX. A/X]`. -/
def sF (S : VTy → Val → WProp) (δ : LSub) : VTy → Val → WProp
  | .unit, v => ⌜v = .unit⌝
  | .tensor T₁ T₂, v => ex fun v₁ => ex fun v₂ => ⌜v = .pair v₁ v₂⌝ ⋆ S T₁ v₁ ⋆ S T₂ v₂
  | .sum T₁ T₂, v =>
      BoLo.or (ex fun v₁ => ⌜v = .inj₁ v₁⌝ ⋆ S T₁ v₁) (ex fun v₂ => ⌜v = .inj₂ v₂⌝ ⋆ S T₂ v₂)
  | .zero, _ => fun _ => False
  | .thunk _, _ => fun _ => True
  | .box a T, v => atLife δ a fun α => box α (S T v)
  | .ref T, v => ex fun ℓ => ex fun v' => ⌜v = .loc ℓ⌝ ⋆ ptoOwn ℓ v' ⋆ S T v'
  | .fam L, v => ex fun ℓ => ex fun c => ⌜v = Val.arr ℓ c⌝ ⋆ sepRange (fun m => S L (.loc m)) ℓ c.toNat
  | .bang _, _ => emp
  | .imm a T, v => atLife δ a fun α => ex fun ℓ => ⌜v = .loc ℓ⌝ ⋆ ptoImm ℓ α (S T)
  | .mut a T, v => atLife δ a fun α => ex fun ℓ => ⌜v = .loc ℓ⌝ ⋆
      fun ρ => ∃ P, ptoMut ℓ α P ρ ∧ ∀ u σ, P u σ → S T u σ
  | .unk, _ => emp
  | .int w, v => ⌜v.IsInt w⌝
  | .opq k, v => ⌜k.Holds v⌝
  | .tvar _, _ => fun _ => False
  | .mu A, v => fun ρ => (VTy.mu A).Cl 0 ∧ S (VTy.inst (.mu A) A) v ρ

/-- `vShape` is its own unfolding. -/
theorem sF_vShape (δ : LSub) : ∀ (T : VTy) (v : Val) (ρ : WRes),
    vShape T δ v ρ ↔ sF (fun T => vShape T δ) δ T v ρ
  | .unit, _, _ => Iff.rfl
  | .tensor _ _, _, _ => Iff.rfl
  | .sum _ _, _, _ => Iff.rfl
  | .zero, _, _ => Iff.rfl
  | .thunk _, _, _ => Iff.rfl
  | .box _ _, _, _ => Iff.rfl
  | .ref _, _, _ => Iff.rfl
  | .fam _, _, _ => Iff.rfl
  | .bang _, _, _ => Iff.rfl
  | .imm _ _, _, _ => Iff.rfl
  | .mut _ _, _, _ => Iff.rfl
  | .unk, _, _ => Iff.rfl
  | .int _, _, _ => Iff.rfl
  | .opq _, _, _ => Iff.rfl
  | .tvar _, _, _ => Iff.rfl
  | .mu _, _, _ => vShape_mu_iff

theorem sF_mono {S₁ S₂ : VTy → Val → WProp} (h : ∀ T v ρ, S₁ T v ρ → S₂ T v ρ) (δ : LSub) :
    ∀ (T : VTy) (v : Val) (ρ : WRes), sF S₁ δ T v ρ → sF S₂ δ T v ρ
  | .unit, _, _, hs => hs
  | .tensor T₁ T₂, _, _, hs => by
      obtain ⟨v₁, v₂, ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', h₁, h₂⟩ := hs
      exact ⟨v₁, v₂, ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', h T₁ v₁ ρ₁ h₁, h T₂ v₂ ρ₂ h₂⟩
  | .sum T₁ T₂, _, _, hs => by
      rcases hs with ⟨v₁, ρ₀, ρ₁, hc, hp, h₁⟩ | ⟨v₂, ρ₀, ρ₂, hc, hp, h₂⟩
      · exact Or.inl ⟨v₁, ρ₀, ρ₁, hc, hp, h T₁ v₁ ρ₁ h₁⟩
      · exact Or.inr ⟨v₂, ρ₀, ρ₂, hc, hp, h T₂ v₂ ρ₂ h₂⟩
  | .zero, _, _, hs => hs
  | .thunk _, _, _, hs => hs
  | .box _ T, _, _, hs => by
      obtain ⟨α, hα, hb, ho⟩ := hs
      exact ⟨α, hα, h T _ _ hb, ho⟩
  | .ref T, _, _, hs => by
      obtain ⟨ℓ, v', ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', ho, h₂⟩ := hs
      exact ⟨ℓ, v', ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', ho, h T v' ρ₂ h₂⟩
  | .fam L, _, _, hs => by
      obtain ⟨ℓ, c, ρ₀, ρ₁, hc, hp, hs⟩ := hs
      exact ⟨ℓ, c, ρ₀, ρ₁, hc, hp, sepRange_mono' (fun m σ hm => h L _ σ hm) hs⟩
  | .bang _, _, _, hs => hs
  | .imm _ T, _, _, hs => by
      obtain ⟨α, hα, ℓ, ρ₀, ρ₁, hc, hp, hpto⟩ := hs
      exact ⟨α, hα, ℓ, ρ₀, ρ₁, hc, hp, ptoImm_mono (fun u σ hu => h T u σ hu) ρ₁ hpto⟩
  | .mut _ T, _, _, hs => by
      obtain ⟨α, hα, ℓ, ρ₀, ρ₁, hc, hp, Q, hQ, hsub⟩ := hs
      exact ⟨α, hα, ℓ, ρ₀, ρ₁, hc, hp, Q, hQ, fun u σ hu => h T u σ (hsub u σ hu)⟩
  | .unk, _, _, hs => hs
  | .int _, _, _, hs => hs
  | .opq _, _, _, hs => hs
  | .tvar _, _, _, hs => hs
  | .mu A, _, _, hs => ⟨hs.1, h _ _ _ hs.2⟩

/-- `B[M · σ] = (B[⇑σ])[M/X]`. -/
theorem VTy.subst_scons_eq_inst (B M : VTy) (σ : Nat → VTy) :
    B.subst (VTy.scons M σ) = VTy.inst M (B.subst (VTy.upS σ)) := by
  rw [VTy.inst, VTy.subst_subst]
  congr 1
  funext n
  cases n with
  | zero => rfl
  | succ n =>
      show σ n = (VTy.rename Nat.succ (σ n)).subst (VTy.scons M .tvar)
      rw [VTy.subst_rename]
      exact (VTy.subst_id (σ n)).symm

/-- **Induction on the least fixed points, at every type.**  A property of `vShape` closed
under one unfolding of every clause — `sF` with the relation and the property at the positions
it recurses to, the unrolling at `μ` — holds of `vShape`.  At a `μ` this is induction on the
least fixed point; at the other formers, on the type. -/
theorem vShape_ind (δ : LSub) (Φ : VTy → Val → WRes → Prop)
    (h : ∀ T v ρ, sF (fun T v ρ => vShape T δ v ρ ∧ Φ T v ρ) δ T v ρ → Φ T v ρ) :
    ∀ T v ρ, vShape T δ v ρ → Φ T v ρ := by
  let G : VTy → Val → WProp := fun T v ρ => vShape T δ v ρ ∧ Φ T v ρ
  have hG : ∀ T v ρ, sF G δ T v ρ → G T v ρ := fun T v ρ hs =>
    ⟨(sF_vShape δ T v ρ).mpr (sF_mono (fun _ _ _ h => h.1) δ T v ρ hs), h T v ρ hs⟩
  have gen : ∀ (A : VTy) (ρe : Nat → SEnt) (σ : Nat → VTy), (∀ n, (ρe n).ty = σ n) →
      (∀ n v r, (ρe n).P v r → G (σ n) v r) →
      ∀ v r, vShapeE (some ρe) A δ v r → G (A.subst σ) v r := by
    intro A
    induction A using VTy.recV with
    | unit => intro _ _ _ _ v r hr; exact hG _ v r hr
    | int w => intro _ _ _ _ v r hr; exact hG _ v r hr
    | opq k => intro _ _ _ _ v r hr; exact hG _ v r hr
    | tensor A B ihA ihB =>
        intro ρe σ ht hP v r hr
        obtain ⟨v₁, v₂, ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', h₁, h₂⟩ := hr
        exact hG _ v r ⟨v₁, v₂, ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', ihA ρe σ ht hP v₁ ρ₁ h₁,
          ihB ρe σ ht hP v₂ ρ₂ h₂⟩
    | zero => intro _ _ _ _ v r hr; exact hr.elim
    | sum A B ihA ihB =>
        intro ρe σ ht hP v r hr
        rcases hr with ⟨v₁, ρ₀, ρ₁, hc, hp, h₁⟩ | ⟨v₂, ρ₀, ρ₂, hc, hp, h₂⟩
        · exact hG _ v r (Or.inl ⟨v₁, ρ₀, ρ₁, hc, hp, ihA ρe σ ht hP v₁ ρ₁ h₁⟩)
        · exact hG _ v r (Or.inr ⟨v₂, ρ₀, ρ₂, hc, hp, ihB ρe σ ht hP v₂ ρ₂ h₂⟩)
    | thunk _ => intro _ _ _ _ v r hr; exact hG _ v r hr
    | ref A ih =>
        intro ρe σ ht hP v r hr
        obtain ⟨ℓ, v', ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', ho, h₂⟩ := hr
        exact hG _ v r ⟨ℓ, v', ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', ho, ih ρe σ ht hP v' ρ₂ h₂⟩
    | fam L ih =>
        intro ρe σ ht hP v r hr
        obtain ⟨ℓ, c, ρ₀, ρ₁, hc, hp, hs⟩ := hr
        exact hG _ v r ⟨ℓ, c, ρ₀, ρ₁, hc, hp,
          sepRange_mono' (fun m σ' hm => ih ρe σ ht hP _ σ' hm) hs⟩
    | imm a A ih =>
        intro ρe σ ht hP v r hr
        obtain ⟨α, hα, ℓ, ρ₀, ρ₁, hc, hp, hpto⟩ := hr
        exact hG _ v r ⟨α, hα, ℓ, ρ₀, ρ₁, hc, hp,
          ptoImm_mono (fun u σ' hu => ih ρe σ ht hP u σ' hu) ρ₁ hpto⟩
    | «mut» a A ih =>
        intro ρe σ ht hP v r hr
        obtain ⟨α, hα, ℓ, ρ₀, ρ₁, hc, hp, Q, hQ, hsub⟩ := hr
        exact hG _ v r ⟨α, hα, ℓ, ρ₀, ρ₁, hc, hp, Q, hQ,
          fun u σ' hu => ih ρe σ ht hP u σ' (hsub u σ' hu)⟩
    | box a A ih =>
        intro ρe σ ht hP v r hr
        obtain ⟨α, hα, hb, ho⟩ := hr
        exact hG _ v r ⟨α, hα, ih ρe σ ht hP v r hb, ho⟩
    | bang A _ => intro _ _ _ _ v r hr; exact hG _ v r hr
    | unk => intro _ _ _ _ v r hr; exact hG _ v r hr
    | tvar n => intro ρe σ _ hP v r hr; exact hP n v r hr
    | mu B ih =>
        intro ρe σ ht hP v r hr
        obtain ⟨hcl, hlfp⟩ := hr
        have hM : sClose (some ρe) (.mu B) = (VTy.mu B).subst σ := by
          simp only [sClose]; congr 1; funext n; exact ht n
        rw [hM] at hcl hlfp
        refine hlfp (G ((VTy.mu B).subst σ)) (fun v' r' h' => ?_)
        have hB := ih (VTy.scons ⟨(VTy.mu B).subst σ, G ((VTy.mu B).subst σ)⟩ ρe)
          (VTy.scons ((VTy.mu B).subst σ) σ)
          (fun n => by cases n with
            | zero => rfl
            | succ n => exact ht n)
          (fun n => by cases n with
            | zero => exact fun _ _ h => h
            | succ n => exact hP n) v' r' h'
        rw [VTy.subst_scons_eq_inst] at hB
        exact hG _ v' r' ⟨hcl, hB⟩
  intro T v ρ hT
  rw [vShape_eq_some] at hT
  have := gen T sNil .tvar (fun _ => rfl) (fun _ _ _ h => h.elim) v ρ hT
  rw [VTy.subst_id] at this
  exact this.2

/-! ### `δ`-congruence and `TyEq` -/

/-- `vShapeE` depends on `δ` only at the lifetime variables free in the type. -/
theorem vShapeE_congr : ∀ (T : VTy) (η : Option (Nat → SEnt)) {δ₁ δ₂ : LSub},
    (∀ y, VFree y T → δ₁.find? y = δ₂.find? y) → vShapeE η T δ₁ = vShapeE η T δ₂ := by
  intro T
  induction T using VTy.recV with
  | unit => intros; rfl
  | int w => intros; rfl
  | opq k => intros; rfl
  | tensor A B ihA ihB =>
      intro η δ₁ δ₂ h; funext v
      simp only [vShapeE, ihA η (fun y hy => h y (Or.inl hy)), ihB η (fun y hy => h y (Or.inr hy))]
  | zero => intros; rfl
  | sum A B ihA ihB =>
      intro η δ₁ δ₂ h; funext v
      simp only [vShapeE, ihA η (fun y hy => h y (Or.inl hy)), ihB η (fun y hy => h y (Or.inr hy))]
  | thunk _ => intros; rfl
  | ref A ih => intro η δ₁ δ₂ h; funext v; simp only [vShapeE, ih η h]
  | fam L ih => intro η δ₁ δ₂ h; funext v; simp only [vShapeE, ih η h]
  | imm a A ih =>
      intro η δ₁ δ₂ h; funext v
      simp only [vShapeE, ih η (fun y hy => h y (Or.inr hy))]
      exact atLife_congr (interp_congr a (fun w hw => h w (Or.inl hw))) rfl
  | «mut» a A ih =>
      intro η δ₁ δ₂ h; funext v
      simp only [vShapeE, ih η (fun y hy => h y (Or.inr hy))]
      exact atLife_congr (interp_congr a (fun w hw => h w (Or.inl hw))) rfl
  | box a A ih =>
      intro η δ₁ δ₂ h; funext v
      simp only [vShapeE, ih η (fun y hy => h y (Or.inr hy))]
      exact atLife_congr (interp_congr a (fun w hw => h w (Or.inl hw))) rfl
  | bang A _ => intros; rfl
  | unk => intros; rfl
  | tvar n => intros; rfl
  | mu A ih =>
      intro η δ₁ δ₂ h; funext v
      simp only [vShapeE]
      funext ρ
      congr 1
      apply propext
      refine forall_congr' fun P => imp_congr ?_ Iff.rfl
      rw [ih _ h]

/-! ### `TyEq` is an equivalence -/

mutual
theorem tyEq_symm : ∀ (S : VTy) {S' : VTy} {δ δ' : LSub}, TyEq S δ S' δ' → TyEq S' δ' S δ
  | .unit, S', _, _, h => by cases S' <;> simp_all [TyEq]
  | .zero, S', _, _, h => by cases S' <;> simp_all [TyEq]
  | .unk, S', _, _, h => by cases S' <;> simp_all [TyEq]
  | .int _, S', _, _, h => by cases S' <;> simp_all [TyEq]
  | .opq _, S', _, _, h => by cases S' <;> simp_all [TyEq]
  | .tensor A B, S', _, _, h => by
      cases S' <;> simp only [TyEq] at h ⊢
      exact ⟨tyEq_symm A h.1, tyEq_symm B h.2⟩
  | .sum A B, S', _, _, h => by
      cases S' <;> simp only [TyEq] at h ⊢
      exact ⟨tyEq_symm A h.1, tyEq_symm B h.2⟩
  | .thunk C, S', _, _, h => by
      cases S' <;> simp only [TyEq] at h ⊢
      exact cTyEq_symm C h
  | .ref A, S', _, _, h => by
      cases S' <;> simp only [TyEq] at h ⊢
      exact tyEq_symm A h
  | .fam A, S', _, _, h => by
      cases S' <;> simp only [TyEq] at h ⊢
      exact tyEq_symm A h
  | .bang A, S', _, _, h => by
      cases S' <;> simp only [TyEq] at h ⊢
      exact tyEq_symm A h
  | .box a A, S', _, _, h => by
      cases S' <;> simp only [TyEq] at h ⊢
      exact ⟨h.1.symm, tyEq_symm A h.2⟩
  | .imm a A, S', _, _, h => by
      cases S' <;> simp only [TyEq] at h ⊢
      exact ⟨h.1.symm, tyEq_symm A h.2⟩
  | .mut a A, S', _, _, h => by
      cases S' <;> simp only [TyEq] at h ⊢
      exact ⟨h.1.symm, tyEq_symm A h.2⟩
  | .tvar n, S', _, _, h => by cases S' <;> simp_all [TyEq]
  | .mu A, S', _, _, h => by
      cases S' <;> simp only [TyEq] at h ⊢
      exact tyEq_symm A h
theorem cTyEq_symm : ∀ (C : CTy) {C' : CTy} {δ δ' : LSub}, CTyEq C δ C' δ' → CTyEq C' δ' C δ
  | .ret A, C', _, _, h => by
      cases C' <;> simp only [CTyEq] at h ⊢
      exact tyEq_symm A h
  | .arr A C, C', _, _, h => by
      cases C' <;> simp only [CTyEq] at h ⊢
      exact ⟨tyEq_symm A h.1, cTyEq_symm C h.2⟩
  | .amp C D, C', _, _, h => by
      cases C' <;> simp only [CTyEq] at h ⊢
      exact ⟨cTyEq_symm C h.1, cTyEq_symm D h.2⟩
  | .top, C', _, _, h => by cases C' <;> simp_all [CTyEq]
  | .all x b C, C', _, _, h => by
      cases C' <;> simp only [CTyEq] at h ⊢
      exact ⟨h.1.symm, fun α => cTyEq_symm C (h.2 α)⟩
  | .nu C, C', _, _, h => by
      cases C' <;> simp only [CTyEq] at h ⊢
      exact cTyEq_symm C h
  | .eff _ _ _ A B C, C', _, _, h => by
      cases C' <;> simp only [CTyEq] at h ⊢
      exact ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, tyEq_symm A h.2.2.2.1, tyEq_symm B h.2.2.2.2.1,
        cTyEq_symm C h.2.2.2.2.2⟩
end

theorem TyEq.symm {S S' : VTy} {δ δ' : LSub} (h : TyEq S δ S' δ') : TyEq S' δ' S δ :=
  tyEq_symm S h

theorem CTyEq.symm {C C' : CTy} {δ δ' : LSub} (h : CTyEq C δ C' δ') : CTyEq C' δ' C δ :=
  cTyEq_symm C h

mutual
theorem tyEq_trans : ∀ (S : VTy) {S' S'' : VTy} {δ δ' δ'' : LSub}, TyEq S δ S' δ' →
    TyEq S' δ' S'' δ'' → TyEq S δ S'' δ''
  | .unit, S', S'', _, _, _, h, h' => by cases S' <;> cases S'' <;> simp_all [TyEq]
  | .zero, S', S'', _, _, _, h, h' => by cases S' <;> cases S'' <;> simp_all [TyEq]
  | .unk, S', S'', _, _, _, h, h' => by cases S' <;> cases S'' <;> simp_all [TyEq]
  | .int _, S', S'', _, _, _, h, h' => by cases S' <;> cases S'' <;> simp_all [TyEq]
  | .opq _, S', S'', _, _, _, h, h' => by cases S' <;> cases S'' <;> simp_all [TyEq]
  | .tensor A B, S', S'', _, _, _, h, h' => by
      cases S' <;> simp only [TyEq] at h
      cases S'' <;> simp only [TyEq] at h' ⊢
      exact ⟨tyEq_trans A h.1 h'.1, tyEq_trans B h.2 h'.2⟩
  | .sum A B, S', S'', _, _, _, h, h' => by
      cases S' <;> simp only [TyEq] at h
      cases S'' <;> simp only [TyEq] at h' ⊢
      exact ⟨tyEq_trans A h.1 h'.1, tyEq_trans B h.2 h'.2⟩
  | .thunk C, S', S'', _, _, _, h, h' => by
      cases S' <;> simp only [TyEq] at h
      cases S'' <;> simp only [TyEq] at h' ⊢
      exact cTyEq_trans C h h'
  | .ref A, S', S'', _, _, _, h, h' => by
      cases S' <;> simp only [TyEq] at h
      cases S'' <;> simp only [TyEq] at h' ⊢
      exact tyEq_trans A h h'
  | .fam A, S', S'', _, _, _, h, h' => by
      cases S' <;> simp only [TyEq] at h
      cases S'' <;> simp only [TyEq] at h' ⊢
      exact tyEq_trans A h h'
  | .bang A, S', S'', _, _, _, h, h' => by
      cases S' <;> simp only [TyEq] at h
      cases S'' <;> simp only [TyEq] at h' ⊢
      exact tyEq_trans A h h'
  | .box a A, S', S'', _, _, _, h, h' => by
      cases S' <;> simp only [TyEq] at h
      cases S'' <;> simp only [TyEq] at h' ⊢
      exact ⟨h.1.trans h'.1, tyEq_trans A h.2 h'.2⟩
  | .imm a A, S', S'', _, _, _, h, h' => by
      cases S' <;> simp only [TyEq] at h
      cases S'' <;> simp only [TyEq] at h' ⊢
      exact ⟨h.1.trans h'.1, tyEq_trans A h.2 h'.2⟩
  | .mut a A, S', S'', _, _, _, h, h' => by
      cases S' <;> simp only [TyEq] at h
      cases S'' <;> simp only [TyEq] at h' ⊢
      exact ⟨h.1.trans h'.1, tyEq_trans A h.2 h'.2⟩
  | .tvar n, S', S'', _, _, _, h, h' => by cases S' <;> cases S'' <;> simp_all [TyEq]
  | .mu A, S', S'', _, _, _, h, h' => by
      cases S' <;> simp only [TyEq] at h
      cases S'' <;> simp only [TyEq] at h' ⊢
      exact tyEq_trans A h h'
theorem cTyEq_trans : ∀ (C : CTy) {C' C'' : CTy} {δ δ' δ'' : LSub}, CTyEq C δ C' δ' →
    CTyEq C' δ' C'' δ'' → CTyEq C δ C'' δ''
  | .ret A, C', C'', _, _, _, h, h' => by
      cases C' <;> simp only [CTyEq] at h
      cases C'' <;> simp only [CTyEq] at h' ⊢
      exact tyEq_trans A h h'
  | .arr A C, C', C'', _, _, _, h, h' => by
      cases C' <;> simp only [CTyEq] at h
      cases C'' <;> simp only [CTyEq] at h' ⊢
      exact ⟨tyEq_trans A h.1 h'.1, cTyEq_trans C h.2 h'.2⟩
  | .amp C D, C', C'', _, _, _, h, h' => by
      cases C' <;> simp only [CTyEq] at h
      cases C'' <;> simp only [CTyEq] at h' ⊢
      exact ⟨cTyEq_trans C h.1 h'.1, cTyEq_trans D h.2 h'.2⟩
  | .top, C', C'', _, _, _, h, h' => by cases C' <;> cases C'' <;> simp_all [CTyEq]
  | .all x b C, C', C'', _, _, _, h, h' => by
      cases C' <;> simp only [CTyEq] at h
      cases C'' <;> simp only [CTyEq] at h' ⊢
      exact ⟨h.1.trans h'.1, fun α => cTyEq_trans C (h.2 α) (h'.2 α)⟩
  | .nu C, C', C'', _, _, _, h, h' => by
      cases C' <;> simp only [CTyEq] at h
      cases C'' <;> simp only [CTyEq] at h' ⊢
      exact cTyEq_trans C h h'
  | .eff _ _ _ A B C, C', C'', _, _, _, h, h' => by
      cases C' <;> simp only [CTyEq] at h
      cases C'' <;> simp only [CTyEq] at h' ⊢
      exact ⟨h.1.trans h'.1, h.2.1.trans h'.2.1, h.2.2.1.trans h'.2.2.1,
        tyEq_trans A h.2.2.2.1 h'.2.2.2.1, tyEq_trans B h.2.2.2.2.1 h'.2.2.2.2.1,
        cTyEq_trans C h.2.2.2.2.2 h'.2.2.2.2.2⟩
end

theorem TyEq.trans {S S' S'' : VTy} {δ δ' δ'' : LSub} (h : TyEq S δ S' δ')
    (h' : TyEq S' δ' S'' δ'') : TyEq S δ S'' δ'' := tyEq_trans S h h'

theorem CTyEq.trans {C C' C'' : CTy} {δ δ' δ'' : LSub} (h : CTyEq C δ C' δ')
    (h' : CTyEq C' δ' C'' δ'') : CTyEq C δ C'' δ'' := cTyEq_trans C h h'

mutual
theorem TyEq.of_agree : ∀ (T : VTy) {δ₁ δ₂ : LSub},
    (∀ y, VFree y T → δ₁.find? y = δ₂.find? y) → TyEq T δ₁ T δ₂
  | .unit, _, _, _ => trivial
  | .zero, _, _, _ => trivial
  | .unk, _, _, _ => trivial
  | .int _, _, _, _ => rfl
  | .opq _, _, _, _ => rfl
  | .tensor A B, _, _, h => ⟨TyEq.of_agree A (fun y hy => h y (Or.inl hy)),
      TyEq.of_agree B (fun y hy => h y (Or.inr hy))⟩
  | .sum A B, _, _, h => ⟨TyEq.of_agree A (fun y hy => h y (Or.inl hy)),
      TyEq.of_agree B (fun y hy => h y (Or.inr hy))⟩
  | .thunk C, _, _, h => CTyEq.of_agree C h
  | .ref A, _, _, h => TyEq.of_agree A h
  | .fam A, _, _, h => TyEq.of_agree A h
  | .bang A, _, _, h => TyEq.of_agree A h
  | .box a A, _, _, h => ⟨interp_congr a (fun y hy => h y (Or.inl hy)),
      TyEq.of_agree A (fun y hy => h y (Or.inr hy))⟩
  | .imm a A, _, _, h => ⟨interp_congr a (fun y hy => h y (Or.inl hy)),
      TyEq.of_agree A (fun y hy => h y (Or.inr hy))⟩
  | .mut a A, _, _, h => ⟨interp_congr a (fun y hy => h y (Or.inl hy)),
      TyEq.of_agree A (fun y hy => h y (Or.inr hy))⟩
  | .tvar _, _, _, _ => rfl
  | .mu A, _, _, h => TyEq.of_agree A h
theorem CTyEq.of_agree : ∀ (C : CTy) {δ₁ δ₂ : LSub},
    (∀ y, CFree y C → δ₁.find? y = δ₂.find? y) → CTyEq C δ₁ C δ₂
  | .ret A, _, _, h => TyEq.of_agree A h
  | .arr A C, _, _, h => ⟨TyEq.of_agree A (fun y hy => h y (Or.inl hy)),
      CTyEq.of_agree C (fun y hy => h y (Or.inr hy))⟩
  | .amp C D, _, _, h => ⟨CTyEq.of_agree C (fun y hy => h y (Or.inl hy)),
      CTyEq.of_agree D (fun y hy => h y (Or.inr hy))⟩
  | .top, _, _, _ => trivial
  | .all x b C, δ₁, δ₂, h => by
      refine ⟨interp_congr b (fun y hy => h y (Or.inl hy)), fun α => ?_⟩
      refine CTyEq.of_agree C (fun y hy => ?_)
      by_cases hxy : x = y
      · subst hxy; rw [find?_extend_self, find?_extend_self]
      · rw [find?_extend_ne _ _ hxy, find?_extend_ne _ _ hxy]
        exact h y (Or.inr ⟨Ne.symm hxy, hy⟩)
  | .nu C, _, _, h => CTyEq.of_agree C h
  | .eff _ _ _ A B C, _, _, h => ⟨rfl, rfl, rfl, TyEq.of_agree A (fun y hy => h y (Or.inl hy)),
      TyEq.of_agree B (fun y hy => h y (Or.inr (Or.inl hy))),
      CTyEq.of_agree C (fun y hy => h y (Or.inr (Or.inr hy)))⟩
end

theorem TyEq.refl (T : VTy) (δ : LSub) : TyEq T δ T δ := TyEq.of_agree T (fun _ _ => rfl)

theorem CTyEq.refl (C : CTy) (δ : LSub) : CTyEq C δ C δ := CTyEq.of_agree C (fun _ _ => rfl)

/-! ### `TyEq` under type substitution -/

theorem TyEq.rename : ∀ (A : VTy) {A' : VTy} {δ δ' : LSub} (r : Nat → Nat),
    TyEq A δ A' δ' → TyEq (A.rename r) δ (A'.rename r) δ' := by
  intro A
  induction A using VTy.recV with
  | unit => intro A' _ _ r h; cases A' <;> simp_all [TyEq, VTy.rename]
  | int w => intro A' _ _ r h; cases A' <;> simp_all [TyEq, VTy.rename]
  | opq k => intro A' _ _ r h; cases A' <;> simp_all [TyEq, VTy.rename]
  | zero => intro A' _ _ r h; cases A' <;> simp_all [TyEq, VTy.rename]
  | unk => intro A' _ _ r h; cases A' <;> simp_all [TyEq, VTy.rename]
  | thunk C => intro A' _ _ r h; cases A' <;> simp_all [TyEq, VTy.rename]
  | tvar n => intro A' _ _ r h; cases A' <;> simp_all [TyEq, VTy.rename]
  | tensor A B ihA ihB =>
      intro A' _ _ r h; cases A' <;> simp only [TyEq, VTy.rename] at h ⊢
      exact ⟨ihA r h.1, ihB r h.2⟩
  | sum A B ihA ihB =>
      intro A' _ _ r h; cases A' <;> simp only [TyEq, VTy.rename] at h ⊢
      exact ⟨ihA r h.1, ihB r h.2⟩
  | ref A ih => intro A' _ _ r h; cases A' <;> simp only [TyEq, VTy.rename] at h ⊢; exact ih r h
  | fam A ih => intro A' _ _ r h; cases A' <;> simp only [TyEq, VTy.rename] at h ⊢; exact ih r h
  | bang A ih => intro A' _ _ r h; cases A' <;> simp only [TyEq, VTy.rename] at h ⊢; exact ih r h
  | imm a A ih =>
      intro A' _ _ r h; cases A' <;> simp only [TyEq, VTy.rename] at h ⊢; exact ⟨h.1, ih r h.2⟩
  | «mut» a A ih =>
      intro A' _ _ r h; cases A' <;> simp only [TyEq, VTy.rename] at h ⊢; exact ⟨h.1, ih r h.2⟩
  | box a A ih =>
      intro A' _ _ r h; cases A' <;> simp only [TyEq, VTy.rename] at h ⊢; exact ⟨h.1, ih r h.2⟩
  | mu A ih =>
      intro A' _ _ r h; cases A' <;> simp only [TyEq, VTy.rename] at h ⊢; exact ih _ h

theorem TyEq.subst : ∀ (A : VTy) {A' : VTy} {δ δ' : LSub} (σ σ' : Nat → VTy),
    TyEq A δ A' δ' → (∀ n, TyEq (σ n) δ (σ' n) δ') → TyEq (A.subst σ) δ (A'.subst σ') δ' := by
  intro A
  induction A using VTy.recV with
  | unit => intro A' _ _ σ σ' h _; cases A' <;> simp_all [TyEq, VTy.subst]
  | int w => intro A' _ _ σ σ' h _; cases A' <;> simp_all [TyEq, VTy.subst]
  | opq k => intro A' _ _ σ σ' h _; cases A' <;> simp_all [TyEq, VTy.subst]
  | zero => intro A' _ _ σ σ' h _; cases A' <;> simp_all [TyEq, VTy.subst]
  | unk => intro A' _ _ σ σ' h _; cases A' <;> simp_all [TyEq, VTy.subst]
  | thunk C => intro A' _ _ σ σ' h _; cases A' <;> simp_all [TyEq, VTy.subst]
  | tvar n =>
      intro A' _ _ σ σ' h hσ; cases A' <;> simp only [TyEq] at h
      subst h; exact hσ _
  | tensor A B ihA ihB =>
      intro A' _ _ σ σ' h hσ; cases A' <;> simp only [TyEq, VTy.subst] at h ⊢
      exact ⟨ihA σ σ' h.1 hσ, ihB σ σ' h.2 hσ⟩
  | sum A B ihA ihB =>
      intro A' _ _ σ σ' h hσ; cases A' <;> simp only [TyEq, VTy.subst] at h ⊢
      exact ⟨ihA σ σ' h.1 hσ, ihB σ σ' h.2 hσ⟩
  | ref A ih =>
      intro A' _ _ σ σ' h hσ; cases A' <;> simp only [TyEq, VTy.subst] at h ⊢; exact ih σ σ' h hσ
  | fam A ih =>
      intro A' _ _ σ σ' h hσ; cases A' <;> simp only [TyEq, VTy.subst] at h ⊢; exact ih σ σ' h hσ
  | bang A ih =>
      intro A' _ _ σ σ' h hσ; cases A' <;> simp only [TyEq, VTy.subst] at h ⊢; exact ih σ σ' h hσ
  | imm a A ih =>
      intro A' _ _ σ σ' h hσ; cases A' <;> simp only [TyEq, VTy.subst] at h ⊢
      exact ⟨h.1, ih σ σ' h.2 hσ⟩
  | «mut» a A ih =>
      intro A' _ _ σ σ' h hσ; cases A' <;> simp only [TyEq, VTy.subst] at h ⊢
      exact ⟨h.1, ih σ σ' h.2 hσ⟩
  | box a A ih =>
      intro A' _ _ σ σ' h hσ; cases A' <;> simp only [TyEq, VTy.subst] at h ⊢
      exact ⟨h.1, ih σ σ' h.2 hσ⟩
  | mu A ih =>
      intro A' _ _ σ σ' h hσ; cases A' <;> simp only [TyEq, VTy.subst] at h ⊢
      refine ih _ _ h (fun n => ?_)
      cases n with
      | zero => show (0 : Nat) = 0; rfl
      | succ n => exact TyEq.rename _ Nat.succ (hσ n)

theorem TyEq.Cl_iff : ∀ (A : VTy) {A' : VTy} {δ δ' : LSub} (k : Nat),
    TyEq A δ A' δ' → (A.Cl k ↔ A'.Cl k) := by
  intro A
  induction A using VTy.recV with
  | unit => intro A' _ _ k h; cases A' <;> simp_all [TyEq, VTy.Cl]
  | int w => intro A' _ _ k h; cases A' <;> simp_all [TyEq, VTy.Cl]
  | opq k => intro A' _ _ k h; cases A' <;> simp_all [TyEq, VTy.Cl]
  | zero => intro A' _ _ k h; cases A' <;> simp_all [TyEq, VTy.Cl]
  | unk => intro A' _ _ k h; cases A' <;> simp_all [TyEq, VTy.Cl]
  | thunk C => intro A' _ _ k h; cases A' <;> simp_all [TyEq, VTy.Cl]
  | tvar n => intro A' _ _ k h; cases A' <;> simp only [TyEq] at h; subst h; exact Iff.rfl
  | tensor A B ihA ihB =>
      intro A' _ _ k h; cases A' <;> simp only [TyEq] at h
      exact and_congr (ihA k h.1) (ihB k h.2)
  | sum A B ihA ihB =>
      intro A' _ _ k h; cases A' <;> simp only [TyEq] at h
      exact and_congr (ihA k h.1) (ihB k h.2)
  | ref A ih => intro A' _ _ k h; cases A' <;> simp only [TyEq] at h; simp only [VTy.Cl]; exact ih k h
  | fam A ih => intro A' _ _ k h; cases A' <;> simp only [TyEq] at h; simp only [VTy.Cl]; exact ih k h
  | bang A ih => intro A' _ _ k h; cases A' <;> simp only [TyEq] at h; simp only [VTy.Cl]; exact ih k h
  | imm a A ih => intro A' _ _ k h; cases A' <;> simp only [TyEq] at h; simp only [VTy.Cl]; exact ih k h.2
  | «mut» a A ih => intro A' _ _ k h; cases A' <;> simp only [TyEq] at h; simp only [VTy.Cl]; exact ih k h.2
  | box a A ih => intro A' _ _ k h; cases A' <;> simp only [TyEq] at h; simp only [VTy.Cl]; exact ih k h.2
  | mu A ih => intro A' _ _ k h; cases A' <;> simp only [TyEq] at h; simp only [VTy.Cl]; exact ih (k + 1) h

theorem TyEq.occ_iff : ∀ (A : VTy) {A' : VTy} {δ δ' : LSub} (k : Nat),
    TyEq A δ A' δ' → (A.Occ k ↔ A'.Occ k) := by
  intro A
  induction A using VTy.recV with
  | unit => intro A' _ _ k h; cases A' <;> simp_all [TyEq, VTy.Occ]
  | int w => intro A' _ _ k h; cases A' <;> simp_all [TyEq, VTy.Occ]
  | opq k => intro A' _ _ k h; cases A' <;> simp_all [TyEq, VTy.Occ]
  | zero => intro A' _ _ k h; cases A' <;> simp_all [TyEq, VTy.Occ]
  | unk => intro A' _ _ k h; cases A' <;> simp_all [TyEq, VTy.Occ]
  | thunk C => intro A' _ _ k h; cases A' <;> simp_all [TyEq, VTy.Occ]
  | tvar n => intro A' _ _ k h; cases A' <;> simp only [TyEq] at h; subst h; exact Iff.rfl
  | tensor A B ihA ihB =>
      intro A' _ _ k h; cases A' <;> simp only [TyEq] at h
      exact or_congr (ihA k h.1) (ihB k h.2)
  | sum A B ihA ihB =>
      intro A' _ _ k h; cases A' <;> simp only [TyEq] at h
      exact or_congr (ihA k h.1) (ihB k h.2)
  | ref A ih => intro A' _ _ k h; cases A' <;> simp only [TyEq] at h; simp only [VTy.Occ]; exact ih k h
  | fam A ih => intro A' _ _ k h; cases A' <;> simp only [TyEq] at h; simp only [VTy.Occ]; exact ih k h
  | bang A ih => intro A' _ _ k h; cases A' <;> simp only [TyEq] at h; simp only [VTy.Occ]; exact ih k h
  | imm a A ih => intro A' _ _ k h; cases A' <;> simp only [TyEq] at h; simp only [VTy.Occ]; exact ih k h.2
  | «mut» a A ih => intro A' _ _ k h; cases A' <;> simp only [TyEq] at h; simp only [VTy.Occ]; exact ih k h.2
  | box a A ih => intro A' _ _ k h; cases A' <;> simp only [TyEq] at h; simp only [VTy.Occ]; exact ih k h.2
  | mu A ih => intro A' _ _ k h; cases A' <;> simp only [TyEq] at h; simp only [VTy.Occ]; exact ih (k + 1) h

theorem TyEq.noMut_iff : ∀ (A : VTy) {A' : VTy} {δ δ' : LSub} (k : Nat),
    TyEq A δ A' δ' → (A.NoMut k ↔ A'.NoMut k) := by
  intro A
  induction A using VTy.recV with
  | unit => intro A' _ _ k h; cases A' <;> simp_all [TyEq, VTy.NoMut]
  | int w => intro A' _ _ k h; cases A' <;> simp_all [TyEq, VTy.NoMut]
  | opq k => intro A' _ _ k h; cases A' <;> simp_all [TyEq, VTy.NoMut]
  | zero => intro A' _ _ k h; cases A' <;> simp_all [TyEq, VTy.NoMut]
  | unk => intro A' _ _ k h; cases A' <;> simp_all [TyEq, VTy.NoMut]
  | thunk C => intro A' _ _ k h; cases A' <;> simp_all [TyEq, VTy.NoMut]
  | tvar n => intro A' _ _ k h; cases A' <;> simp only [TyEq] at h; subst h; exact Iff.rfl
  | tensor A B ihA ihB =>
      intro A' _ _ k h; cases A' <;> simp only [TyEq] at h
      exact and_congr (ihA k h.1) (ihB k h.2)
  | sum A B ihA ihB =>
      intro A' _ _ k h; cases A' <;> simp only [TyEq] at h
      exact and_congr (ihA k h.1) (ihB k h.2)
  | ref A ih => intro A' _ _ k h; cases A' <;> simp only [TyEq] at h; simp only [VTy.NoMut]; exact ih k h
  | fam A ih => intro A' _ _ k h; cases A' <;> simp only [TyEq] at h; simp only [VTy.NoMut]; exact ih k h
  | bang A ih => intro A' _ _ k h; cases A' <;> simp only [TyEq] at h; simp only [VTy.NoMut]; exact ih k h
  | imm a A ih => intro A' _ _ k h; cases A' <;> simp only [TyEq] at h; simp only [VTy.NoMut]; exact ih k h.2
  | «mut» a A _ =>
      intro A' _ _ k h; cases A' <;> simp only [TyEq] at h; simp only [VTy.NoMut]
      exact not_congr (TyEq.occ_iff A k h.2)
  | box a A ih => intro A' _ _ k h; cases A' <;> simp only [TyEq] at h; simp only [VTy.NoMut]; exact ih k h.2
  | mu A ih => intro A' _ _ k h; cases A' <;> simp only [TyEq] at h; simp only [VTy.NoMut]; exact ih (k + 1) h

theorem TyEq.inst {A A' S S' : VTy} {δ δ' : LSub} (hA : TyEq A δ A' δ') (hS : TyEq S δ S' δ') :
    TyEq (VTy.inst S A) δ (VTy.inst S' A') δ' :=
  TyEq.subst A _ _ hA (fun n => by
    cases n with
    | zero => exact hS
    | succ n => show n = n; rfl)

/-- `vShapeE` reads a type only up to `TyEq`, at environments with equal candidates and
`TyEq` types. -/
theorem vShapeE_tyEq : ∀ (A : VTy) {A' : VTy} {δ δ' : LSub} (η η' : Nat → SEnt),
    TyEq A δ A' δ' → (∀ n, (η n).P = (η' n).P ∧ TyEq (η n).ty δ (η' n).ty δ') →
    vShapeE (some η) A δ = vShapeE (some η') A' δ' := by
  intro A
  induction A using VTy.recV with
  | unit => intro A' _ _ η η' h _; cases A' <;> first | rfl | simp_all [TyEq]
  | int w =>
      intro A' _ _ η η' h _; cases A' <;> simp only [TyEq] at h
      subst h; rfl
  | opq k =>
      intro A' _ _ η η' h _; cases A' <;> simp only [TyEq] at h
      subst h; rfl
  | zero => intro A' _ _ η η' h _; cases A' <;> first | rfl | simp_all [TyEq]
  | unk => intro A' _ _ η η' h _; cases A' <;> first | rfl | simp_all [TyEq]
  | thunk C => intro A' _ _ η η' h _; cases A' <;> first | rfl | simp_all [TyEq]
  | tvar n =>
      intro A' _ _ η η' h hη; cases A' <;> simp only [TyEq] at h
      subst h; funext v; exact congrFun (hη n).1 v
  | tensor A B ihA ihB =>
      intro A' _ _ η η' h hη; cases A' <;> simp only [TyEq] at h
      funext v; simp only [vShapeE, ihA η η' h.1 hη, ihB η η' h.2 hη]
  | sum A B ihA ihB =>
      intro A' _ _ η η' h hη; cases A' <;> simp only [TyEq] at h
      funext v; simp only [vShapeE, ihA η η' h.1 hη, ihB η η' h.2 hη]
  | ref A ih =>
      intro A' _ _ η η' h hη; cases A' <;> simp only [TyEq] at h
      funext v; simp only [vShapeE, ih η η' h hη]
  | fam A ih =>
      intro A' _ _ η η' h hη; cases A' <;> simp only [TyEq] at h
      funext v; simp only [vShapeE, ih η η' h hη]
  | bang A _ => intro A' _ _ η η' h _; cases A' <;> first | rfl | simp_all [TyEq]
  | imm a A ih =>
      intro A' _ _ η η' h hη; cases A' <;> simp only [TyEq] at h
      funext v; simp only [vShapeE, ih η η' h.2 hη]; exact atLife_congr h.1 rfl
  | «mut» a A ih =>
      intro A' _ _ η η' h hη; cases A' <;> simp only [TyEq] at h
      funext v; simp only [vShapeE, ih η η' h.2 hη]; exact atLife_congr h.1 rfl
  | box a A ih =>
      intro A' _ _ η η' h hη; cases A' <;> simp only [TyEq] at h
      funext v; simp only [vShapeE, ih η η' h.2 hη]; exact atLife_congr h.1 rfl
  | mu A ih =>
      intro A' δ δ' η η' h hη; cases A' <;> simp only [TyEq] at h
      rename_i A'
      have hM : TyEq (sClose (some η) (.mu A)) δ (sClose (some η') (.mu A')) δ' :=
        TyEq.subst (.mu A) _ _ h (fun n => (hη n).2)
      funext v ρ
      simp only [vShapeE]
      rw [(TyEq.Cl_iff _ 0 hM)]
      congr 1
      apply propext
      refine forall_congr' fun P => imp_congr ?_ Iff.rfl
      rw [ih (VTy.scons ⟨sClose (some η) (.mu A), P⟩ (sEnv (some η)))
        (VTy.scons ⟨sClose (some η') (.mu A'), P⟩ (sEnv (some η'))) h (fun n => by
        cases n with
        | zero => exact ⟨rfl, hM⟩
        | succ n => exact hη n)]

/-- `vShape` reads a type only up to `TyEq`. -/
theorem vShape_tyEq {S S' : VTy} {δ δ' : LSub} (h : TyEq S δ S' δ') : vShape S δ = vShape S' δ' := by
  rw [vShape_eq_some]
  exact vShapeE_tyEq S _ _ h (fun n => ⟨rfl, show n = n from rfl⟩)

theorem vShape_congr (T : VTy) {δ₁ δ₂ : LSub} (h : ∀ y, VFree y T → δ₁.find? y = δ₂.find? y) :
    vShape T δ₁ = vShape T δ₂ := vShapeE_congr T none h

/-- `Imm̲` at a closed `μ` is read at the reborrow of the unrolling. -/
theorem vShape_immReborrow_mu_iff {A : VTy} (hA : A.Cl 1) (b : Lifetime.Life) (δ : LSub) (v : Val)
    (ρ : WRes) : vShape ((VTy.mu A).immReborrow b) δ v ρ ↔
      vShape ((VTy.inst (.mu A) A).immReborrow b) δ v ρ := by
  rw [VTy.immReborrow_mu b hA, VTy.immReborrow_unroll' b hA, vShape_mu_iff]
  exact ⟨fun h => h.2, fun h => ⟨VTy.Cl_immX b hA, h⟩⟩

end BoCa.Fig16.LogRel.Core

end
