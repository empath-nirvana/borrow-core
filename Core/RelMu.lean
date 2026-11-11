import Paper.S5_Model.Definitions
import Paper.S6_5_NonStandardEntailments.Lemmas
import Support.LogicalRelation.Facts
import Support.Model.Notation
import Core.Relation
import Core.ShapeMu

/-!
# Core — the relation at `μ`  `[spec §6]`

`vCE` reads a type variable at its environment entry and `μX. A` at the least fixed point
`⋂{P | A[P/X] ⊆ P}`, joint over the mode and the record list.  This file proves:

* the environment of a closed type is the empty one read explicitly (`vCE_some`);
* renaming and substitution move into the environment (`vCE_rename`, `vCE_subst`);
* the relation reads only the entries of the variables that occur (`vCE_congr_occ`);
* monotonicity in an entry whose variable is outside every `Mut` payload (`vCE_mono_at`);
* **the unroll equation** `vC (μX. A) ↔ vC (A[μX. A/X])`, at a `μ` whose variable is outside
  its `Mut` payloads and which is closed (`vC_mu_iff`, with `vC_unfold`/`vC_roll`);
* **the induction principle** at every type (`vC_ind`): a property closed under one unfolding
  of every clause (`vF`) holds of `vC`, in both modes.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### Coherence and the `imm` payload -/

theorem cohE_of_coh {rs : List FrameRec} {m : Loc} {S : VTy} {δ : LSub} (h : Coh rs m S δ) :
    CohE rs m S δ := ⟨S, δ, TyEq.refl S δ, h⟩

theorem CohE.tyEq {rs : List FrameRec} {m : Loc} {S S' : VTy} {δ δ' : LSub}
    (he : TyEq S δ S' δ') (h : CohE rs m S' δ') : CohE rs m S δ := by
  obtain ⟨S₀, δ₀, he₀, hc⟩ := h
  exact ⟨S₀, δ₀, he.trans he₀, hc⟩

/-! ### Lemma 6.113 (I-mono) at the typed world; record in `Paper/S6_5_NonStandardEntailments/Lemmas.lean` -/
/-- `ptoImmS` is monotone in its payload.  6.172 (`withbor1`) frames a payload at the
program's relation (6.64 at `vC true`); the relation's `Imm` clause asks it at the
observable view. -/
theorem ptoImmS_mono {l : Loc} {α : Life} {ls : List SRec} {P P' : List SRec → Val → WProp}
    (h : ∀ ls₀ u σ, P ls₀ u σ → P' ls₀ u σ) {ρ : WRes} (hp : ptoImmS l α ls P ρ) :
    ptoImmS l α ls P' ρ := by
  obtain ⟨s, u, σ, hs, ls₀, hρ, hP, hα, hls₀⟩ := hp
  exact ⟨s, u, σ, hs, ls₀, hρ, h _ _ _ hP, hα, hls₀⟩

theorem ptoImmSv_mono {l : Loc} {α : Life} {ls : List SRec} {u : Val}
    {P P' : List SRec → Val → WProp}
    (h : ∀ ls₀ u σ, P ls₀ u σ → P' ls₀ u σ) {ρ : WRes} (hp : ptoImmSv l α ls u P ρ) :
    ptoImmSv l α ls u P' ρ := by
  obtain ⟨s, σ, hs, ls₀, hρ, hP, hα, hls₀⟩ := hp
  exact ⟨s, σ, hs, ls₀, hρ, h _ _ _ hP, hα, hls₀⟩

/-- A stored value's view is a `ptoImmS` cell. -/
theorem ptoImmS_of_v {l : Loc} {α : Life} {ls : List SRec} {u : Val}
    {P : List SRec → Val → WProp} {ρ : WRes} (hp : ptoImmSv l α ls u P ρ) : ptoImmS l α ls P ρ := by
  obtain ⟨s, σ, hs, ls₀, hρ, hP, hα, hls₀⟩ := hp
  exact ⟨s, u, σ, hs, ls₀, hρ, hP, hα, hls₀⟩

/-! ### The environment -/

theorem TEnt.ext' {a b : TEnt} (h₁ : a.ty = b.ty) (h₂ : a.P = b.P) (h₃ : a.S = b.S) : a = b := by
  cases a; cases b; simp only at h₁ h₂ h₃; subst h₁; subst h₂; subst h₃; rfl

theorem tEnvP_eq (η : Option (Nat → TEnt)) (n : Nat) (b : Bool) (ls : List SRec) (v : Val) :
    tEnvP η n b ls v = (tEnv η n).P b ls v := by
  cases η <;> rfl

theorem tEnvS_eq (η : Option (Nat → TEnt)) (n : Nat) (α : Life) (ls : List SRec) (v : Val) :
    tEnvS η n α ls v = (tEnv η n).S α ls v := by
  cases η <;> rfl

theorem tClose_eq (η : Option (Nat → TEnt)) (A : VTy) :
    tClose η A = A.subst (fun n => (tEnv η n).ty) := by
  cases η with
  | none => exact (VTy.subst_id A).symm
  | some η => rfl

/-- The relation and the views read their environment only through `tEnv`. -/
theorem vCE_shrE_some (η : Option (Nat → TEnt)) :
    ∀ (A : VTy), (∀ b : Bool, vCE η b A = vCE (some (tEnv η)) b A) ∧
      shrE η A = shrE (some (tEnv η)) A := by
  intro A
  induction A using VTy.recV with
  | unit => exact ⟨fun _ => rfl, rfl⟩
  | int w => exact ⟨fun _ => rfl, rfl⟩
  | opq k => exact ⟨fun _ => rfl, rfl⟩
  | tensor A B ihA ihB =>
      refine ⟨fun b => ?_, ?_⟩
      · funext ls δ v; simp only [vCE, ihA.1, ihB.1]
      · funext α ls δ v; simp only [shrE, ihA.2, ihB.2]
  | zero => exact ⟨fun _ => rfl, rfl⟩
  | sum A B ihA ihB =>
      refine ⟨fun b => ?_, ?_⟩
      · funext ls δ v; simp only [vCE, ihA.1, ihB.1]
      · funext α ls δ v; simp only [shrE, ihA.2, ihB.2]
  | thunk _ => exact ⟨fun b => by cases b <;> rfl, rfl⟩
  | code _ _ _ _ => exact ⟨fun b => by cases b <;> rfl, rfl⟩
  | ref A ih =>
      refine ⟨fun b => ?_, ?_⟩
      · funext ls δ v; simp only [vCE, ih.1]
      · funext α ls δ v; simp only [shrE, ih.1, ih.2]
  | fam L ih =>
      refine ⟨fun b => ?_, ?_⟩
      · funext ls δ v; simp only [vCE, ih.1]
      · funext α ls δ v; simp only [shrE, ih.2]
  | imm a A ih =>
      refine ⟨fun b => ?_, rfl⟩
      funext ls δ v
      have e : tClose η A = tClose (some (tEnv η)) A := by rw [tClose_eq]; rfl
      simp only [vCE, ih.1, ih.2, e]
  | «mut» a A ih =>
      refine ⟨fun b => ?_, ?_⟩
      · funext ls δ v; simp only [vCE, ih.1]
      · funext α ls δ v; simp only [shrE, ih.1, ih.2]
  | box a A ih =>
      refine ⟨fun b => ?_, ?_⟩
      · funext ls δ v; simp only [vCE, ih.1]
      · funext α ls δ v; simp only [shrE, ih.2]
  | bang A ih =>
      refine ⟨fun b => ?_, rfl⟩
      funext ls δ v; simp only [vCE, ih.1]
  | unk => exact ⟨fun _ => rfl, rfl⟩
  | tvar n =>
      refine ⟨fun b => ?_, ?_⟩
      · funext ls δ v; simp only [vCE, tEnvP_eq]; rfl
      · funext α ls δ v; simp only [shrE, tEnvS_eq]; rfl
  | mu A _ =>
      have e : tClose η (.mu A) = tClose (some (tEnv η)) (.mu A) := by rw [tClose_eq]; rfl
      refine ⟨fun b => ?_, ?_⟩
      · funext ls δ v; simp only [vCE, e]; rfl
      · funext α ls δ v; simp only [shrE, e]; rfl

theorem vCE_some (η : Option (Nat → TEnt)) :
    ∀ (A : VTy) (b : Bool), vCE η b A = vCE (some (tEnv η)) b A :=
  fun A => (vCE_shrE_some η A).1

theorem shrE_some (η : Option (Nat → TEnt)) (A : VTy) : shrE η A = shrE (some (tEnv η)) A :=
  (vCE_shrE_some η A).2

/-- The environment of a closed type. -/
abbrev tNil : Nat → TEnt := tEnv none

theorem vC_eq_some (b : Bool) (A : VTy) : vC b A = vCE (some tNil) b A := vCE_some none A b

theorem shr_eq_some (A : VTy) : shrE none A = shrE (some tNil) A := shrE_some none A

/-! ### Renaming and substitution -/

theorem vCE_shrE_rename : ∀ (A : VTy) (ρ : Nat → TEnt) (r : Nat → Nat),
    (∀ b, vCE (some ρ) b (A.rename r) = vCE (some (ρ ∘ r)) b A) ∧
      shrE (some ρ) (A.rename r) = shrE (some (ρ ∘ r)) A := by
  intro A
  induction A using VTy.recV with
  | unit => intro ρ r; exact ⟨fun _ => rfl, rfl⟩
  | int w => intro ρ r; exact ⟨fun _ => rfl, rfl⟩
  | opq k => intro ρ r; exact ⟨fun _ => rfl, rfl⟩
  | tensor A B ihA ihB =>
      intro ρ r
      refine ⟨fun b => ?_, ?_⟩
      · funext ls δ v; simp only [VTy.rename, vCE, (ihA ρ r).1, (ihB ρ r).1]
      · funext α ls δ v; simp only [VTy.rename, shrE, (ihA ρ r).2, (ihB ρ r).2]
  | zero => intro ρ r; exact ⟨fun _ => rfl, rfl⟩
  | sum A B ihA ihB =>
      intro ρ r
      refine ⟨fun b => ?_, ?_⟩
      · funext ls δ v; simp only [VTy.rename, vCE, (ihA ρ r).1, (ihB ρ r).1]
      · funext α ls δ v; simp only [VTy.rename, shrE, (ihA ρ r).2, (ihB ρ r).2]
  | thunk _ => intro ρ r; exact ⟨fun b => by cases b <;> rfl, rfl⟩
  | code _ _ _ _ => intro ρ r; exact ⟨fun b => by cases b <;> rfl, rfl⟩
  | ref A ih =>
      intro ρ r
      refine ⟨fun b => ?_, ?_⟩
      · funext ls δ v; simp only [VTy.rename, vCE, (ih ρ r).1]
      · funext α ls δ v; simp only [VTy.rename, shrE, (ih ρ r).1, (ih ρ r).2]
  | fam L ih =>
      intro ρ r
      refine ⟨fun b => ?_, ?_⟩
      · funext ls δ v; simp only [VTy.rename, vCE, (ih ρ r).1]
      · funext α ls δ v; simp only [VTy.rename, shrE, (ih ρ r).2]
  | imm a A ih =>
      intro ρ r
      refine ⟨fun b => ?_, rfl⟩
      funext ls δ v
      have e : tClose (some ρ) (A.rename r) = tClose (some (ρ ∘ r)) A := by
        simp only [tClose, VTy.subst_rename]; rfl
      simp only [VTy.rename, vCE, (ih ρ r).1, (ih ρ r).2, e]
  | «mut» a A ih =>
      intro ρ r
      refine ⟨fun b => ?_, ?_⟩
      · funext ls δ v; simp only [VTy.rename, vCE, (ih ρ r).1]
      · funext α ls δ v; simp only [VTy.rename, shrE, (ih ρ r).1, (ih ρ r).2]
  | box a A ih =>
      intro ρ r
      refine ⟨fun b => ?_, ?_⟩
      · funext ls δ v; simp only [VTy.rename, vCE, (ih ρ r).1]
      · funext α ls δ v; simp only [VTy.rename, shrE, (ih ρ r).2]
  | bang A ih =>
      intro ρ r
      refine ⟨fun b => ?_, rfl⟩
      funext ls δ v; simp only [VTy.rename, vCE, (ih ρ r).1]
  | unk => intro ρ r; exact ⟨fun _ => rfl, rfl⟩
  | tvar n => intro ρ r; exact ⟨fun _ => rfl, rfl⟩
  | mu A ih =>
      intro ρ r
      have e' : tClose (some ρ) (.mu (A.rename (VTy.upR r))) = tClose (some (ρ ∘ r)) (.mu A) := by
        simp only [tClose]
        rw [show VTy.mu (A.rename (VTy.upR r)) = (VTy.mu A).rename r from rfl, VTy.subst_rename]
        rfl
      have ih1 := fun ρ r => (ih ρ r).1
      have ih2 := fun ρ r => (ih ρ r).2
      refine ⟨fun b => ?_, ?_⟩
      · funext ls δ v
        simp only [VTy.rename, vCE, e', tEnv, ih1, ih2, scons_comp_upR, VTy.noMut_rename_upR_iff]
      · funext α ls δ v
        simp only [VTy.rename, shrE, e', tEnv, ih1, ih2, scons_comp_upR, VTy.noMut_rename_upR_iff]

theorem vCE_rename (A : VTy) (ρ : Nat → TEnt) (r : Nat → Nat) (b : Bool) :
    vCE (some ρ) b (A.rename r) = vCE (some (ρ ∘ r)) b A := (vCE_shrE_rename A ρ r).1 b

theorem shrE_rename (A : VTy) (ρ : Nat → TEnt) (r : Nat → Nat) :
    shrE (some ρ) (A.rename r) = shrE (some (ρ ∘ r)) A := (vCE_shrE_rename A ρ r).2

/-- The environment a substitution moves into. -/
def substEnv (ρ : Nat → TEnt) (σ : Nat → VTy) (δ : LSub) : Nat → TEnt :=
  fun n => ⟨(σ n).subst (fun k => (ρ k).ty), fun b ls => vCE (some ρ) b (σ n) ls δ,
    fun α ls => shrE (some ρ) (σ n) α ls δ⟩

theorem vCE_shrE_subst : ∀ (A : VTy) (ρ : Nat → TEnt) (σ : Nat → VTy) (δ : LSub),
    (∀ b ls, vCE (some ρ) b (A.subst σ) ls δ = vCE (some (substEnv ρ σ δ)) b A ls δ) ∧
      (∀ α ls, shrE (some ρ) (A.subst σ) α ls δ = shrE (some (substEnv ρ σ δ)) A α ls δ) := by
  intro A
  induction A using VTy.recV with
  | unit => intro ρ σ δ; exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  | int w => intro ρ σ δ; exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  | opq k => intro ρ σ δ; exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  | tensor A B ihA ihB =>
      intro ρ σ δ
      refine ⟨fun b ls => ?_, fun α ls => ?_⟩
      · funext v; simp only [VTy.subst, vCE, (ihA ρ σ δ).1, (ihB ρ σ δ).1]
      · funext v; simp only [VTy.subst, shrE, (ihA ρ σ δ).2, (ihB ρ σ δ).2]
  | zero => intro ρ σ δ; exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  | sum A B ihA ihB =>
      intro ρ σ δ
      refine ⟨fun b ls => ?_, fun α ls => ?_⟩
      · funext v; simp only [VTy.subst, vCE, (ihA ρ σ δ).1, (ihB ρ σ δ).1]
      · funext v; simp only [VTy.subst, shrE, (ihA ρ σ δ).2, (ihB ρ σ δ).2]
  | thunk _ => intro ρ σ δ; exact ⟨fun b _ => by cases b <;> rfl, fun _ _ => rfl⟩
  | code _ _ _ _ => intro ρ σ δ; exact ⟨fun b _ => by cases b <;> rfl, fun _ _ => rfl⟩
  | ref A ih =>
      intro ρ σ δ
      refine ⟨fun b ls => ?_, fun α ls => ?_⟩
      · funext v; simp only [VTy.subst, vCE, (ih ρ σ δ).1]
      · funext v; simp only [VTy.subst, shrE, (ih ρ σ δ).1, (ih ρ σ δ).2]
  | fam L ih =>
      intro ρ σ δ
      refine ⟨fun b ls => ?_, fun α ls => ?_⟩
      · funext v; simp only [VTy.subst, vCE, (ih ρ σ δ).1]
      · funext v; simp only [VTy.subst, shrE, (ih ρ σ δ).2]
  | imm a A ih =>
      intro ρ σ δ
      refine ⟨fun b ls => ?_, fun _ _ => rfl⟩
      funext v
      have e : tClose (some ρ) (A.subst σ) = tClose (some (substEnv ρ σ δ)) A := by
        simp only [tClose, substEnv, VTy.subst_subst]
      simp only [VTy.subst, vCE, (ih ρ σ δ).1, (ih ρ σ δ).2, e]
  | «mut» a A ih =>
      intro ρ σ δ
      refine ⟨fun b ls => ?_, fun α ls => ?_⟩
      · funext v; simp only [VTy.subst, vCE, (ih ρ σ δ).1]
      · funext v; simp only [VTy.subst, shrE, (ih ρ σ δ).1, (ih ρ σ δ).2]
  | box a A ih =>
      intro ρ σ δ
      refine ⟨fun b ls => ?_, fun α ls => ?_⟩
      · funext v; simp only [VTy.subst, vCE, (ih ρ σ δ).1]
      · funext v; simp only [VTy.subst, shrE, (ih ρ σ δ).2]
  | bang A ih =>
      intro ρ σ δ
      refine ⟨fun b ls => ?_, fun _ _ => rfl⟩
      funext v; simp only [VTy.subst, vCE, (ih ρ σ δ).1]
  | unk => intro ρ σ δ; exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  | tvar n => intro ρ σ δ; exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  | mu A ih =>
      intro ρ σ δ
      have eM : tClose (some ρ) (.mu (A.subst (VTy.upS σ)))
          = tClose (some (substEnv ρ σ δ)) (.mu A) := by
        simp only [tClose, substEnv]
        rw [show VTy.mu (A.subst (VTy.upS σ)) = (VTy.mu A).subst σ from rfl, VTy.subst_subst]
      have eNM : (A.subst (VTy.upS σ)).NoMut 0 ↔ A.NoMut 0 := VTy.noMut_upS_iff A σ
      have eenv : ∀ P S, substEnv (VTy.scons ⟨tClose (some (substEnv ρ σ δ)) (.mu A), P, S⟩ ρ)
          (VTy.upS σ) δ = VTy.scons ⟨tClose (some (substEnv ρ σ δ)) (.mu A), P, S⟩
            (substEnv ρ σ δ) := by
        intro P S
        funext n
        cases n with
        | zero => rfl
        | succ n =>
            refine TEnt.ext' ?_ ?_ ?_
            · show (VTy.rename Nat.succ (σ n)).subst _ = _
              rw [VTy.subst_rename]; rfl
            · funext b ls
              show vCE _ b (VTy.rename Nat.succ (σ n)) ls δ = _
              rw [vCE_rename]; rfl
            · funext α ls
              show shrE _ (VTy.rename Nat.succ (σ n)) α ls δ = _
              rw [shrE_rename]; rfl
      have key : ∀ P S,
          ((∀ b' ls' v' ρ', vCE (some (VTy.scons ⟨tClose (some (substEnv ρ σ δ)) (.mu A), P, S⟩ ρ))
              b' (A.subst (VTy.upS σ)) ls' δ v' ρ' → P b' ls' v' ρ') ↔
            (∀ b' ls' v' ρ', vCE (some (VTy.scons ⟨tClose (some (substEnv ρ σ δ)) (.mu A), P, S⟩
              (substEnv ρ σ δ))) b' A ls' δ v' ρ' → P b' ls' v' ρ')) ∧
          ((∀ α' ls' v' ρ', shrE (some (VTy.scons ⟨tClose (some (substEnv ρ σ δ)) (.mu A), P, S⟩ ρ))
              (A.subst (VTy.upS σ)) α' ls' δ v' ρ' → S α' ls' v' ρ') ↔
            (∀ α' ls' v' ρ', shrE (some (VTy.scons ⟨tClose (some (substEnv ρ σ δ)) (.mu A), P, S⟩
              (substEnv ρ σ δ))) A α' ls' δ v' ρ' → S α' ls' v' ρ')) := by
        intro P S
        refine ⟨forall_congr' fun b' => forall_congr' fun ls' => ?_,
          forall_congr' fun α' => forall_congr' fun ls' => ?_⟩
        · rw [(ih _ (VTy.upS σ) δ).1 b' ls', eenv]
        · rw [(ih _ (VTy.upS σ) δ).2 α' ls', eenv]
      refine ⟨fun b ls => ?_, fun α ls => ?_⟩
      · funext v
        simp only [VTy.subst, vCE, eM, tEnv]
        funext r
        refine propext (and_congr eNM (and_congr Iff.rfl
          (forall_congr' fun P => forall_congr' fun S =>
            imp_congr (key P S).1 (imp_congr (key P S).2 Iff.rfl))))
      · funext v
        simp only [VTy.subst, shrE, eM, tEnv]
        funext r
        refine propext (and_congr eNM (and_congr Iff.rfl
          (forall_congr' fun P => forall_congr' fun S =>
            imp_congr (key P S).1 (imp_congr (key P S).2 Iff.rfl))))

theorem vCE_subst (A : VTy) (ρ : Nat → TEnt) (σ : Nat → VTy) (δ : LSub) (b : Bool)
    (ls : List SRec) : vCE (some ρ) b (A.subst σ) ls δ = vCE (some (substEnv ρ σ δ)) b A ls δ :=
  (vCE_shrE_subst A ρ σ δ).1 b ls

theorem shrE_subst (A : VTy) (ρ : Nat → TEnt) (σ : Nat → VTy) (δ : LSub) (α : Life)
    (ls : List SRec) : shrE (some ρ) (A.subst σ) α ls δ = shrE (some (substEnv ρ σ δ)) A α ls δ :=
  (vCE_shrE_subst A ρ σ δ).2 α ls

/-! ### Occurring variables and monotonicity -/

/-- The relation and the views read only the entries of the variables that occur. -/
theorem vCE_shrE_congr_occ : ∀ (A : VTy) (η₁ η₂ : Nat → TEnt), (∀ n, A.Occ n → η₁ n = η₂ n) →
    (∀ b, vCE (some η₁) b A = vCE (some η₂) b A) ∧ shrE (some η₁) A = shrE (some η₂) A := by
  intro A
  induction A using VTy.recV with
  | unit => intros; exact ⟨fun _ => rfl, rfl⟩
  | int w => intros; exact ⟨fun _ => rfl, rfl⟩
  | opq k => intros; exact ⟨fun _ => rfl, rfl⟩
  | tensor A B ihA ihB =>
      intro η₁ η₂ h
      have hA := ihA η₁ η₂ (fun n hn => h n (Or.inl hn))
      have hB := ihB η₁ η₂ (fun n hn => h n (Or.inr hn))
      refine ⟨fun b => ?_, ?_⟩
      · funext ls δ v; simp only [vCE, hA.1, hB.1]
      · funext α ls δ v; simp only [shrE, hA.2, hB.2]
  | zero => intros; exact ⟨fun _ => rfl, rfl⟩
  | sum A B ihA ihB =>
      intro η₁ η₂ h
      have hA := ihA η₁ η₂ (fun n hn => h n (Or.inl hn))
      have hB := ihB η₁ η₂ (fun n hn => h n (Or.inr hn))
      refine ⟨fun b => ?_, ?_⟩
      · funext ls δ v; simp only [vCE, hA.1, hB.1]
      · funext α ls δ v; simp only [shrE, hA.2, hB.2]
  | thunk _ => intros; exact ⟨fun b => by cases b <;> rfl, rfl⟩
  | code _ _ _ _ => intros; exact ⟨fun b => by cases b <;> rfl, rfl⟩
  | ref A ih =>
      intro η₁ η₂ h
      have hA := ih η₁ η₂ h
      refine ⟨fun b => ?_, ?_⟩
      · funext ls δ v; simp only [vCE, hA.1]
      · funext α ls δ v; simp only [shrE, hA.1, hA.2]
  | fam L ih =>
      intro η₁ η₂ h
      have hA := ih η₁ η₂ h
      refine ⟨fun b => ?_, ?_⟩
      · funext ls δ v; simp only [vCE, hA.1]
      · funext α ls δ v; simp only [shrE, hA.2]
  | imm a A ih =>
      intro η₁ η₂ h
      have hA := ih η₁ η₂ h
      refine ⟨fun b => ?_, rfl⟩
      funext ls δ v
      have e : tClose (some η₁) A = tClose (some η₂) A :=
        VTy.subst_congr_occ A (fun n hn => by rw [h n hn])
      simp only [vCE, hA.1, hA.2, e]
  | «mut» a A ih =>
      intro η₁ η₂ h
      have hA := ih η₁ η₂ h
      refine ⟨fun b => ?_, ?_⟩
      · funext ls δ v; simp only [vCE, hA.1]
      · funext α ls δ v; simp only [shrE, hA.1, hA.2]
  | box a A ih =>
      intro η₁ η₂ h
      have hA := ih η₁ η₂ h
      refine ⟨fun b => ?_, ?_⟩
      · funext ls δ v; simp only [vCE, hA.1]
      · funext α ls δ v; simp only [shrE, hA.2]
  | bang A ih =>
      intro η₁ η₂ h
      have hA := ih η₁ η₂ h
      refine ⟨fun b => ?_, rfl⟩
      funext ls δ v; simp only [vCE, hA.1]
  | unk => intros; exact ⟨fun _ => rfl, rfl⟩
  | tvar n =>
      intro η₁ η₂ h
      refine ⟨fun b => ?_, ?_⟩
      · funext ls δ v; simp only [vCE, tEnvP, h n rfl]
      · funext α ls δ v; simp only [shrE, tEnvS, h n rfl]
  | mu A ih =>
      intro η₁ η₂ h
      have e : tClose (some η₁) (.mu A) = tClose (some η₂) (.mu A) :=
        VTy.subst_congr_occ (.mu A) (fun n hn => by rw [h n hn])
      have hB : ∀ P S, (∀ b, vCE (some (VTy.scons ⟨tClose (some η₂) (.mu A), P, S⟩ η₁)) b A =
            vCE (some (VTy.scons ⟨tClose (some η₂) (.mu A), P, S⟩ η₂)) b A) ∧
          shrE (some (VTy.scons ⟨tClose (some η₂) (.mu A), P, S⟩ η₁)) A =
            shrE (some (VTy.scons ⟨tClose (some η₂) (.mu A), P, S⟩ η₂)) A := fun P S =>
        ih _ _ (fun n hn => by
          cases n with
          | zero => rfl
          | succ n => exact h n hn)
      refine ⟨fun b => ?_, ?_⟩
      · funext ls δ v
        simp only [vCE, e, tEnv]
        funext r
        refine propext (and_congr Iff.rfl (and_congr Iff.rfl
          (forall_congr' fun P => forall_congr' fun S => ?_)))
        simp only [(hB P S).1, (hB P S).2]
      · funext α ls δ v
        simp only [shrE, e, tEnv]
        funext r
        refine propext (and_congr Iff.rfl (and_congr Iff.rfl
          (forall_congr' fun P => forall_congr' fun S => ?_)))
        simp only [(hB P S).1, (hB P S).2]

theorem vCE_congr_occ (A : VTy) (η₁ η₂ : Nat → TEnt) (h : ∀ n, A.Occ n → η₁ n = η₂ n)
    (b : Bool) : vCE (some η₁) b A = vCE (some η₂) b A := (vCE_shrE_congr_occ A η₁ η₂ h).1 b

theorem shrE_congr_occ (A : VTy) (η₁ η₂ : Nat → TEnt) (h : ∀ n, A.Occ n → η₁ n = η₂ n) :
    shrE (some η₁) A = shrE (some η₂) A := (vCE_shrE_congr_occ A η₁ η₂ h).2

/-- **Monotonicity in the environment.**  The relation and the views grow with the candidates
of every variable, where a variable that occurs in a `Mut` payload keeps its entry. -/
theorem vCE_shrE_mono : ∀ (A : VTy) (η₁ η₂ : Nat → TEnt),
    (∀ n, (η₁ n).ty = (η₂ n).ty) → (∀ n, ¬ A.NoMut n → η₁ n = η₂ n) →
    (∀ n b ls v ρ, (η₁ n).P b ls v ρ → (η₂ n).P b ls v ρ) →
    (∀ n α ls v ρ, (η₁ n).S α ls v ρ → (η₂ n).S α ls v ρ) →
    (∀ b ls δ v ρ, vCE (some η₁) b A ls δ v ρ → vCE (some η₂) b A ls δ v ρ) ∧
      (∀ α ls δ v ρ, shrE (some η₁) A α ls δ v ρ → shrE (some η₂) A α ls δ v ρ) := by
  intro A
  induction A using VTy.recV with
  | unit => intros; exact ⟨fun _ _ _ _ _ h => h, fun _ _ _ _ _ h => h⟩
  | int w => intros; exact ⟨fun _ _ _ _ _ h => h, fun _ _ _ _ _ h => h⟩
  | opq k => intros; exact ⟨fun _ _ _ _ _ h => h, fun _ _ _ _ _ h => h⟩
  | tensor A B ihA ihB =>
      intro η₁ η₂ ht he hP hS
      have hA := ihA η₁ η₂ ht (fun n hn => he n (fun h => hn h.1)) hP hS
      have hB := ihB η₁ η₂ ht (fun n hn => he n (fun h => hn h.2)) hP hS
      refine ⟨fun b ls δ v ρ h => ?_, fun α ls δ v ρ h => ?_⟩
      · obtain ⟨v₁, v₂, ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', h₁, h₂⟩ := h
        exact ⟨v₁, v₂, ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', hA.1 b ls δ v₁ ρ₁ h₁, hB.1 b ls δ v₂ ρ₂ h₂⟩
      · obtain ⟨v₁, v₂, ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', h₁, h₂⟩ := h
        exact ⟨v₁, v₂, ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', hA.2 α ls δ v₁ ρ₁ h₁, hB.2 α ls δ v₂ ρ₂ h₂⟩
  | zero => intros; exact ⟨fun _ _ _ _ _ h => h, fun _ _ _ _ _ h => h⟩
  | sum A B ihA ihB =>
      intro η₁ η₂ ht he hP hS
      have hA := ihA η₁ η₂ ht (fun n hn => he n (fun h => hn h.1)) hP hS
      have hB := ihB η₁ η₂ ht (fun n hn => he n (fun h => hn h.2)) hP hS
      refine ⟨fun b ls δ v ρ h => ?_, fun α ls δ v ρ h => ?_⟩
      · rcases h with ⟨v₁, ρ₀, ρ₁, hc, hp, h₁⟩ | ⟨v₂, ρ₀, ρ₂, hc, hp, h₂⟩
        · exact Or.inl ⟨v₁, ρ₀, ρ₁, hc, hp, hA.1 b ls δ v₁ ρ₁ h₁⟩
        · exact Or.inr ⟨v₂, ρ₀, ρ₂, hc, hp, hB.1 b ls δ v₂ ρ₂ h₂⟩
      · rcases h with ⟨v₁, ρ₀, ρ₁, hc, hp, h₁⟩ | ⟨v₂, ρ₀, ρ₂, hc, hp, h₂⟩
        · exact Or.inl ⟨v₁, ρ₀, ρ₁, hc, hp, hA.2 α ls δ v₁ ρ₁ h₁⟩
        · exact Or.inr ⟨v₂, ρ₀, ρ₂, hc, hp, hB.2 α ls δ v₂ ρ₂ h₂⟩
  | thunk _ => intros; exact ⟨fun b _ _ _ _ h => by cases b <;> exact h, fun _ _ _ _ _ h => h⟩
  | code _ _ _ _ => intros; exact ⟨fun b _ _ _ _ h => by cases b <;> exact h, fun _ _ _ _ _ h => h⟩
  | ref A ih =>
      intro η₁ η₂ ht he hP hS
      have hA := ih η₁ η₂ ht he hP hS
      refine ⟨fun b ls δ v ρ h => ?_, fun α ls δ v ρ h => ?_⟩
      · obtain ⟨ℓ, v', ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', ho, h₂⟩ := h
        exact ⟨ℓ, v', ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', ho, hA.1 b ls δ v' ρ₂ h₂⟩
      · obtain ⟨ℓ, u, ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', hpto, h₂⟩ := h
        exact ⟨ℓ, u, ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc',
          ptoImmSv_mono (fun ls₀ u σ hu => hA.1 false ls₀ δ u σ hu) hpto, hA.2 α ls δ u ρ₂ h₂⟩
  | fam L ih =>
      intro η₁ η₂ ht he hP hS
      have hA := ih η₁ η₂ ht he hP hS
      refine ⟨fun b ls δ v ρ h => ?_, fun α ls δ v ρ h => ?_⟩
      · obtain ⟨ℓ, c, ρ₀, ρ₁, hc, hp, hs⟩ := h
        exact ⟨ℓ, c, ρ₀, ρ₁, hc, hp, sepRange_mono' (fun m σ hm => hA.1 b ls δ _ σ hm) hs⟩
      · obtain ⟨ℓ, c, ρ₀, ρ₁, hc, hp, hs⟩ := h
        exact ⟨ℓ, c, ρ₀, ρ₁, hc, hp, sepRange_mono' (fun m σ hm => hA.2 α ls δ _ σ hm) hs⟩
  | imm a A ih =>
      intro η₁ η₂ ht he hP hS
      have hA := ih η₁ η₂ ht he hP hS
      refine ⟨fun b ls δ v ρ h => ?_, fun _ _ _ _ _ h => h⟩
      have e : tClose (some η₁) A = tClose (some η₂) A := by
        simp only [tClose]; congr 1; funext n; exact ht n
      obtain ⟨α, hα, ℓ, u, ρ₀, ρ₁, hc, hp, ρ₂, ρ₃, hc', hpto, hsh⟩ := h
      rw [e] at hp
      exact ⟨α, hα, ℓ, u, ρ₀, ρ₁, hc, hp, ρ₂, ρ₃, hc',
        ptoImmSv_mono (fun ls₀ u σ hu => hA.1 false ls₀ δ u σ hu) hpto, hA.2 α ls δ u ρ₃ hsh⟩
  | «mut» a A _ =>
      intro η₁ η₂ _ he _ _
      have hc := vCE_shrE_congr_occ (.mut a A) η₁ η₂ (fun n hn => he n (fun h => h hn))
      refine ⟨fun b ls δ v ρ h => ?_, fun α ls δ v ρ h => ?_⟩
      · rw [hc.1] at h; exact h
      · rw [hc.2] at h; exact h
  | box a A ih =>
      intro η₁ η₂ ht he hP hS
      have hA := ih η₁ η₂ ht he hP hS
      refine ⟨fun b ls δ v ρ h => ?_, fun α ls δ v ρ h => hA.2 α ls δ v ρ h⟩
      obtain ⟨α, hα, hb, ho⟩ := h
      exact ⟨α, hα, hA.1 b ls δ v ρ hb, ho⟩
  | bang A ih =>
      intro η₁ η₂ ht he hP hS
      have hA := ih η₁ η₂ ht he hP hS
      exact ⟨fun b ls δ v ρ h => ⟨h.1, hA.1 true ls δ v ρ h.2⟩, fun _ _ _ _ _ h => h⟩
  | unk => intros; exact ⟨fun _ _ _ _ _ h => h, fun _ _ _ _ _ h => h⟩
  | tvar n =>
      intro η₁ η₂ _ _ hP hS
      exact ⟨fun b ls δ v ρ h => hP n b ls v ρ h, fun α ls δ v ρ h => hS n α ls v ρ h⟩
  | mu A ih =>
      intro η₁ η₂ ht he hP hS
      have eM : tClose (some η₁) (.mu A) = tClose (some η₂) (.mu A) := by
        simp only [tClose]; congr 1; funext n; exact ht n
      have hB : ∀ P S, _ := fun (P : Bool → List SRec → Val → WProp)
          (S : Life → List SRec → Val → WProp) =>
        ih (VTy.scons ⟨tClose (some η₁) (.mu A), P, S⟩ η₁)
          (VTy.scons ⟨tClose (some η₂) (.mu A), P, S⟩ η₂)
          (fun n => by cases n with
            | zero => exact eM
            | succ n => exact ht n)
          (fun n hn => by cases n with
            | zero => exact congrArg (fun t => TEnt.mk t P S) eM
            | succ n => exact he n hn)
          (fun n => by cases n with
            | zero => exact fun _ _ _ _ h => h
            | succ n => exact hP n)
          (fun n => by cases n with
            | zero => exact fun _ _ _ _ h => h
            | succ n => exact hS n)
      refine ⟨fun b ls δ v ρ h => ?_, fun α ls δ v ρ h => ?_⟩
      · obtain ⟨hnm, hcl, hlfp⟩ := h
        exact ⟨hnm, eM ▸ hcl, fun P S hPre hSre => hlfp P S
          (fun b' ls' v' ρ' h' => hPre b' ls' v' ρ' ((hB P S).1 b' ls' δ v' ρ' h'))
          (fun α' ls' v' ρ' h' => hSre α' ls' v' ρ' ((hB P S).2 α' ls' δ v' ρ' h'))⟩
      · obtain ⟨hnm, hcl, hlfp⟩ := h
        exact ⟨hnm, eM ▸ hcl, fun P S hPre hSre => hlfp P S
          (fun b' ls' v' ρ' h' => hPre b' ls' v' ρ' ((hB P S).1 b' ls' δ v' ρ' h'))
          (fun α' ls' v' ρ' h' => hSre α' ls' v' ρ' ((hB P S).2 α' ls' δ v' ρ' h'))⟩

/-- The relation is monotone in the entry of a variable that occurs in no `Mut` payload. -/
theorem vCE_mono_at (A : VTy) (k : Nat) (η₁ η₂ : Nat → TEnt) (hk : A.NoMut k)
    (ht : ∀ n, (η₁ n).ty = (η₂ n).ty) (hP : ∀ n, n ≠ k → (η₁ n).P = (η₂ n).P)
    (hS : ∀ n, n ≠ k → (η₁ n).S = (η₂ n).S)
    (hPk : ∀ b ls v ρ, (η₁ k).P b ls v ρ → (η₂ k).P b ls v ρ)
    (hSk : ∀ α ls v ρ, (η₁ k).S α ls v ρ → (η₂ k).S α ls v ρ) :
    (∀ b ls δ v ρ, vCE (some η₁) b A ls δ v ρ → vCE (some η₂) b A ls δ v ρ) ∧
      (∀ α ls δ v ρ, shrE (some η₁) A α ls δ v ρ → shrE (some η₂) A α ls δ v ρ) :=
  vCE_shrE_mono A η₁ η₂ ht
    (fun n hn => by
      have hnk : n ≠ k := by rintro rfl; exact hn hk
      exact TEnt.ext' (ht n) (hP n hnk) (hS n hnk))
    (fun n b ls v ρ h => by
      by_cases e : n = k
      · subst e; exact hPk b ls v ρ h
      · rw [← hP n e]; exact h)
    (fun n α ls v ρ h => by
      by_cases e : n = k
      · subst e; exact hSk α ls v ρ h
      · rw [← hS n e]; exact h)

/-! ### The unroll equation -/

/-- One unfolding of `μX. A` at the candidates `P` (the relation) and `S` (the views). -/
def cBody (A : VTy) (δ : LSub) (P : Bool → List SRec → Val → WProp)
    (S : Life → List SRec → Val → WProp) : Bool → List SRec → Val → WProp :=
  fun b ls => vCE (some (VTy.scons ⟨.mu A, P, S⟩ tNil)) b A ls δ

/-- The views component of one unfolding of `μX. A`. -/
def sBodyV (A : VTy) (δ : LSub) (P : Bool → List SRec → Val → WProp)
    (S : Life → List SRec → Val → WProp) : Life → List SRec → Val → WProp :=
  fun α ls => shrE (some (VTy.scons ⟨.mu A, P, S⟩ tNil)) A α ls δ

/-- The relation's candidate at `μX. A`. -/
abbrev muP (A : VTy) (δ : LSub) : Bool → List SRec → Val → WProp := fun b ls => vC b (.mu A) ls δ

/-- The views' candidate at `μX. A`. -/
abbrev muS (A : VTy) (δ : LSub) : Life → List SRec → Val → WProp :=
  fun α ls => shrE none (.mu A) α ls δ

theorem muEnv_eq (A : VTy) (δ : LSub) :
    substEnv tNil (VTy.scons (.mu A) .tvar) δ = VTy.scons ⟨.mu A, muP A δ, muS A δ⟩ tNil := by
  funext n
  cases n with
  | zero =>
      refine TEnt.ext' (VTy.subst_id _) ?_ ?_
      · funext b ls
        show vCE (some tNil) b (.mu A) ls δ = vCE none b (.mu A) ls δ
        rw [← vC_eq_some]
      · funext α ls
        show shrE (some tNil) (.mu A) α ls δ = shrE none (.mu A) α ls δ
        rw [← shr_eq_some]
  | succ n => rfl

/-- `A[μX. A/X]` is the body at `vC (μX. A)`. -/
theorem vC_inst (A : VTy) (δ : LSub) (b : Bool) (ls : List SRec) :
    vC b (VTy.inst (.mu A) A) ls δ = cBody A δ (muP A δ) (muS A δ) b ls := by
  show vCE none b (VTy.inst (.mu A) A) ls δ = _
  rw [vCE_some, VTy.inst, vCE_subst, show tEnv none = tNil from rfl, muEnv_eq]; rfl

/-- `A[μX. A/X]` is the body at `shrE (μX. A)`. -/
theorem shr_inst (A : VTy) (δ : LSub) (α : Life) (ls : List SRec) :
    shrE none (VTy.inst (.mu A) A) α ls δ = sBodyV A δ (muP A δ) (muS A δ) α ls := by
  rw [shrE_some, VTy.inst, shrE_subst, show tEnv none = tNil from rfl, muEnv_eq]; rfl

theorem body_mono (A : VTy) (δ : LSub) (hA : A.NoMut 0)
    {P Q : Bool → List SRec → Val → WProp} {S T : Life → List SRec → Val → WProp}
    (hPQ : ∀ b ls v ρ, P b ls v ρ → Q b ls v ρ) (hST : ∀ α ls v ρ, S α ls v ρ → T α ls v ρ) :
    (∀ b ls v ρ, cBody A δ P S b ls v ρ → cBody A δ Q T b ls v ρ) ∧
      (∀ α ls v ρ, sBodyV A δ P S α ls v ρ → sBodyV A δ Q T α ls v ρ) := by
  have h := vCE_mono_at A 0 (VTy.scons ⟨.mu A, P, S⟩ tNil) (VTy.scons ⟨.mu A, Q, T⟩ tNil) hA
    (fun n => by cases n <;> rfl)
    (fun n hn => by
      cases n with
      | zero => exact absurd rfl hn
      | succ n => rfl)
    (fun n hn => by
      cases n with
      | zero => exact absurd rfl hn
      | succ n => rfl) hPQ hST
  exact ⟨fun b ls v ρ => h.1 b ls δ v ρ, fun α ls v ρ => h.2 α ls δ v ρ⟩

theorem cBody_mono (A : VTy) (δ : LSub) (hA : A.NoMut 0)
    {P Q : Bool → List SRec → Val → WProp} {S T : Life → List SRec → Val → WProp}
    (hPQ : ∀ b ls v ρ, P b ls v ρ → Q b ls v ρ) (hST : ∀ α ls v ρ, S α ls v ρ → T α ls v ρ) :
    ∀ b ls v ρ, cBody A δ P S b ls v ρ → cBody A δ Q T b ls v ρ :=
  (body_mono A δ hA hPQ hST).1

/-- `roll`. -/
theorem vC_roll {A : VTy} {b : Bool} {ls : List SRec} {δ : LSub} {v : Val} {ρ : WRes}
    (hA : A.NoMut 0) (hc : (VTy.mu A).Cl 0) (h : vC b (VTy.inst (.mu A) A) ls δ v ρ) :
    vC b (.mu A) ls δ v ρ := by
  rw [vC_inst] at h
  exact ⟨hA, hc, fun P S hP hS => hP b ls v ρ
    ((body_mono A δ hA (fun b' ls' v' ρ' h' => h'.2.2 P S hP hS)
      (fun α' ls' v' ρ' h' => h'.2.2 P S hP hS)).1 b ls v ρ h)⟩

/-- `roll` at the views. -/
theorem shr_roll {A : VTy} {α : Life} {ls : List SRec} {δ : LSub} {v : Val} {ρ : WRes}
    (hA : A.NoMut 0) (hc : (VTy.mu A).Cl 0) (h : shrE none (VTy.inst (.mu A) A) α ls δ v ρ) :
    shrE none (.mu A) α ls δ v ρ := by
  rw [shr_inst] at h
  exact ⟨hA, hc, fun P S hP hS => hS α ls v ρ
    ((body_mono A δ hA (fun b' ls' v' ρ' h' => h'.2.2 P S hP hS)
      (fun α' ls' v' ρ' h' => h'.2.2 P S hP hS)).2 α ls v ρ h)⟩

/-- One unfolding is below the least fixed point, at both components. -/
theorem body_le_mu {A : VTy} {δ : LSub} (hA : A.NoMut 0) (hc : (VTy.mu A).Cl 0) :
    (∀ b ls v ρ, cBody A δ (muP A δ) (muS A δ) b ls v ρ → muP A δ b ls v ρ) ∧
      (∀ α ls v ρ, sBodyV A δ (muP A δ) (muS A δ) α ls v ρ → muS A δ α ls v ρ) :=
  ⟨fun b ls v ρ h => vC_roll hA hc (by rw [vC_inst]; exact h),
    fun α ls v ρ h => shr_roll hA hc (by rw [shr_inst]; exact h)⟩

/-- `unroll`. -/
theorem vC_unfold {A : VTy} {b : Bool} {ls : List SRec} {δ : LSub} {v : Val} {ρ : WRes}
    (h : vC b (.mu A) ls δ v ρ) :
    A.NoMut 0 ∧ (VTy.mu A).Cl 0 ∧ vC b (VTy.inst (.mu A) A) ls δ v ρ := by
  obtain ⟨hA, hc, hlfp⟩ := h
  refine ⟨hA, hc, ?_⟩
  rw [vC_inst]
  have hm := body_mono A δ hA (body_le_mu (δ := δ) hA hc).1 (body_le_mu (δ := δ) hA hc).2
  exact hlfp (cBody A δ (muP A δ) (muS A δ)) (sBodyV A δ (muP A δ) (muS A δ)) hm.1 hm.2

/-- `unroll` at the views. -/
theorem shr_unfold {A : VTy} {α : Life} {ls : List SRec} {δ : LSub} {v : Val} {ρ : WRes}
    (h : shrE none (.mu A) α ls δ v ρ) :
    A.NoMut 0 ∧ (VTy.mu A).Cl 0 ∧ shrE none (VTy.inst (.mu A) A) α ls δ v ρ := by
  obtain ⟨hA, hc, hlfp⟩ := h
  refine ⟨hA, hc, ?_⟩
  rw [shr_inst]
  have hm := body_mono A δ hA (body_le_mu (δ := δ) hA hc).1 (body_le_mu (δ := δ) hA hc).2
  exact hlfp (cBody A δ (muP A δ) (muS A δ)) (sBodyV A δ (muP A δ) (muS A δ)) hm.1 hm.2

/-- **The unroll equation.**  `[spec §6]` -/
theorem vC_mu_iff {A : VTy} {b : Bool} {ls : List SRec} {δ : LSub} {v : Val} {ρ : WRes} :
    vC b (.mu A) ls δ v ρ ↔
      A.NoMut 0 ∧ (VTy.mu A).Cl 0 ∧ vC b (VTy.inst (.mu A) A) ls δ v ρ :=
  ⟨vC_unfold, fun ⟨hA, hc, h⟩ => vC_roll hA hc h⟩

/-- **The unroll equation at the views.**  `[spec §6]` -/
theorem shr_mu_iff {A : VTy} {α : Life} {ls : List SRec} {δ : LSub} {v : Val} {ρ : WRes} :
    shrE none (.mu A) α ls δ v ρ ↔
      A.NoMut 0 ∧ (VTy.mu A).Cl 0 ∧ shrE none (VTy.inst (.mu A) A) α ls δ v ρ :=
  ⟨shr_unfold, fun ⟨hA, hc, h⟩ => shr_roll hA hc h⟩

/-! ### The induction principle -/

/-- One unfolding of the relation at every type, with `S` at the positions the clauses recurse
to: the `Mut` clause is kept, with `S` at its payload's type; the `Code⟨N; E⟩ C` clause is kept,
with `S` at every value of its environment type `E` (`[spec §68]`); at `μX. A` the unrolling
`A[μX. A/X]`. -/
def vF (S : Bool → VTy → List SRec → Val → WProp) (δ : LSub) :
    Bool → VTy → List SRec → Val → WProp
  | _, .unit, _, v => ⌜v = .unit⌝
  | _, .int w, _, v => ⌜v.IsInt w⌝
  | _, .opq k, _, v => k.rel v
  | b, .tensor A B, ls, v => ex fun v₁ => ex fun v₂ => ⌜v = .pair v₁ v₂⌝ ⋆ S b A ls v₁ ⋆ S b B ls v₂
  | _, .zero, _, _ => fun _ => False
  | b, .sum A B, ls, v =>
      BoLo.or (ex fun v₁ => ⌜v = .inj₁ v₁⌝ ⋆ S b A ls v₁) (ex fun v₂ => ⌜v = .inj₂ v₂⌝ ⋆ S b B ls v₂)
  | b, .thunk C, ls, v => vC b (.thunk C) ls δ v
  | b, .code N E C, ls, v => fun ρ => vC b (.code N E C) ls δ v ρ ∧
      ∀ ls' u σ, vC true E ls' δ u σ → S true E ls' u σ
  | _, .bang A, ls, v => fun ρ => ρ = PMap.empty ∧ S true A ls v ρ
  | b, .box a A, ls, v => atLife δ a fun α => box α (S b A ls v)
  | b, .ref A, ls, v => ex fun ℓ => ex fun v' => ⌜v = .loc ℓ⌝ ⋆ ptoOwn ℓ v' ⋆ S b A ls v'
  | b, .fam L, ls, v => ex fun ℓ => ex fun c => ⌜v = Val.arr ℓ c ∧ c.toNat < 2 ^ 31⌝ ⋆
      sepRange (fun m => S b L ls (.loc m)) ℓ c.toNat
  | _, .imm a A, ls, v => atLife δ a fun α => ex fun ℓ => ex fun u =>
      ⌜v = .loc ℓ ∧ CohE (rsOf ls) ℓ A δ⌝ ⋆
        ptoImmSv ℓ α ls u (fun ls₀ => S false A ls₀) ⋆ shrE none A α ls δ u
  | b, .mut a A, ls, v => fun ρ => vC b (.mut a A) ls δ v ρ ∧
      ∀ ls' u σ, vC true A ls' δ u σ → S true A ls' u σ
  | _, .unk, _, _ => emp
  | _, .tvar _, _, _ => fun _ => False
  | b, .mu A, ls, v => fun ρ => A.NoMut 0 ∧ (VTy.mu A).Cl 0 ∧ S b (VTy.inst (.mu A) A) ls v ρ

/-- `vC` is its own unfolding. -/
theorem vF_vC (δ : LSub) : ∀ (b : Bool) (T : VTy) (ls : List SRec) (v : Val) (ρ : WRes),
    vC b T ls δ v ρ ↔ vF (fun b T ls => vC b T ls δ) δ b T ls v ρ
  | _, .unit, _, _, _ => Iff.rfl
  | _, .int _, _, _, _ => Iff.rfl
  | _, .opq _, _, _, _ => Iff.rfl
  | _, .tensor _ _, _, _, _ => Iff.rfl
  | _, .sum _ _, _, _, _ => Iff.rfl
  | _, .zero, _, _, _ => Iff.rfl
  | _, .thunk _, _, _, _ => Iff.rfl
  | _, .code _ _ _, _, _, _ => ⟨fun h => ⟨h, fun _ _ _ h => h⟩, And.left⟩
  | _, .box _ _, _, _, _ => Iff.rfl
  | _, .ref _, _, _, _ => Iff.rfl
  | _, .fam _, _, _, _ => Iff.rfl
  | _, .bang _, _, _, _ => Iff.rfl
  | _, .imm _ _, _, _, _ => Iff.rfl
  | _, .mut _ _, _, _, _ => ⟨fun h => ⟨h, fun _ _ _ h => h⟩, And.left⟩
  | _, .unk, _, _, _ => Iff.rfl
  | _, .tvar _, _, _, _ => Iff.rfl
  | _, .mu _, _, _, _ => vC_mu_iff

theorem vF_mono {S₁ S₂ : Bool → VTy → List SRec → Val → WProp}
    (h : ∀ b T ls v ρ, S₁ b T ls v ρ → S₂ b T ls v ρ) (δ : LSub) :
    ∀ (b : Bool) (T : VTy) (ls : List SRec) (v : Val) (ρ : WRes),
      vF S₁ δ b T ls v ρ → vF S₂ δ b T ls v ρ
  | _, .unit, _, _, _, hs => hs
  | _, .int w, _, _, _, hs => hs
  | _, .opq k, _, _, _, hs => hs
  | b, .tensor T₁ T₂, ls, _, _, hs => by
      obtain ⟨v₁, v₂, ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', h₁, h₂⟩ := hs
      exact ⟨v₁, v₂, ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', h b T₁ ls v₁ ρ₁ h₁, h b T₂ ls v₂ ρ₂ h₂⟩
  | b, .sum T₁ T₂, ls, _, _, hs => by
      rcases hs with ⟨v₁, ρ₀, ρ₁, hc, hp, h₁⟩ | ⟨v₂, ρ₀, ρ₂, hc, hp, h₂⟩
      · exact Or.inl ⟨v₁, ρ₀, ρ₁, hc, hp, h b T₁ ls v₁ ρ₁ h₁⟩
      · exact Or.inr ⟨v₂, ρ₀, ρ₂, hc, hp, h b T₂ ls v₂ ρ₂ h₂⟩
  | _, .zero, _, _, _, hs => hs
  | _, .thunk _, _, _, _, hs => hs
  | _, .code _ E _, _, _, _, hs => ⟨hs.1, fun ls' u σ hu => h true E ls' u σ (hs.2 ls' u σ hu)⟩
  | b, .box _ T, ls, _, _, hs => by
      obtain ⟨α, hα, hb, ho⟩ := hs
      exact ⟨α, hα, h b T ls _ _ hb, ho⟩
  | b, .ref T, ls, _, _, hs => by
      obtain ⟨ℓ, v', ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', ho, h₂⟩ := hs
      exact ⟨ℓ, v', ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', ho, h b T ls v' ρ₂ h₂⟩
  | b, .fam L, ls, _, _, hs => by
      obtain ⟨ℓ, c, ρ₀, ρ₁, hc, hp, hs⟩ := hs
      exact ⟨ℓ, c, ρ₀, ρ₁, hc, hp, sepRange_mono' (fun m σ hm => h b L ls _ σ hm) hs⟩
  | _, .bang T, ls, _, _, hs => ⟨hs.1, h true T ls _ _ hs.2⟩
  | _, .imm _ T, _, _, _, hs => by
      obtain ⟨α, hα, ℓ, u, ρ₀, ρ₁, hc, hp, ρ₂, ρ₃, hc', hpto, hsh⟩ := hs
      exact ⟨α, hα, ℓ, u, ρ₀, ρ₁, hc, hp, ρ₂, ρ₃, hc',
        ptoImmSv_mono (fun ls₀ u σ hu => h false T ls₀ u σ hu) hpto, hsh⟩
  | _, .mut _ T, _, _, _, hs => ⟨hs.1, fun ls' u σ hu => h true T ls' u σ (hs.2 ls' u σ hu)⟩
  | _, .unk, _, _, _, hs => hs
  | _, .tvar _, _, _, _, hs => hs
  | b, .mu A, ls, v, ρ, hs => ⟨hs.1, hs.2.1, h b _ ls v ρ hs.2.2⟩

/-- Views under an environment whose candidates are below the relation and whose views
candidates are the views of the types it stands for are views of the substituted type. -/
theorem shrE_env_to_none {A : VTy} {η₀ : Nat → TEnt} {σ : Nat → VTy} {δ : LSub}
    (ht : ∀ n, (η₀ n).ty = σ n)
    (hP : ∀ n b ls v r, (η₀ n).P b ls v r → vC b (σ n) ls δ v r)
    (hex : ∀ n, ¬ A.NoMut n → (η₀ n).P = fun b ls => vC b (σ n) ls δ)
    (hS : ∀ n, (η₀ n).S = fun α ls => shrE none (σ n) α ls δ) :
    ∀ α ls v r, shrE (some η₀) A α ls δ v r → shrE none (A.subst σ) α ls δ v r := by
  intro α ls v r h
  have ht' : ∀ n, (η₀ n).ty = (substEnv tNil σ δ n).ty :=
    fun n => (ht n).trans (VTy.subst_id _).symm
  rw [shrE_some, show tEnv none = tNil from rfl, shrE_subst]
  refine (vCE_shrE_mono A η₀ (substEnv tNil σ δ) ht' (fun n hn => ?_) (fun n b ls v r h => ?_)
    (fun n α ls v r h => ?_)).2 α ls δ v r h
  · refine TEnt.ext' (ht' n) ?_ ?_
    · rw [hex n hn]; funext b ls
      show vC b (σ n) ls δ = vCE (some tNil) b (σ n) ls δ
      rw [vC_eq_some]
    · rw [hS n]; funext α ls
      show shrE none (σ n) α ls δ = shrE (some tNil) (σ n) α ls δ
      rw [shr_eq_some]
  · show vCE (some tNil) b (σ n) ls δ v r
    rw [← vC_eq_some]; exact hP n b ls v r h
  · rw [hS n] at h
    show shrE (some tNil) (σ n) α ls δ v r
    rw [← shr_eq_some]; exact h

/-- **Induction on the least fixed points, at every type, in both modes.**  A property of `vC`
closed under one unfolding of every clause — `vF` with the relation and the property at the
positions it recurses to, the unrolling at `μ` — holds of `vC`.  The environment type `E` of a
`Code⟨N; E⟩ C` is smaller than the type it occurs in, and a type substitution leaves it as it
is, so the property at `E` comes from an outer induction on the type's size. -/
theorem vC_ind (δ : LSub) (Φ : Bool → VTy → List SRec → Val → WRes → Prop)
    (h : ∀ b T ls v ρ, vF (fun b T ls v ρ => vC b T ls δ v ρ ∧ Φ b T ls v ρ) δ b T ls v ρ →
      Φ b T ls v ρ) :
    ∀ b T ls v ρ, vC b T ls δ v ρ → Φ b T ls v ρ := by
  let G : Bool → VTy → List SRec → Val → WProp := fun b T ls v ρ => vC b T ls δ v ρ ∧ Φ b T ls v ρ
  have hG : ∀ b T ls v ρ, vF G δ b T ls v ρ → G b T ls v ρ := fun b T ls v ρ hs =>
    ⟨(vF_vC δ b T ls v ρ).mpr (vF_mono (fun _ _ _ _ _ h => h.1) δ b T ls v ρ hs), h b T ls v ρ hs⟩
  suffices key : ∀ n (T : VTy), sizeOf T ≤ n → ∀ b ls v ρ, vC b T ls δ v ρ → G b T ls v ρ from
    fun b T ls v ρ hT => (key _ T le_rfl b ls v ρ hT).2
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
  have gen : ∀ (A : VTy), sizeOf A ≤ n → ∀ (η₀ : Nat → TEnt) (σ : Nat → VTy), (∀ n, (η₀ n).ty = σ n) →
      (∀ n b ls v r, (η₀ n).P b ls v r → G b (σ n) ls v r) →
      (∀ n, ¬ A.NoMut n → (η₀ n).P = fun b ls => vC b (σ n) ls δ) →
      (∀ n, (η₀ n).S = fun α ls => shrE none (σ n) α ls δ) →
      ∀ b ls v r, vCE (some η₀) b A ls δ v r → G b (A.subst σ) ls v r := by
    intro A
    induction A using VTy.recV with
    | unit => intro _ _ _ _ _ _ _ b ls v r hr; exact hG b _ ls v r hr
    | int w => intro _ _ _ _ _ _ _ b ls v r hr; exact hG b _ ls v r hr
    | opq k => intro _ _ _ _ _ _ _ b ls v r hr; exact hG b _ ls v r hr
    | tensor A B ihA ihB =>
        intro hsz η₀ σ ht hP hex hSd b ls v r hr
        obtain ⟨v₁, v₂, ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', h₁, h₂⟩ := hr
        exact hG b _ ls v r ⟨v₁, v₂, ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc',
          ihA (le_trans (by simp <;> omega) hsz) η₀ σ ht hP (fun n hn => hex n (fun h => hn h.1)) hSd b ls v₁ ρ₁ h₁,
          ihB (le_trans (by simp <;> omega) hsz) η₀ σ ht hP (fun n hn => hex n (fun h => hn h.2)) hSd b ls v₂ ρ₂ h₂⟩
    | zero => intro _ _ _ _ _ _ _ _ _ _ _ hr; exact hr.elim
    | sum A B ihA ihB =>
        intro hsz η₀ σ ht hP hex hSd b ls v r hr
        rcases hr with ⟨v₁, ρ₀, ρ₁, hc, hp, h₁⟩ | ⟨v₂, ρ₀, ρ₂, hc, hp, h₂⟩
        · exact hG b _ ls v r (Or.inl ⟨v₁, ρ₀, ρ₁, hc, hp,
            ihA (le_trans (by simp <;> omega) hsz) η₀ σ ht hP (fun n hn => hex n (fun h => hn h.1)) hSd b ls v₁ ρ₁ h₁⟩)
        · exact hG b _ ls v r (Or.inr ⟨v₂, ρ₀, ρ₂, hc, hp,
            ihB (le_trans (by simp <;> omega) hsz) η₀ σ ht hP (fun n hn => hex n (fun h => hn h.2)) hSd b ls v₂ ρ₂ h₂⟩)
    | thunk _ => intro _ _ _ _ _ _ _ b ls v r hr; cases b <;> exact hG _ _ ls v r hr
    | code N E C _ =>
        intro hsz _ _ _ _ _ _ b ls v r hr
        have hE : sizeOf E < n := lt_of_lt_of_le (by simp <;> omega) hsz
        refine hG b _ ls v r ⟨?_, fun ls' u σ' hu => ihn _ hE E le_rfl true ls' u σ' hu⟩
        cases b <;> exact hr
    | ref A ih =>
        intro hsz η₀ σ ht hP hex hSd b ls v r hr
        obtain ⟨ℓ, v', ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', ho, h₂⟩ := hr
        exact hG b _ ls v r ⟨ℓ, v', ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', ho,
          ih (le_trans (by simp <;> omega) hsz) η₀ σ ht hP hex hSd b ls v' ρ₂ h₂⟩
    | fam L ih =>
        intro hsz η₀ σ ht hP hex hSd b ls v r hr
        obtain ⟨ℓ, c, ρ₀, ρ₁, hc, hp, hs⟩ := hr
        exact hG b _ ls v r ⟨ℓ, c, ρ₀, ρ₁, hc, hp,
          sepRange_mono' (fun m σ' hm => ih (le_trans (by simp <;> omega) hsz) η₀ σ ht hP hex hSd b ls _ σ' hm) hs⟩
    | imm a A ih =>
        intro hsz η₀ σ ht hP hex hSd b ls v r hr
        have e : tClose (some η₀) A = A.subst σ := by
          simp only [tClose]; congr 1; funext n; exact ht n
        obtain ⟨α, hα, ℓ, u, ρ₀, ρ₁, hc, hp, ρ₂, ρ₃, hc', hpto, hsh⟩ := hr
        rw [e] at hp
        exact hG b _ ls v r ⟨α, hα, ℓ, u, ρ₀, ρ₁, hc, hp, ρ₂, ρ₃, hc',
          ptoImmSv_mono (fun ls₀ u σ' hu => ih (le_trans (by simp <;> omega) hsz) η₀ σ ht hP hex hSd false ls₀ u σ' hu) hpto,
          shrE_env_to_none (A := A) ht (fun n b ls v r h => (hP n b ls v r h).1) hex hSd α ls u ρ₃ hsh⟩
    | «mut» a A ih =>
        intro hsz η₀ σ ht hP hex hSd b ls v r hr
        have hmut : ∀ b' ls₀, vCE (some η₀) b' A ls₀ δ = vC b' (A.subst σ) ls₀ δ := by
          intro b' ls₀
          rw [vC_eq_some, vCE_subst]
          refine congrFun (congrFun (vCE_congr_occ A _ _ (fun n hn => ?_) b') ls₀) δ
          refine TEnt.ext' ((ht n).trans (VTy.subst_id _).symm) ?_ ?_
          · rw [hex n (fun h => h hn)]
            funext b'' ls''
            exact vC_eq_some b'' (σ n) ▸ rfl
          · rw [hSd n]
            funext α'' ls''
            exact shr_eq_some (σ n) ▸ rfl
        have hr' : vC b (.mut a (A.subst σ)) ls δ v r := by
          have e : (fun ls₀ => vCE (some η₀) true A ls₀ δ) = (fun ls₀ => vC true (A.subst σ) ls₀ δ) :=
            funext (hmut true)
          obtain ⟨α, hα, ℓ, ρ₀, ρ₁, hc, hp, hpto⟩ := hr
          refine ⟨α, hα, ℓ, ρ₀, ρ₁, hc, hp, ?_⟩
          rw [← e]; exact hpto
        refine hG b _ ls v r ⟨hr', fun ls' u σ' hu => ?_⟩
        rw [← hmut] at hu
        exact ih (le_trans (by simp <;> omega) hsz) η₀ σ ht hP (fun n hn => hex n (fun h => hn (VTy.noMut_of_not_occ A h))) hSd true ls' u σ' hu
    | box a A ih =>
        intro hsz η₀ σ ht hP hex hSd b ls v r hr
        obtain ⟨α, hα, hb, ho⟩ := hr
        exact hG b _ ls v r ⟨α, hα, ih (le_trans (by simp <;> omega) hsz) η₀ σ ht hP hex hSd b ls v r hb, ho⟩
    | bang A ih =>
        intro hsz η₀ σ ht hP hex hSd b ls v r hr
        exact hG b _ ls v r ⟨hr.1, ih (le_trans (by simp <;> omega) hsz) η₀ σ ht hP hex hSd true ls v r hr.2⟩
    | unk => intro _ _ _ _ _ _ _ b ls v r hr; exact hG b _ ls v r hr
    | tvar n => intro _ η₀ σ _ hP _ _ b ls v r hr; exact hP n b ls v r hr
    | mu B ih =>
        intro hsz η₀ σ ht hP hex hSd b ls v r hr
        obtain ⟨hnm, hcl, hlfp⟩ := hr
        have hM : tClose (some η₀) (.mu B) = (VTy.mu B).subst σ := by
          simp only [tClose]; congr 1; funext n; exact ht n
        rw [hM] at hcl hlfp
        refine hlfp (fun b ls v r => G b ((VTy.mu B).subst σ) ls v r)
          (fun α ls v r => shrE none ((VTy.mu B).subst σ) α ls δ v r) (fun b' ls' v' r' h' => ?_)
          (fun α' ls' v' r' h' => ?_)
        rotate_left
        · have hS := shrE_env_to_none (A := B) (η₀ := VTy.scons ⟨(VTy.mu B).subst σ,
              fun b ls v r => G b ((VTy.mu B).subst σ) ls v r,
              fun α ls v r => shrE none ((VTy.mu B).subst σ) α ls δ v r⟩ η₀)
            (σ := VTy.scons ((VTy.mu B).subst σ) σ)
            (fun n => by cases n with
              | zero => rfl
              | succ n => exact ht n)
            (fun n => by cases n with
              | zero => exact fun _ _ _ _ h => h.1
              | succ n => exact fun b ls v r h => (hP n b ls v r h).1)
            (fun n hn => by cases n with
              | zero => exact absurd hnm hn
              | succ n => exact hex n hn)
            (fun n => by cases n with
              | zero => rfl
              | succ n => exact hSd n) α' ls' v' r' h'
          rw [VTy.subst_scons_eq_inst] at hS
          exact shr_roll ((VTy.noMut_upS_iff B σ).mpr hnm) hcl hS
        have hB := ih (le_trans (by simp <;> omega) hsz) (VTy.scons ⟨(VTy.mu B).subst σ,
            fun b ls v r => G b ((VTy.mu B).subst σ) ls v r,
            fun α ls v r => shrE none ((VTy.mu B).subst σ) α ls δ v r⟩ η₀)
          (VTy.scons ((VTy.mu B).subst σ) σ)
          (fun n => by cases n with
            | zero => rfl
            | succ n => exact ht n)
          (fun n => by cases n with
            | zero => exact fun _ _ _ _ h => h
            | succ n => exact hP n)
          (fun n hn => by cases n with
            | zero => exact absurd hnm hn
            | succ n => exact hex n hn)
          (fun n => by cases n with
            | zero => rfl
            | succ n => exact hSd n) b' ls' v' r' h'
        rw [VTy.subst_scons_eq_inst] at hB
        exact hG _ _ _ _ _ ⟨(VTy.noMut_upS_iff B σ).mpr hnm, hcl, hB⟩
  intro T hT b ls v ρ hv
  rw [vC_eq_some] at hv
  have := gen T hT tNil .tvar (fun _ => rfl) (fun _ _ _ _ _ h => h.elim) (fun _ _ => rfl)
    (fun _ => rfl) b ls v ρ hv
  rw [VTy.subst_id] at this
  exact this

/-- `Imm̲` at a closed `μ` is read at the reborrow of the unrolling. -/
theorem vC_immReborrow_mu_iff {A : VTy} (hA : A.Cl 1) (c : Lifetime.Life) (b : Bool)
    (ls : List SRec) (δ : LSub) (v : Val) (ρ : WRes) :
    vC b ((VTy.mu A).immReborrow c) ls δ v ρ ↔
      vC b ((VTy.inst (.mu A) A).immReborrow c) ls δ v ρ := by
  rw [VTy.immReborrow_mu c hA, VTy.immReborrow_unroll' c hA, vC_mu_iff]
  exact ⟨fun h => h.2.2, fun h => ⟨VTy.noMut_immX c hA 0, VTy.Cl_immX c hA, h⟩⟩

/-- **Induction on the least fixed point at `μX. A`.**  A property closed under one unfolding
of the body, with the relation and the property at `X`, holds of `vC (μX. A)`. -/
theorem vC_mu_ind {A : VTy} {δ : LSub} (P : Bool → List SRec → Val → WProp)
    (h : ∀ b ls v ρ, A.NoMut 0 → (VTy.mu A).Cl 0 →
      cBody A δ (fun b ls v ρ => vC b (.mu A) ls δ v ρ ∧ P b ls v ρ) (muS A δ) b ls v ρ →
        P b ls v ρ) :
    ∀ b ls v ρ, vC b (.mu A) ls δ v ρ → P b ls v ρ := by
  intro b ls v ρ hv
  obtain ⟨hA, hc, hlfp⟩ := hv
  have hm := body_mono A δ hA (P := fun b ls v ρ => vC b (.mu A) ls δ v ρ ∧ P b ls v ρ)
    (Q := muP A δ) (S := muS A δ) (T := muS A δ) (fun _ _ _ _ h => h.1) (fun _ _ _ _ h => h)
  refine (hlfp (fun b ls v ρ => vC b (.mu A) ls δ v ρ ∧ P b ls v ρ) (muS A δ)
    (fun b' ls' v' ρ' h' => ⟨vC_roll hA hc ?_, h b' ls' v' ρ' hA hc h'⟩)
    (fun α' ls' v' ρ' h' => shr_roll hA hc ?_)).2
  · rw [vC_inst]; exact hm.1 b' ls' v' ρ' h'
  · rw [shr_inst]; exact hm.2 α' ls' v' ρ' h'

end BoCa.Fig16.LogRel.Core

end
