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

/-! ### The environment -/

theorem TEnt.ext' {a b : TEnt} (h₁ : a.ty = b.ty) (h₂ : a.P = b.P) : a = b := by
  cases a; cases b; simp only at h₁ h₂; subst h₁; subst h₂; rfl

theorem tEnvP_eq (η : Option (Nat → TEnt)) (n : Nat) (b : Bool) (ls : List SRec) (v : Val) :
    tEnvP η n b ls v = (tEnv η n).P b ls v := by
  cases η <;> rfl

theorem tClose_eq (η : Option (Nat → TEnt)) (A : VTy) :
    tClose η A = A.subst (fun n => (tEnv η n).ty) := by
  cases η with
  | none => exact (VTy.subst_id A).symm
  | some η => rfl

/-- The relation reads its environment only through `tEnv`. -/
theorem vCE_some (η : Option (Nat → TEnt)) :
    ∀ (A : VTy) (b : Bool), vCE η b A = vCE (some (tEnv η)) b A := by
  intro A
  induction A using VTy.recV with
  | unit => intro b; rfl
  | tensor A B ihA ihB => intro b; funext ls δ v; simp only [vCE, ihA, ihB]
  | zero => intro b; rfl
  | sum A B ihA ihB => intro b; funext ls δ v; simp only [vCE, ihA, ihB]
  | thunk _ => intro b; cases b <;> rfl
  | ref A ih => intro b; funext ls δ v; simp only [vCE, ih]
  | imm a A ih =>
      intro b; funext ls δ v
      have e : tClose η A = tClose (some (tEnv η)) A := by rw [tClose_eq]; rfl
      simp only [vCE, ih, e]
  | «mut» a A ih => intro b; funext ls δ v; simp only [vCE, ih]
  | box a A ih => intro b; funext ls δ v; simp only [vCE, ih]
  | bang A ih => intro b; funext ls δ v; simp only [vCE, ih]
  | unk => intro b; rfl
  | tvar n => intro b; funext ls δ v; simp only [vCE, tEnvP_eq]; rfl
  | mu A _ =>
      intro b; funext ls δ v
      have e : tClose η (.mu A) = tClose (some (tEnv η)) (.mu A) := by rw [tClose_eq]; rfl
      simp only [vCE, e]
      rfl

/-- The environment of a closed type. -/
abbrev tNil : Nat → TEnt := tEnv none

theorem vC_eq_some (b : Bool) (A : VTy) : vC b A = vCE (some tNil) b A := vCE_some none A b

/-! ### Renaming and substitution -/

theorem vCE_rename : ∀ (A : VTy) (ρ : Nat → TEnt) (r : Nat → Nat) (b : Bool),
    vCE (some ρ) b (A.rename r) = vCE (some (ρ ∘ r)) b A := by
  intro A
  induction A using VTy.recV with
  | unit => intro ρ r b; rfl
  | tensor A B ihA ihB => intro ρ r b; funext ls δ v; simp only [VTy.rename, vCE, ihA, ihB]
  | zero => intro ρ r b; rfl
  | sum A B ihA ihB => intro ρ r b; funext ls δ v; simp only [VTy.rename, vCE, ihA, ihB]
  | thunk _ => intro ρ r b; cases b <;> rfl
  | ref A ih => intro ρ r b; funext ls δ v; simp only [VTy.rename, vCE, ih]
  | imm a A ih =>
      intro ρ r b; funext ls δ v
      have e : tClose (some ρ) (A.rename r) = tClose (some (ρ ∘ r)) A := by
        simp only [tClose, VTy.subst_rename]; rfl
      simp only [VTy.rename, vCE, ih, e]
  | «mut» a A ih => intro ρ r b; funext ls δ v; simp only [VTy.rename, vCE, ih]
  | box a A ih => intro ρ r b; funext ls δ v; simp only [VTy.rename, vCE, ih]
  | bang A ih => intro ρ r b; funext ls δ v; simp only [VTy.rename, vCE, ih]
  | unk => intro ρ r b; rfl
  | tvar n => intro ρ r b; rfl
  | mu A ih =>
      intro ρ r b
      funext ls δ v
      have e' : tClose (some ρ) (.mu (A.rename (VTy.upR r))) = tClose (some (ρ ∘ r)) (.mu A) := by
        simp only [tClose]
        rw [show VTy.mu (A.rename (VTy.upR r)) = (VTy.mu A).rename r from rfl, VTy.subst_rename]
        rfl
      simp only [VTy.rename, vCE, e', tEnv, ih, scons_comp_upR, VTy.noMut_rename_upR_iff]

/-- The environment a substitution moves into. -/
def substEnv (ρ : Nat → TEnt) (σ : Nat → VTy) (δ : LSub) : Nat → TEnt :=
  fun n => ⟨(σ n).subst (fun k => (ρ k).ty), fun b ls => vCE (some ρ) b (σ n) ls δ⟩

theorem vCE_subst : ∀ (A : VTy) (ρ : Nat → TEnt) (σ : Nat → VTy) (δ : LSub) (b : Bool)
    (ls : List SRec), vCE (some ρ) b (A.subst σ) ls δ = vCE (some (substEnv ρ σ δ)) b A ls δ := by
  intro A
  induction A using VTy.recV with
  | unit => intro ρ σ δ b ls; rfl
  | tensor A B ihA ihB => intro ρ σ δ b ls; funext v; simp only [VTy.subst, vCE, ihA, ihB]
  | zero => intro ρ σ δ b ls; rfl
  | sum A B ihA ihB => intro ρ σ δ b ls; funext v; simp only [VTy.subst, vCE, ihA, ihB]
  | thunk _ => intro ρ σ δ b ls; cases b <;> rfl
  | ref A ih => intro ρ σ δ b ls; funext v; simp only [VTy.subst, vCE, ih]
  | imm a A ih =>
      intro ρ σ δ b ls; funext v
      have e : tClose (some ρ) (A.subst σ) = tClose (some (substEnv ρ σ δ)) A := by
        simp only [tClose, substEnv, VTy.subst_subst]
      simp only [VTy.subst, vCE, ih, e]
  | «mut» a A ih => intro ρ σ δ b ls; funext v; simp only [VTy.subst, vCE, ih]
  | box a A ih => intro ρ σ δ b ls; funext v; simp only [VTy.subst, vCE, ih]
  | bang A ih => intro ρ σ δ b ls; funext v; simp only [VTy.subst, vCE, ih]
  | unk => intro ρ σ δ b ls; rfl
  | tvar n => intro ρ σ δ b ls; rfl
  | mu A ih =>
      intro ρ σ δ b ls
      funext v
      have eM : tClose (some ρ) (.mu (A.subst (VTy.upS σ)))
          = tClose (some (substEnv ρ σ δ)) (.mu A) := by
        simp only [tClose, substEnv]
        rw [show VTy.mu (A.subst (VTy.upS σ)) = (VTy.mu A).subst σ from rfl, VTy.subst_subst]
      have eNM : (A.subst (VTy.upS σ)).NoMut 0 ↔ A.NoMut 0 := VTy.noMut_upS_iff A σ
      simp only [VTy.subst, vCE, eM, tEnv]
      funext r
      congr 1
      · exact propext eNM
      congr 1
      apply propext
      refine forall_congr' fun P => imp_congr ?_ Iff.rfl
      refine forall_congr' fun b' => forall_congr' fun ls' => forall_congr' fun v' =>
        forall_congr' fun r' => imp_congr ?_ Iff.rfl
      rw [ih]
      have eenv : substEnv (VTy.scons ⟨tClose (some (substEnv ρ σ δ)) (.mu A), P⟩ ρ)
          (VTy.upS σ) δ = VTy.scons ⟨tClose (some (substEnv ρ σ δ)) (.mu A), P⟩ (substEnv ρ σ δ) := by
        funext n
        cases n with
        | zero => rfl
        | succ n =>
            refine TEnt.ext' ?_ ?_
            · show (VTy.rename Nat.succ (σ n)).subst _ = _
              rw [VTy.subst_rename]; rfl
            · funext b ls
              show vCE _ b (VTy.rename Nat.succ (σ n)) ls δ = _
              rw [vCE_rename]; rfl
      rw [eenv]

/-! ### Occurring variables and monotonicity -/

/-- The relation reads only the entries of the variables that occur. -/
theorem vCE_congr_occ : ∀ (A : VTy) (η₁ η₂ : Nat → TEnt), (∀ n, A.Occ n → η₁ n = η₂ n) →
    ∀ b, vCE (some η₁) b A = vCE (some η₂) b A := by
  intro A
  induction A using VTy.recV with
  | unit => intros; rfl
  | tensor A B ihA ihB =>
      intro η₁ η₂ h b; funext ls δ v
      simp only [vCE, ihA η₁ η₂ (fun n hn => h n (Or.inl hn)),
        ihB η₁ η₂ (fun n hn => h n (Or.inr hn))]
  | zero => intros; rfl
  | sum A B ihA ihB =>
      intro η₁ η₂ h b; funext ls δ v
      simp only [vCE, ihA η₁ η₂ (fun n hn => h n (Or.inl hn)),
        ihB η₁ η₂ (fun n hn => h n (Or.inr hn))]
  | thunk _ => intro _ _ _ b; cases b <;> rfl
  | ref A ih => intro η₁ η₂ h b; funext ls δ v; simp only [vCE, ih η₁ η₂ h]
  | imm a A ih =>
      intro η₁ η₂ h b; funext ls δ v
      have e : tClose (some η₁) A = tClose (some η₂) A :=
        VTy.subst_congr_occ A (fun n hn => by rw [h n hn])
      simp only [vCE, ih η₁ η₂ h, e]
  | «mut» a A ih => intro η₁ η₂ h b; funext ls δ v; simp only [vCE, ih η₁ η₂ h]
  | box a A ih => intro η₁ η₂ h b; funext ls δ v; simp only [vCE, ih η₁ η₂ h]
  | bang A ih => intro η₁ η₂ h b; funext ls δ v; simp only [vCE, ih η₁ η₂ h]
  | unk => intros; rfl
  | tvar n => intro η₁ η₂ h b; funext ls δ v; simp only [vCE, tEnvP, h n rfl]
  | mu A ih =>
      intro η₁ η₂ h b; funext ls δ v
      have e : tClose (some η₁) (.mu A) = tClose (some η₂) (.mu A) :=
        VTy.subst_congr_occ (.mu A) (fun n hn => by rw [h n hn])
      simp only [vCE, e, tEnv]
      funext r
      congr 2
      apply propext
      refine forall_congr' fun P => imp_congr ?_ Iff.rfl
      have := ih (VTy.scons ⟨tClose (some η₂) (.mu A), P⟩ η₁)
        (VTy.scons ⟨tClose (some η₂) (.mu A), P⟩ η₂) (fun n hn => by
          cases n with
          | zero => rfl
          | succ n => exact h n hn)
      simp only [this]

/-- The relation is monotone in the entry of a variable that occurs in no `Mut` payload. -/
theorem vCE_mono_at : ∀ (A : VTy) (k : Nat) (η₁ η₂ : Nat → TEnt), A.NoMut k →
    (∀ n, (η₁ n).ty = (η₂ n).ty) → (∀ n, n ≠ k → (η₁ n).P = (η₂ n).P) →
    (∀ b ls v ρ, (η₁ k).P b ls v ρ → (η₂ k).P b ls v ρ) →
    ∀ b ls δ v ρ, vCE (some η₁) b A ls δ v ρ → vCE (some η₂) b A ls δ v ρ := by
  intro A
  induction A using VTy.recV with
  | unit => intro _ _ _ _ _ _ _ _ _ _ _ _ h; exact h
  | tensor A B ihA ihB =>
      intro k η₁ η₂ hk ht hP hPk b ls δ v ρ h
      obtain ⟨v₁, v₂, ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', h₁, h₂⟩ := h
      exact ⟨v₁, v₂, ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', ihA k η₁ η₂ hk.1 ht hP hPk b ls δ v₁ ρ₁ h₁,
        ihB k η₁ η₂ hk.2 ht hP hPk b ls δ v₂ ρ₂ h₂⟩
  | zero => intro _ _ _ _ _ _ _ _ _ _ _ _ h; exact h
  | sum A B ihA ihB =>
      intro k η₁ η₂ hk ht hP hPk b ls δ v ρ h
      rcases h with ⟨v₁, ρ₀, ρ₁, hc, hp, h₁⟩ | ⟨v₂, ρ₀, ρ₂, hc, hp, h₂⟩
      · exact Or.inl ⟨v₁, ρ₀, ρ₁, hc, hp, ihA k η₁ η₂ hk.1 ht hP hPk b ls δ v₁ ρ₁ h₁⟩
      · exact Or.inr ⟨v₂, ρ₀, ρ₂, hc, hp, ihB k η₁ η₂ hk.2 ht hP hPk b ls δ v₂ ρ₂ h₂⟩
  | thunk _ => intro _ _ _ _ _ _ _ b _ _ _ _ h; cases b <;> exact h
  | ref A ih =>
      intro k η₁ η₂ hk ht hP hPk b ls δ v ρ h
      obtain ⟨ℓ, v', ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', ho, h₂⟩ := h
      exact ⟨ℓ, v', ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', ho, ih k η₁ η₂ hk ht hP hPk b ls δ v' ρ₂ h₂⟩
  | imm a A ih =>
      intro k η₁ η₂ hk ht hP hPk b ls δ v ρ h
      have e : tClose (some η₁) A = tClose (some η₂) A := by
        simp only [tClose]; congr 1; funext n; exact ht n
      obtain ⟨α, hα, ℓ, ρ₀, ρ₁, hc, hp, hpto⟩ := h
      rw [e] at hp
      exact ⟨α, hα, ℓ, ρ₀, ρ₁, hc, hp,
        ptoImmS_mono (fun ls₀ u σ hu => ih k η₁ η₂ hk ht hP hPk false ls₀ δ u σ hu) hpto⟩
  | «mut» a A _ =>
      intro k η₁ η₂ hk ht hP _ b ls δ v ρ h
      rw [vCE_congr_occ (.mut a A) η₁ η₂ (fun n hn => by
        refine TEnt.ext' (ht n) (hP n ?_)
        rintro rfl; exact hk hn)] at h
      exact h
  | box a A ih =>
      intro k η₁ η₂ hk ht hP hPk b ls δ v ρ h
      obtain ⟨α, hα, hb, ho⟩ := h
      exact ⟨α, hα, ih k η₁ η₂ hk ht hP hPk b ls δ v ρ hb, ho⟩
  | bang A ih =>
      intro k η₁ η₂ hk ht hP hPk b ls δ v ρ h
      exact ⟨h.1, ih k η₁ η₂ hk ht hP hPk true ls δ v ρ h.2⟩
  | unk => intro _ _ _ _ _ _ _ _ _ _ _ _ h; exact h
  | tvar n =>
      intro k η₁ η₂ _ _ hP hPk b ls δ v ρ h
      by_cases e : n = k
      · subst e; exact hPk b ls v ρ h
      · show (η₂ n).P b ls v ρ
        rw [← hP n e]; exact h
  | mu A ih =>
      intro k η₁ η₂ hk ht hP hPk b ls δ v ρ h
      have eM : tClose (some η₁) (.mu A) = tClose (some η₂) (.mu A) := by
        simp only [tClose]; congr 1; funext n; exact ht n
      obtain ⟨hnm, hcl, hlfp⟩ := h
      refine ⟨hnm, eM ▸ hcl, fun P hPre => hlfp P (fun b' ls' v' ρ' h' => hPre b' ls' v' ρ' ?_)⟩
      refine ih (k + 1) _ _ hk (fun n => ?_) (fun n hn => ?_) ?_ b' ls' δ v' ρ' h'
      · cases n with
        | zero => exact eM
        | succ n => exact ht n
      · cases n with
        | zero => rfl
        | succ n => exact hP n (fun e => hn (by rw [e]))
      · exact hPk

/-! ### The unroll equation -/

/-- One unfolding of `μX. A` at the candidate `P`. -/
def cBody (A : VTy) (δ : LSub) (P : Bool → List SRec → Val → WProp) :
    Bool → List SRec → Val → WProp :=
  fun b ls => vCE (some (VTy.scons ⟨.mu A, P⟩ tNil)) b A ls δ

/-- `A[μX. A/X]` is the body at `vC (μX. A)`. -/
theorem vC_inst (A : VTy) (δ : LSub) (b : Bool) (ls : List SRec) :
    vC b (VTy.inst (.mu A) A) ls δ = cBody A δ (fun b ls => vC b (.mu A) ls δ) b ls := by
  rw [vC_eq_some, VTy.inst, vCE_subst, cBody]
  congr 2
  funext n
  cases n with
  | zero =>
      refine TEnt.ext' (VTy.subst_id _) ?_
      funext b ls
      show vCE (some tNil) b (.mu A) ls δ = vCE none b (.mu A) ls δ
      rw [← vC_eq_some]
  | succ n => rfl

theorem cBody_mono (A : VTy) (δ : LSub) (hA : A.NoMut 0) {P Q : Bool → List SRec → Val → WProp}
    (h : ∀ b ls v ρ, P b ls v ρ → Q b ls v ρ) :
    ∀ b ls v ρ, cBody A δ P b ls v ρ → cBody A δ Q b ls v ρ :=
  fun b ls v ρ => vCE_mono_at A 0 _ _ hA (fun n => by cases n <;> rfl)
    (fun n hn => by
      cases n with
      | zero => exact absurd rfl hn
      | succ n => rfl) h b ls δ v ρ

/-- `roll`. -/
theorem vC_roll {A : VTy} {b : Bool} {ls : List SRec} {δ : LSub} {v : Val} {ρ : WRes}
    (hA : A.NoMut 0) (hc : (VTy.mu A).Cl 0) (h : vC b (VTy.inst (.mu A) A) ls δ v ρ) :
    vC b (.mu A) ls δ v ρ := by
  rw [vC_inst] at h
  exact ⟨hA, hc, fun P hP => hP b ls v ρ
    (cBody_mono A δ hA (fun b' ls' v' ρ' h' => h'.2.2 P hP) b ls v ρ h)⟩

/-- `unroll`. -/
theorem vC_unfold {A : VTy} {b : Bool} {ls : List SRec} {δ : LSub} {v : Val} {ρ : WRes}
    (h : vC b (.mu A) ls δ v ρ) :
    A.NoMut 0 ∧ (VTy.mu A).Cl 0 ∧ vC b (VTy.inst (.mu A) A) ls δ v ρ := by
  obtain ⟨hA, hc, hlfp⟩ := h
  refine ⟨hA, hc, ?_⟩
  rw [vC_inst]
  exact hlfp (cBody A δ (fun b ls => vC b (.mu A) ls δ)) (fun b' ls' v' ρ' h' =>
    cBody_mono A δ hA (fun b'' ls'' v'' ρ'' h'' => vC_roll hA hc (by rw [vC_inst]; exact h''))
      b' ls' v' ρ' h')

/-- **The unroll equation.**  `[spec §6]` -/
theorem vC_mu_iff {A : VTy} {b : Bool} {ls : List SRec} {δ : LSub} {v : Val} {ρ : WRes} :
    vC b (.mu A) ls δ v ρ ↔
      A.NoMut 0 ∧ (VTy.mu A).Cl 0 ∧ vC b (VTy.inst (.mu A) A) ls δ v ρ :=
  ⟨vC_unfold, fun ⟨hA, hc, h⟩ => vC_roll hA hc h⟩

/-! ### The induction principle -/

/-- One unfolding of the relation at every type, with `S` at the positions the clauses recurse
to: the `Mut` clause is kept, with `S` at its payload's type; at `μX. A` the unrolling
`A[μX. A/X]`. -/
def vF (S : Bool → VTy → List SRec → Val → WProp) (δ : LSub) :
    Bool → VTy → List SRec → Val → WProp
  | _, .unit, _, v => ⌜v = .unit⌝
  | b, .tensor A B, ls, v => ex fun v₁ => ex fun v₂ => ⌜v = .pair v₁ v₂⌝ ⋆ S b A ls v₁ ⋆ S b B ls v₂
  | _, .zero, _, _ => fun _ => False
  | b, .sum A B, ls, v =>
      BoLo.or (ex fun v₁ => ⌜v = .inj₁ v₁⌝ ⋆ S b A ls v₁) (ex fun v₂ => ⌜v = .inj₂ v₂⌝ ⋆ S b B ls v₂)
  | b, .thunk C, ls, v => vC b (.thunk C) ls δ v
  | _, .bang A, ls, v => fun ρ => ρ = PMap.empty ∧ S true A ls v ρ
  | b, .box a A, ls, v => atLife δ a fun α => box α (S b A ls v)
  | b, .ref A, ls, v => ex fun ℓ => ex fun v' => ⌜v = .loc ℓ⌝ ⋆ ptoOwn ℓ v' ⋆ S b A ls v'
  | _, .imm a A, ls, v => atLife δ a fun α => ex fun ℓ => ⌜v = .loc ℓ ∧ CohE (rsOf ls) ℓ A δ⌝ ⋆
      ptoImmS ℓ α ls (fun ls₀ => S false A ls₀)
  | b, .mut a A, ls, v => fun ρ => vC b (.mut a A) ls δ v ρ ∧
      ∀ ls' u σ, vC true A ls' δ u σ → S true A ls' u σ
  | _, .unk, _, _ => emp
  | _, .tvar _, _, _ => fun _ => False
  | b, .mu A, ls, v => fun ρ => A.NoMut 0 ∧ (VTy.mu A).Cl 0 ∧ S b (VTy.inst (.mu A) A) ls v ρ

/-- `vC` is its own unfolding. -/
theorem vF_vC (δ : LSub) : ∀ (b : Bool) (T : VTy) (ls : List SRec) (v : Val) (ρ : WRes),
    vC b T ls δ v ρ ↔ vF (fun b T ls => vC b T ls δ) δ b T ls v ρ
  | _, .unit, _, _, _ => Iff.rfl
  | _, .tensor _ _, _, _, _ => Iff.rfl
  | _, .sum _ _, _, _, _ => Iff.rfl
  | _, .zero, _, _, _ => Iff.rfl
  | _, .thunk _, _, _, _ => Iff.rfl
  | _, .box _ _, _, _, _ => Iff.rfl
  | _, .ref _, _, _, _ => Iff.rfl
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
  | b, .tensor T₁ T₂, ls, _, _, hs => by
      obtain ⟨v₁, v₂, ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', h₁, h₂⟩ := hs
      exact ⟨v₁, v₂, ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', h b T₁ ls v₁ ρ₁ h₁, h b T₂ ls v₂ ρ₂ h₂⟩
  | b, .sum T₁ T₂, ls, _, _, hs => by
      rcases hs with ⟨v₁, ρ₀, ρ₁, hc, hp, h₁⟩ | ⟨v₂, ρ₀, ρ₂, hc, hp, h₂⟩
      · exact Or.inl ⟨v₁, ρ₀, ρ₁, hc, hp, h b T₁ ls v₁ ρ₁ h₁⟩
      · exact Or.inr ⟨v₂, ρ₀, ρ₂, hc, hp, h b T₂ ls v₂ ρ₂ h₂⟩
  | _, .zero, _, _, _, hs => hs
  | _, .thunk _, _, _, _, hs => hs
  | b, .box _ T, ls, _, _, hs => by
      obtain ⟨α, hα, hb, ho⟩ := hs
      exact ⟨α, hα, h b T ls _ _ hb, ho⟩
  | b, .ref T, ls, _, _, hs => by
      obtain ⟨ℓ, v', ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', ho, h₂⟩ := hs
      exact ⟨ℓ, v', ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', ho, h b T ls v' ρ₂ h₂⟩
  | _, .bang T, ls, _, _, hs => ⟨hs.1, h true T ls _ _ hs.2⟩
  | _, .imm _ T, _, _, _, hs => by
      obtain ⟨α, hα, ℓ, ρ₀, ρ₁, hc, hp, hpto⟩ := hs
      exact ⟨α, hα, ℓ, ρ₀, ρ₁, hc, hp, ptoImmS_mono (fun ls₀ u σ hu => h false T ls₀ u σ hu) hpto⟩
  | _, .mut _ T, _, _, _, hs => ⟨hs.1, fun ls' u σ hu => h true T ls' u σ (hs.2 ls' u σ hu)⟩
  | _, .unk, _, _, _, hs => hs
  | _, .tvar _, _, _, _, hs => hs
  | b, .mu A, ls, v, ρ, hs => ⟨hs.1, hs.2.1, h b _ ls v ρ hs.2.2⟩

/-- **Induction on the least fixed points, at every type, in both modes.**  A property of `vC`
closed under one unfolding of every clause — `vF` with the relation and the property at the
positions it recurses to, the unrolling at `μ` — holds of `vC`. -/
theorem vC_ind (δ : LSub) (Φ : Bool → VTy → List SRec → Val → WRes → Prop)
    (h : ∀ b T ls v ρ, vF (fun b T ls v ρ => vC b T ls δ v ρ ∧ Φ b T ls v ρ) δ b T ls v ρ →
      Φ b T ls v ρ) :
    ∀ b T ls v ρ, vC b T ls δ v ρ → Φ b T ls v ρ := by
  let G : Bool → VTy → List SRec → Val → WProp := fun b T ls v ρ => vC b T ls δ v ρ ∧ Φ b T ls v ρ
  have hG : ∀ b T ls v ρ, vF G δ b T ls v ρ → G b T ls v ρ := fun b T ls v ρ hs =>
    ⟨(vF_vC δ b T ls v ρ).mpr (vF_mono (fun _ _ _ _ _ h => h.1) δ b T ls v ρ hs), h b T ls v ρ hs⟩
  have gen : ∀ (A : VTy) (η₀ : Nat → TEnt) (σ : Nat → VTy), (∀ n, (η₀ n).ty = σ n) →
      (∀ n b ls v r, (η₀ n).P b ls v r → G b (σ n) ls v r) →
      (∀ n, ¬ A.NoMut n → (η₀ n).P = fun b ls => vC b (σ n) ls δ) →
      ∀ b ls v r, vCE (some η₀) b A ls δ v r → G b (A.subst σ) ls v r := by
    intro A
    induction A using VTy.recV with
    | unit => intro _ _ _ _ _ b ls v r hr; exact hG b _ ls v r hr
    | tensor A B ihA ihB =>
        intro η₀ σ ht hP hex b ls v r hr
        obtain ⟨v₁, v₂, ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', h₁, h₂⟩ := hr
        exact hG b _ ls v r ⟨v₁, v₂, ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc',
          ihA η₀ σ ht hP (fun n hn => hex n (fun h => hn h.1)) b ls v₁ ρ₁ h₁,
          ihB η₀ σ ht hP (fun n hn => hex n (fun h => hn h.2)) b ls v₂ ρ₂ h₂⟩
    | zero => intro _ _ _ _ _ _ _ _ _ hr; exact hr.elim
    | sum A B ihA ihB =>
        intro η₀ σ ht hP hex b ls v r hr
        rcases hr with ⟨v₁, ρ₀, ρ₁, hc, hp, h₁⟩ | ⟨v₂, ρ₀, ρ₂, hc, hp, h₂⟩
        · exact hG b _ ls v r (Or.inl ⟨v₁, ρ₀, ρ₁, hc, hp,
            ihA η₀ σ ht hP (fun n hn => hex n (fun h => hn h.1)) b ls v₁ ρ₁ h₁⟩)
        · exact hG b _ ls v r (Or.inr ⟨v₂, ρ₀, ρ₂, hc, hp,
            ihB η₀ σ ht hP (fun n hn => hex n (fun h => hn h.2)) b ls v₂ ρ₂ h₂⟩)
    | thunk _ => intro _ _ _ _ _ b ls v r hr; cases b <;> exact hG _ _ ls v r hr
    | ref A ih =>
        intro η₀ σ ht hP hex b ls v r hr
        obtain ⟨ℓ, v', ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', ho, h₂⟩ := hr
        exact hG b _ ls v r ⟨ℓ, v', ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', ho,
          ih η₀ σ ht hP hex b ls v' ρ₂ h₂⟩
    | imm a A ih =>
        intro η₀ σ ht hP hex b ls v r hr
        have e : tClose (some η₀) A = A.subst σ := by
          simp only [tClose]; congr 1; funext n; exact ht n
        obtain ⟨α, hα, ℓ, ρ₀, ρ₁, hc, hp, hpto⟩ := hr
        rw [e] at hp
        exact hG b _ ls v r ⟨α, hα, ℓ, ρ₀, ρ₁, hc, hp,
          ptoImmS_mono (fun ls₀ u σ' hu => ih η₀ σ ht hP hex false ls₀ u σ' hu) hpto⟩
    | «mut» a A ih =>
        intro η₀ σ ht hP hex b ls v r hr
        have hmut : ∀ b' ls₀, vCE (some η₀) b' A ls₀ δ = vC b' (A.subst σ) ls₀ δ := by
          intro b' ls₀
          rw [vC_eq_some, vCE_subst]
          refine congrFun (congrFun (vCE_congr_occ A _ _ (fun n hn => ?_) b') ls₀) δ
          refine TEnt.ext' ((ht n).trans (VTy.subst_id _).symm) ?_
          rw [hex n (fun h => h hn)]
          funext b'' ls''
          exact vC_eq_some b'' (σ n) ▸ rfl
        have hr' : vC b (.mut a (A.subst σ)) ls δ v r := by
          have e : (fun ls₀ => vCE (some η₀) true A ls₀ δ) = (fun ls₀ => vC true (A.subst σ) ls₀ δ) :=
            funext (hmut true)
          obtain ⟨α, hα, ℓ, ρ₀, ρ₁, hc, hp, hpto⟩ := hr
          refine ⟨α, hα, ℓ, ρ₀, ρ₁, hc, hp, ?_⟩
          rw [← e]; exact hpto
        refine hG b _ ls v r ⟨hr', fun ls' u σ' hu => ?_⟩
        rw [← hmut] at hu
        exact ih η₀ σ ht hP (fun n hn => hex n (fun h => hn (VTy.noMut_of_not_occ A h))) true ls' u σ' hu
    | box a A ih =>
        intro η₀ σ ht hP hex b ls v r hr
        obtain ⟨α, hα, hb, ho⟩ := hr
        exact hG b _ ls v r ⟨α, hα, ih η₀ σ ht hP hex b ls v r hb, ho⟩
    | bang A ih =>
        intro η₀ σ ht hP hex b ls v r hr
        exact hG b _ ls v r ⟨hr.1, ih η₀ σ ht hP hex true ls v r hr.2⟩
    | unk => intro _ _ _ _ _ b ls v r hr; exact hG b _ ls v r hr
    | tvar n => intro η₀ σ _ hP _ b ls v r hr; exact hP n b ls v r hr
    | mu B ih =>
        intro η₀ σ ht hP hex b ls v r hr
        obtain ⟨hnm, hcl, hlfp⟩ := hr
        have hM : tClose (some η₀) (.mu B) = (VTy.mu B).subst σ := by
          simp only [tClose]; congr 1; funext n; exact ht n
        rw [hM] at hcl hlfp
        refine hlfp (fun b ls v r => G b ((VTy.mu B).subst σ) ls v r) (fun b' ls' v' r' h' => ?_)
        have hB := ih (VTy.scons ⟨(VTy.mu B).subst σ,
            fun b ls v r => G b ((VTy.mu B).subst σ) ls v r⟩ η₀)
          (VTy.scons ((VTy.mu B).subst σ) σ)
          (fun n => by cases n with
            | zero => rfl
            | succ n => exact ht n)
          (fun n => by cases n with
            | zero => exact fun _ _ _ _ h => h
            | succ n => exact hP n)
          (fun n hn => by cases n with
            | zero => exact absurd hnm hn
            | succ n => exact hex n hn) b' ls' v' r' h'
        rw [VTy.subst_scons_eq_inst] at hB
        exact hG _ _ _ _ _ ⟨(VTy.noMut_upS_iff B σ).mpr hnm, hcl, hB⟩
  intro b T ls v ρ hT
  rw [vC_eq_some] at hT
  have := gen T tNil .tvar (fun _ => rfl) (fun _ _ _ _ _ h => h.elim) (fun _ _ => rfl) b ls v ρ hT
  rw [VTy.subst_id] at this
  exact this.2

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
      cBody A δ (fun b ls v ρ => vC b (.mu A) ls δ v ρ ∧ P b ls v ρ) b ls v ρ → P b ls v ρ) :
    ∀ b ls v ρ, vC b (.mu A) ls δ v ρ → P b ls v ρ := by
  intro b ls v ρ hv
  obtain ⟨hA, hc, hlfp⟩ := hv
  refine (hlfp (fun b ls v ρ => vC b (.mu A) ls δ v ρ ∧ P b ls v ρ)
    (fun b' ls' v' ρ' h' => ⟨vC_roll hA hc ?_, h b' ls' v' ρ' hA hc h'⟩)).2
  rw [vC_inst]
  exact cBody_mono A δ hA (fun _ _ _ _ h => h.1) b' ls' v' ρ' h'

end BoCa.Fig16.LogRel.Core

end
