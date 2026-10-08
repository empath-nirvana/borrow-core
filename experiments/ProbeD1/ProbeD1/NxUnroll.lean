import ProbeD1.Nx

/-!
# ProbeD1 — `VRLMUnroll`: `vRLM`'s substitution lemma and the `μ` rows (`NEXT.md` item 2)

`vRLM` reads `μ` itself, by a least fixed point over W's clauses (`R1.lean`), so the unroll row
needs `vRLM`'s analog of Core's substitution lemma. The route is `Core/RelMu.lean`'s at W's
clauses:

* `vRLM_some` (`vCE_some`): the relation reads its environment only through `wEnv`.
* `vRLM_rename` and `vRLM_subst` (`vCE_rename`, `vCE_subst`): by induction on the type. `VTy.subst`
  leaves `U C` alone and `vRLM`'s `U` clause reads no environment (`vRLM_thunk_env`); a `Mut` or
  `Imm` leaf reads its type closed by the environment (`wClose`, through `VTy.subst_subst`); a
  variable reads its entry; `μ` moves the substitution under the binder (`VTy.upS`), the entry
  for the bound variable fixed and the others renamed (`vRLM_rename`).
* `vRLM_inst` (`vC_inst`): the unrolling is the body at the `μ` itself.
* `vRLM_unroll` (`vC_mu_iff`): `vRLM_roll` one way; the other is the least fixed point at the
  candidate the body at the `μ` gives, inside the `μ` by `vRLM_mono_at` and `vRLM_roll`.
* `rollRowM`, `unrollRowM`: `[roll]` and `[unroll]` at `SemSM` at every placement, the index facts
  carried between `μX. A` and `A[μX. A/X]` (their free lifetime variables agree, and the
  unrolling's binders are `A`'s). `StackJM`'s added conjunct reads an outermost `∀`, so at `F _` it
  is `StackJ` (`stackJM_of_notAll`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace ProbeD1
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open GhostEnd (LEnt LStack LKind extS vwE vwS vis stratS ReLend TabAtS jdgCty)

theorem WEnt.ext' {a b : WEnt} (h₁ : a.ty = b.ty) (h₂ : a.P = b.P) : a = b := by
  cases a; cases b; simp only at h₁ h₂; subst h₁; subst h₂; rfl

/-! ### The environment -/

/-- **`VRLMSome`**: the relation reads its environment only through `wEnv`. -/
theorem vRLM_some (p : Placement) (σ : LStack) (δ : LSub) (αs : List Life) (ls : List SRec) :
    ∀ (A : VTy) (η : Option (Nat → WEnt)),
      vRLM (ℍ := ℍ) p η σ δ A αs ls = vRLM (ℍ := ℍ) p (some (wEnv η)) σ δ A αs ls := by
  intro A
  induction A using VTy.recV with
  | unit => intro η; rfl
  | int w => intro η; rfl
  | opq k => intro η; rfl
  | zero => intro η; rfl
  | unk => intro η; rfl
  | thunk C => intro η; funext v; exact vRLM_thunk_env p η _ σ δ C αs ls v
  | tensor A B ihA ihB => intro η; funext v; rw [vRLM, vRLM, ihA, ihB]
  | sum A B ihA ihB => intro η; funext v; rw [vRLM, vRLM, ihA, ihB]
  | ref A ih => intro η; funext v; rw [vRLM, vRLM, ih]
  | fam L ih => intro η; funext v; rw [vRLM, vRLM, ih]
  | box a A ih => intro η; funext v; rw [vRLM, vRLM, ih]
  | bang A ih => intro η; funext v; rw [vRLM, vRLM, ih]
  | imm a A _ =>
      intro η; funext v
      rw [vRLM_imm_eq, vRLM_imm_eq, wClose_eq, wClose_eq]; rfl
  | «mut» a A _ =>
      intro η; funext v
      rw [vRLM_mut_eq, vRLM_mut_eq, wClose_eq, wClose_eq]; rfl
  | tvar n => intro η; funext v; rw [vRLM, vRLM, wEnvP_eq]; rfl
  | mu A _ =>
      intro η; funext v
      have e : wClose η (.mu A) = wClose (some (wEnv η)) (.mu A) := by
        rw [wClose_eq, wClose_eq]; rfl
      rw [vRLM, vRLM, e]
      rfl

theorem vRLMSome : VRLMSome (ℍ := ℍ) := fun p η A σ δ αs ls => vRLM_some p σ δ αs ls A η

/-! ### Renaming and substitution -/

/-- **`VRLMRename`.** -/
theorem vRLM_rename (p : Placement) (σ : LStack) (δ : LSub) (αs : List Life) (ls : List SRec) :
    ∀ (A : VTy) (ρ : Nat → WEnt) (r : Nat → Nat),
      vRLM (ℍ := ℍ) p (some ρ) σ δ (A.rename r) αs ls =
        vRLM (ℍ := ℍ) p (some (ρ ∘ r)) σ δ A αs ls := by
  intro A
  induction A using VTy.recV with
  | unit => intro ρ r; rfl
  | int w => intro ρ r; rfl
  | opq k => intro ρ r; rfl
  | zero => intro ρ r; rfl
  | unk => intro ρ r; rfl
  | thunk C => intro ρ r; funext v; exact vRLM_thunk_env p _ _ σ δ C αs ls v
  | tensor A B ihA ihB => intro ρ r; funext v; rw [VTy.rename, vRLM, vRLM, ihA, ihB]
  | sum A B ihA ihB => intro ρ r; funext v; rw [VTy.rename, vRLM, vRLM, ihA, ihB]
  | ref A ih => intro ρ r; funext v; rw [VTy.rename, vRLM, vRLM, ih]
  | fam L ih => intro ρ r; funext v; rw [VTy.rename, vRLM, vRLM, ih]
  | box a A ih => intro ρ r; funext v; rw [VTy.rename, vRLM, vRLM, ih]
  | bang A ih => intro ρ r; funext v; rw [VTy.rename, vRLM, vRLM, ih]
  | imm a A _ =>
      intro ρ r; funext v
      rw [VTy.rename, vRLM_imm_eq, vRLM_imm_eq]
      simp only [wClose, VTy.subst_rename]; rfl
  | «mut» a A _ =>
      intro ρ r; funext v
      rw [VTy.rename, vRLM_mut_eq, vRLM_mut_eq]
      simp only [wClose, VTy.subst_rename]; rfl
  | tvar n => intro ρ r; funext v; rw [VTy.rename, vRLM, vRLM]; rfl
  | mu A ih =>
      intro ρ r; funext v
      have e' : wClose (some ρ) (.mu (A.rename (VTy.upR r))) = wClose (some (ρ ∘ r)) (.mu A) := by
        simp only [wClose]
        rw [show VTy.mu (A.rename (VTy.upR r)) = (VTy.mu A).rename r from rfl, VTy.subst_rename]
        rfl
      rw [VTy.rename, vRLM, vRLM]
      simp only [e', wEnv, ih, scons_comp_upR, VTy.noMut_rename_upR_iff]

theorem vRLMRename : VRLMRename (ℍ := ℍ) :=
  fun p A ρ r σ δ αs ls => vRLM_rename p σ δ αs ls A ρ r

/-- **`VRLMSubst`.** -/
theorem vRLM_subst (p : Placement) (σ : LStack) (δ : LSub) (αs : List Life) (ls : List SRec) :
    ∀ (A : VTy) (ρ : Nat → WEnt) (τ : Nat → VTy),
      vRLM (ℍ := ℍ) p (some ρ) σ δ (A.subst τ) αs ls =
        vRLM (ℍ := ℍ) p (some (substEnvW p ρ τ σ δ αs ls)) σ δ A αs ls := by
  intro A
  induction A using VTy.recV with
  | unit => intro ρ τ; rfl
  | int w => intro ρ τ; rfl
  | opq k => intro ρ τ; rfl
  | zero => intro ρ τ; rfl
  | unk => intro ρ τ; rfl
  | thunk C => intro ρ τ; funext v; exact vRLM_thunk_env p _ _ σ δ C αs ls v
  | tensor A B ihA ihB => intro ρ τ; funext v; rw [VTy.subst, vRLM, vRLM, ihA, ihB]
  | sum A B ihA ihB => intro ρ τ; funext v; rw [VTy.subst, vRLM, vRLM, ihA, ihB]
  | ref A ih => intro ρ τ; funext v; rw [VTy.subst, vRLM, vRLM, ih]
  | fam L ih => intro ρ τ; funext v; rw [VTy.subst, vRLM, vRLM, ih]
  | box a A ih => intro ρ τ; funext v; rw [VTy.subst, vRLM, vRLM, ih]
  | bang A ih => intro ρ τ; funext v; rw [VTy.subst, vRLM, vRLM, ih]
  | imm a A _ =>
      intro ρ τ; funext v
      rw [VTy.subst, vRLM_imm_eq, vRLM_imm_eq]
      simp only [wClose, substEnvW, VTy.subst_subst]
  | «mut» a A _ =>
      intro ρ τ; funext v
      rw [VTy.subst, vRLM_mut_eq, vRLM_mut_eq]
      simp only [wClose, substEnvW, VTy.subst_subst]
  | tvar n => intro ρ τ; rfl
  | mu A ih =>
      intro ρ τ; funext v
      have eM : wClose (some ρ) (.mu (A.subst (VTy.upS τ)))
          = wClose (some (substEnvW p ρ τ σ δ αs ls)) (.mu A) := by
        simp only [wClose, substEnvW]
        rw [show VTy.mu (A.subst (VTy.upS τ)) = (VTy.mu A).subst τ from rfl, VTy.subst_subst]
      have eNM : (A.subst (VTy.upS τ)).NoMut 0 ↔ A.NoMut 0 := VTy.noMut_upS_iff A τ
      rw [VTy.subst, vRLM, vRLM]
      funext r
      simp only [eM, wEnv]
      congr 1
      · exact propext eNM
      congr 1
      apply propext
      refine forall_congr' fun P => imp_congr ?_ Iff.rfl
      refine forall_congr' fun v' => forall_congr' fun r' => imp_congr ?_ Iff.rfl
      rw [ih]
      have eenv : substEnvW p (VTy.scons ⟨wClose (some (substEnvW p ρ τ σ δ αs ls)) (.mu A), P⟩ ρ)
          (VTy.upS τ) σ δ αs ls =
          VTy.scons ⟨wClose (some (substEnvW p ρ τ σ δ αs ls)) (.mu A), P⟩
            (substEnvW p ρ τ σ δ αs ls) := by
        funext n
        cases n with
        | zero => exact WEnt.ext' rfl rfl
        | succ n =>
            refine WEnt.ext' ?_ ?_
            · show (VTy.rename Nat.succ (τ n)).subst _ = _
              rw [VTy.subst_rename]; rfl
            · show vRLM (ℍ := ℍ) p _ σ δ (VTy.rename Nat.succ (τ n)) αs ls = _
              rw [vRLM_rename]; rfl
      rw [eenv]

theorem vRLMSubst : VRLMSubst (ℍ := ℍ) :=
  fun p A ρ τ σ δ αs ls => vRLM_subst p σ δ αs ls A ρ τ

/-! ### The unroll equation -/

/-- **`VRLMInst`**: the unrolling is the body at the `μ` itself. -/
theorem vRLM_inst (p : Placement) (A : VTy) (σ : LStack) (δ : LSub) (αs : List Life)
    (ls : List SRec) :
    vRLM (ℍ := ℍ) p none σ δ (VTy.inst (.mu A) A) αs ls =
      vRLM (ℍ := ℍ) p (some (VTy.scons ⟨.mu A, vRLM p none σ δ (.mu A) αs ls⟩ (wEnv none)))
        σ δ A αs ls := by
  rw [vRLM_some, VTy.inst, vRLM_subst]
  congr 2
  funext n
  cases n with
  | zero =>
      refine WEnt.ext' (VTy.subst_id _) ?_
      show vRLM (ℍ := ℍ) p (some (wEnv none)) σ δ (.mu A) αs ls = vRLM p none σ δ (.mu A) αs ls
      rw [← vRLM_some]
  | succ n =>
      refine WEnt.ext' rfl ?_
      funext v r
      show vRLM (ℍ := ℍ) p (some (wEnv none)) σ δ (.tvar n) αs ls v r = False
      rw [vRLM]; rfl

theorem vRLMInst : VRLMInst (ℍ := ℍ) := vRLM_inst

/-- **`VRLMUnroll`**: `vRLM_roll` one way; the other is the least fixed point at the body at the
`μ`, which is closed under the body by `vRLM_mono_at` at `0` and `vRLM_roll` (`vC_unfold`'s
argument). -/
theorem vRLMUnroll : VRLMUnroll (ℍ := ℍ) := by
  intro p A σ δ αs ls v ρ
  have hcl : (wClose none (.mu A)) = .mu A := rfl
  constructor
  · intro h
    obtain ⟨hA, hc, hlfp⟩ := h
    refine ⟨hA, hc, ?_⟩
    rw [vRLM_inst]
    refine hlfp (fun v' ρ' => vRLM (ℍ := ℍ) p (some (VTy.scons ⟨.mu A,
      vRLM p none σ δ (.mu A) αs ls⟩ (wEnv none))) σ δ A αs ls v' ρ') (fun v' ρ' h' => ?_)
    refine vRLM_mono_at p A 0 _ _ hA (fun n => by cases n <;> rfl) (fun n hn => ?_)
      (fun v'' ρ'' h'' => ?_) σ δ αs ls v' ρ' h'
    · cases n with
      | zero => exact absurd rfl hn
      | succ n => rfl
    · exact vRLM_roll hA hc h''
  · rintro ⟨hA, hc, h⟩
    rw [vRLM_inst] at h
    exact vRLM_roll hA hc h

/-! ### The rows -/

theorem vTy_binders_rename (r : Nat → Nat) : ∀ A : VTy, VTy.binders (A.rename r) = VTy.binders A := by
  intro A
  induction A using VTy.recV generalizing r with
  | unit | int _ | opq _ | zero | unk | tvar _ | thunk _ => rfl
  | tensor A B ihA ihB => simp only [VTy.rename, VTy.binders, ihA, ihB]
  | sum A B ihA ihB => simp only [VTy.rename, VTy.binders, ihA, ihB]
  | ref A ih => simp only [VTy.rename, VTy.binders, ih]
  | fam L ih => simp only [VTy.rename, VTy.binders, ih]
  | box a A ih => simp only [VTy.rename, VTy.binders, ih]
  | bang A ih => simp only [VTy.rename, VTy.binders, ih]
  | imm a A ih => simp only [VTy.rename, VTy.binders, ih]
  | «mut» a A ih => simp only [VTy.rename, VTy.binders, ih]
  | mu A ih => simp only [VTy.rename, VTy.binders, ih]

/-- A binder of a substitution instance is the type's or one of the substituted types'. -/
theorem vTy_binders_subst (τ : Nat → VTy) : ∀ (A : VTy) (x : LifeVar),
    x ∈ VTy.binders (A.subst τ) → x ∈ VTy.binders A ∨ ∃ n, x ∈ VTy.binders (τ n) := by
  intro A
  induction A using VTy.recV generalizing τ with
  | unit | int _ | opq _ | zero | unk | thunk _ => intro x h; exact Or.inl h
  | tvar n => intro x h; exact Or.inr ⟨n, h⟩
  | tensor A B ihA ihB =>
      intro x h
      simp only [VTy.subst, VTy.binders, List.mem_append] at h ⊢
      rcases h with h | h
      · rcases ihA τ x h with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
      · rcases ihB τ x h with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
  | sum A B ihA ihB =>
      intro x h
      simp only [VTy.subst, VTy.binders, List.mem_append] at h ⊢
      rcases h with h | h
      · rcases ihA τ x h with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
      · rcases ihB τ x h with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
  | ref A ih => intro x h; exact ih τ x h
  | fam L ih => intro x h; exact ih τ x h
  | box a A ih => intro x h; exact ih τ x h
  | bang A ih => intro x h; exact ih τ x h
  | imm a A ih => intro x h; exact ih τ x h
  | «mut» a A ih => intro x h; exact ih τ x h
  | mu A ih =>
      intro x h
      rcases ih (VTy.upS τ) x h with h | ⟨n, hn⟩
      · exact Or.inl h
      · cases n with
        | zero => exact absurd hn (by simp [VTy.upS, VTy.scons, VTy.binders])
        | succ n =>
            refine Or.inr ⟨n, ?_⟩
            have : VTy.upS τ (n + 1) = VTy.rename Nat.succ (τ n) := rfl
            rwa [this, vTy_binders_rename] at hn

/-- A binder of the type is one of every substitution instance. -/
theorem vTy_binders_subst_of (τ : Nat → VTy) : ∀ (A : VTy) (x : LifeVar),
    x ∈ VTy.binders A → x ∈ VTy.binders (A.subst τ) := by
  intro A
  induction A using VTy.recV generalizing τ with
  | unit | int _ | opq _ | zero | unk | thunk _ => intro x h; exact h
  | tvar n => intro x h; exact absurd h (by simp [VTy.binders])
  | tensor A B ihA ihB =>
      intro x h
      simp only [VTy.subst, VTy.binders, List.mem_append] at h ⊢
      exact h.imp (ihA τ x) (ihB τ x)
  | sum A B ihA ihB =>
      intro x h
      simp only [VTy.subst, VTy.binders, List.mem_append] at h ⊢
      exact h.imp (ihA τ x) (ihB τ x)
  | ref A ih => intro x h; exact ih τ x h
  | fam L ih => intro x h; exact ih τ x h
  | box a A ih => intro x h; exact ih τ x h
  | bang A ih => intro x h; exact ih τ x h
  | imm a A ih => intro x h; exact ih τ x h
  | «mut» a A ih => intro x h; exact ih τ x h
  | mu A ih => intro x h; exact ih (VTy.upS τ) x h

/-- `μX. A` and its unrolling have the same binders. -/
theorem vTy_binders_inst_iff (A : VTy) (x : LifeVar) :
    x ∈ VTy.binders (VTy.inst (.mu A) A) ↔ x ∈ VTy.binders (.mu A) := by
  constructor
  · intro h
    rcases vTy_binders_subst _ A x h with h | ⟨n, hn⟩
    · exact h
    · cases n with
      | zero => exact hn
      | succ n => exact absurd hn (by simp [VTy.scons, VTy.binders])
  · exact vTy_binders_subst_of _ A x

/-- `μX. A` and its unrolling have the same free lifetime variables. -/
theorem vFree_inst_iff (A : VTy) (y : LifeVar) :
    VFree y (VTy.inst (.mu A) A) ↔ VFree y (.mu A) := by
  constructor
  · intro h
    rcases vFree_subst A _ h with h | ⟨n, hn⟩
    · exact h
    · cases n with
      | zero => exact hn
      | succ n => exact hn.elim
  · exact vFree_subst_of A _

/-- **The index facts carry between `F (μX. A)` and `F (A[μX. A/X])`**: binder hygiene, scoping and
`StackJ` read the type only through its binders and its free lifetime variables, which agree. -/
theorem semIdx_mu_iff {Δ : LifeCtx} {Γ : Ctx VTy} {A : VTy} {σ : LStack} {αs : List Life}
    {δ : LSub} :
    (BindersLow Γ (.ret (VTy.inst (.mu A) A)) ↔ BindersLow Γ (.ret (.mu A))) ∧
    (Scoped Δ Γ (.ret (VTy.inst (.mu A) A)) ↔ Scoped Δ Γ (.ret (.mu A))) ∧
    (StackJ σ αs δ Δ Γ (.ret (VTy.inst (.mu A) A)) ↔ StackJ σ αs δ Δ Γ (.ret (.mu A))) := by
  have hb : ∀ x, x ∈ CTy.binders (.ret (VTy.inst (.mu A) A)) ↔ x ∈ CTy.binders (.ret (.mu A)) :=
    fun x => vTy_binders_inst_iff A x
  have hf : ∀ y, CFree y (.ret (VTy.inst (.mu A) A)) ↔ CFree y (.ret (.mu A)) :=
    fun y => vFree_inst_iff A y
  refine ⟨⟨fun h => ⟨fun x hx => h.1 x ((hb x).mpr hx), h.2⟩,
      fun h => ⟨fun x hx => h.1 x ((hb x).mp hx), h.2⟩⟩,
    ⟨fun h => ⟨fun y hy => h.1 y ((hf y).mpr hy), h.2⟩,
      fun h => ⟨fun y hy => h.1 y ((hf y).mp hy), h.2⟩⟩, ?_⟩
  constructor
  · rintro ⟨h₁, h₂, h₃⟩
    refine ⟨h₁, h₂, fun e he => ?_⟩
    rcases h₃ e he with h | ⟨hns, hΔ, hC, hΓ⟩ | ⟨-, -, -, c, C', hC, -⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨hns, hΔ, fun h => hC ((hf _).mpr h), hΓ⟩)
    · cases hC
  · rintro ⟨h₁, h₂, h₃⟩
    refine ⟨h₁, h₂, fun e he => ?_⟩
    rcases h₃ e he with h | ⟨hns, hΔ, hC, hΓ⟩ | ⟨-, -, -, c, C', hC, -⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨hns, hΔ, fun h => hC ((hf _).mp h), hΓ⟩)
    · cases hC

/-- **`RollRowM`**: `[roll]` at `SemSM`, at every placement, with the rule's own premises. -/
theorem rollRowM (p : Placement) : RollRowM (ℍ := ℍ) p := by
  intro Δ Γ e A hA hc h hB hS δ σ αs ls γ ρ hok hob hJ hD hM hR hSO hT hPV hG
  obtain ⟨eB, eS, eJ⟩ := semIdx_mu_iff (Δ := Δ) (Γ := Γ) (A := A) (σ := σ) (αs := αs) (δ := δ)
  have := h (eB.mpr hB) (eS.mpr hS) δ σ αs ls γ ρ hok hob
    (stackJM_of_notAll (eJ.mpr hJ.1) (fun _ _ _ h => by cases h)) hD hM hR hSO hT hPV hG
  exact wpTS_mono (fun ls' v ρ' h' => (vRLMUnroll p A σ δ αs ls' v ρ').mpr ⟨hA, hc, h'⟩) ρ this

/-- **`UnrollRowM`**: `[unroll]` at `SemSM`, at every placement; the rule has no premise beside
its derivation. -/
theorem unrollRowM (p : Placement) : UnrollRowM (ℍ := ℍ) p := by
  intro Δ Γ e A h hB hS δ σ αs ls γ ρ hok hob hJ hD hM hR hSO hT hPV hG
  obtain ⟨eB, eS, eJ⟩ := semIdx_mu_iff (Δ := Δ) (Γ := Γ) (A := A) (σ := σ) (αs := αs) (δ := δ)
  have := h (eB.mp hB) (eS.mp hS) δ σ αs ls γ ρ hok hob
    (stackJM_of_notAll (eJ.mp hJ.1) (fun _ _ _ h => by cases h)) hD hM hR hSO hT hPV hG
  exact wpTS_mono (fun ls' v ρ' h' => ((vRLMUnroll p A σ δ αs ls' v ρ').mp h').2.2) ρ this

end ProbeD1

end
