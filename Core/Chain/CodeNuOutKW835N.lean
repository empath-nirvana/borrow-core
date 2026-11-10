import Core.Chain.CodeRulesKW835N
import Core.CodeNuOut

/-!
# `unfoldK` and `nuOutK` at the chain's relation  `[spec §68]`

Core's `Core/CodeNuOut.lean` at `SemJN`, the relation `goal791N` reads.

* `unfoldK_compatN` (Core's `unfoldK_compatX`): `unfoldN_compatN`'s proof at the step's code;
  `unfold step` is `hCode C` closed by `[step]`, and `unfold step s` is in the code clause
  (`etaN_codeRelN`).
* `nuOutK_compatN` (Core's `nuOutK_compatX`): an observation of `unfold step s` read at
  `𝒞⟦C[Code⟨etaCode C; !G ⊗ (S ⊗ 1)⟩ (νX. C)/X]⟧`.

**The unrolling at a code type.** Core reads one unfolding at the code's candidate as the
unrolled type (`cB_unrollK`): `U X` at `codeCand` is the code type, the candidate's quantifier
over lists being `vC_local`'s. At the chain's relation `U X` is read at the candidate through
`thunkRN`, at the `OK` extensions of the world and the views consistent with the resource, while
the code clause reads the environment at the leaf's own world. So the leaf of `cBN` at
`codeCandN` gives the code clause only at those extensions, and `cBN (.thunk (.nu C)) codeCandN D
⊆ cN (D[Code⟨…⟩ (νX. C)/X])` is not derived from `nuOutK_stepN` (obstruction not verified). The
observation is read at the unrolled type directly instead: `node_okK` is `node_okN` with every
leaf mapped into `𝒱⟦A[Code⟨…⟩ (νX. C)/X]⟧` (`map_okN` at the code type), each rest `unfold step s′` in the code
clause at the leaf's world (`etaN_codeRelN` at the state's world and index).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel (LtLife substAll)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Kont Head)

/-- A type forced at `S ⊸ C[S/X]` erases to `U(S ⊸ C[S/X])` at the chain's relation. -/
theorem vN_step_of_forceTy {G S : VTy} {C : CTy} (hG : G.forceTy = some (.arr S (C.instT S)))
    {δ : LSub} : ∀ Θ k v ρ, vN (ℍ := ℍ) G δ Θ k v ρ →
      vN (ℍ := ℍ) (.thunk (.arr S (C.instT S))) δ Θ k v ρ := by
  intro Θ k v ρ h
  cases G <;> simp only [VTy.forceTy, Option.some.injEq, reduceCtorEq] at hG
  · subst hG; exact h
  · subst hG; exact h.2

/-! ### `unfoldK` -/

/-- **`unfoldK` at `SemJN`** (Core's `unfoldK_compatX`): `unfoldN_compatN`'s proof at the step's
code.  `[spec §68]` -/
theorem unfoldK_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {C : CTy} (hC : C.NuOk) {G S : VTy}
    (hG : G.forceTy = some (.arr S (C.instT S))) (hS : C.BindsFresh S) (hΓ : Ctx.DeadP Γ) :
    SemJN (ℍ := ℍ) Δ Γ (.val (unfoldV C)) (.val (unfoldKTy C G S)) := by
  intro δ γ Θ c n ls ρ _ _ _ _ hg
  obtain rfl := gN_deadP hΓ hg
  rw [substAll_closed (unfoldV_closed C)]
  refine cN_ret_of (erwp_val (v := unfoldV C) ?_)
  intro Θ' _ hΘ' _ _ ls' c'' k _ g σ τ hcomp hv hcon
  have hσ : σ = PMap.empty := hv.1
  subst hσ
  obtain rfl := eq_of_compS_empty_left hcomp
  have hg' : ∀ Θ'' : LocTy, vN (ℍ := ℍ) (.bang G) δ Θ'' k g PMap.empty :=
    fun Θ'' => vN_extR _ δ k g _ (LocTy.extR_empty Θ' Θ'') hv
  have hΦ := LocTy.view_down hΘ'.1 c''
  refine cN_ret_of ?_
  refine erwp_det hΦ (opTableN_down OpTabN.empty_down) (fun k _ v ρ h => vN_down _ δ Θ' k v ρ h)
    (fun μ => step1Only_plug (Head.beta μ _ g) rfl .hole) ?_
  simp only [Kont.plug]
  rw [unfoldV_subst]
  refine erwp_val (v := hN C g) ⟨rfl, ⟨[g], hN_code C g, ?_⟩, ?_⟩
  · exact ⟨g, .unit, PMap.empty, PMap.empty, rfl, compS_empty_left _, hg' Θ', rfl, rfl⟩
  intro Θ₂ _ hΘ₂ _ _ ls₂ c₃ k' hk' s ρs ρ₃ hcomp' hs hcon'
  have e₃ := eq_of_compS_empty_left hcomp'
  subst e₃
  refine cN_head (.ret (codeTy C G S)) δ Θ₂ hΘ₂.1 c₃ k' ls₂ _ .hole _ _
    (fun μ => Head.beta μ _ s) rfl ?_
  simp only [Kont.plug]
  rw [hN_subst]
  exact cN_ret_of (erwp_val (v := etaN C g s)
    (etaN_codeRelN hC hS (vN_step_of_forceTy hG) (fun Θ'' => vN_le hk' (hg' Θ'')) hs))

/-! ### `nuOutK` -/

/-- **`𝒞⟦C⟧` is closed under a pure step backwards** (`cBN_step` at the relation itself). -/
theorem cN_step : ∀ (C : CTy) (δ : LSub) (Θ : LocTy), Θ.Down → ∀ (c : Loc → Option Life)
    (n : Nat) (ls : List SRec) (ρ : WRes) (e e' : Expr),
    (∀ μ, BoCa.BoLo.Step1N (ℍ := ℍ) μ e μ e') →
    cN (ℍ := ℍ) C δ Θ c n ls e' ρ → cN (ℍ := ℍ) C δ Θ c n ls e ρ
  | .ret A, δ, _, hΘ, _, _, _, _, _, _, hs, h => fun lo =>
      erwpK_ret_det hΘ (fun z k v ρ h => vN_down A δ z.Θ k v ρ h)
        (fun μ => step1Only_of_step1N (hs μ)) (h lo)
  | .arr _ C, δ, Θ, hΘ, _, _, ls, _, _, _, hs, h =>
      fun c' k hk v ρv ρ' hc hv hcon =>
        cN_step C δ Θ hΘ c' k ls ρ' _ _ (fun μ => (hs μ).plug (Kont.appL .hole v))
          (h c' k hk v ρv ρ' hc hv hcon)
  | .amp C D, δ, Θ, hΘ, c, n, ls, ρ, _, _, hs, h =>
      ⟨cN_step C δ Θ hΘ c n ls ρ _ _ (fun μ => (hs μ).plug (Kont.appL .hole _)) h.1,
        cN_step D δ Θ hΘ c n ls ρ _ _ (fun μ => (hs μ).plug (Kont.appL .hole _)) h.2⟩
  | .top, _, _, _, _, _, _, _, _, _, _, h => h
  | .all x _ C, δ, Θ, hΘ, c, n, ls, ρ, _, _, hs, h =>
      fun α hα => cN_step C (δ.extend x α) Θ hΘ c n ls ρ _ _
        (fun μ => (hs μ).plug (Kont.appL .hole _)) (h α hα)
  | .nu C, δ, Θ, hΘ, c, n, ls, ρ, _, _, hs, h => fun hS =>
      (cN_nu_unfold hS δ Θ c n ls _ ρ).mpr (cBN_step _ (nuCand_down C δ) C δ Θ hΘ c n ls ρ _ _
        hs ((cN_nu_unfold hS δ Θ c n ls _ ρ).mp h)) hS
  | .eff _ _ _ _ _ _ _ _, _, _, hΘ, _, _, _, _, _, _, hs, h =>
      cN_eff_det hΘ (fun μ => step1Only_of_step1N (hs μ)) h

/-- Pure steps in front of `𝒞⟦C⟧`. -/
theorem cN_pureSteps (C : CTy) (δ : LSub) {Θ : LocTy} (hΘ : Θ.Down) (c : Loc → Option Life)
    (n : Nat) (ls : List SRec) (ρ : WRes) {e e' : Expr} (h : PureSteps e e')
    (hw : cN (ℍ := ℍ) C δ Θ c n ls e' ρ) : cN (ℍ := ℍ) C δ Θ c n ls e ρ := by
  induction h with
  | refl => exact hw
  | tail _ hs ih => exact ih (cN_step C δ Θ hΘ c n ls ρ _ _ hs hw)

/-- **The node lemma at a code type** (`node_okN` read at the unrolled type): when `c ()` runs a
computation of `D[S/X]`, `node_D (unfold step) c` is a computation of `D[T/X]`, each state `s′`
mapped to `unfold step s′ ∈ 𝒱⟦T⟧`.  The tree is read at `δ`, agreeing with `δ₀` on `T`'s free
variables; under a `∀'x` leaf at `δ[x ↦ α]`, which still agrees because `'x` is not free in `T`.
`[spec §68]` -/
-- A near-copy of `node_okN` at target `cN (D.instT T)`; to be merged by generalising `cBN` (#947).
theorem node_okK (C : CTy) (g : Val) (S T : VTy) (δ₀ : LSub) (kg : Nat)
    (hW : ∀ δ, (∀ y, VFree y T → δ₀.find? y = δ.find? y) → ∀ Θ k w σ, k ≤ kg →
      vN (ℍ := ℍ) S δ Θ k w σ → vN (ℍ := ℍ) T δ Θ k (etaN C g w) σ) :
    ∀ (D : CTy), D.NuLeaf → (∀ x, D.LeafBinds x → ¬ VFree x T) → ∀ (δ : LSub),
      (∀ y, VFree y T → δ₀.find? y = δ.find? y) → ∀ (Θ : LocTy),
      Θ.OK → ∀ (c : Loc → Option Life) (j : Nat), j ≤ kg → ∀ (cv : Val) (M : Expr)
      (ls : List SRec) (ρ : WRes),
      PureSteps (.app (.val cv) (.val .unit)) M → cN (ℍ := ℍ) (D.instT S) δ Θ c j ls M ρ →
      cN (ℍ := ℍ) (D.instT T) δ Θ c j ls
        (.app (.app (.val (nodeV D)) (.val (hN C g))) (.val cv)) ρ
  | .ret A, hA, _, δ, hag, Θ, hΘ, c, j, hj, cv, M, ls, ρ, hc, hM => fun lo => by
      have hΦ : ∀ z : KW, z.Θ.OK → (z.Θ.view z.c).Down := fun z hz => LocTy.view_down hz.1 z.c
      have hDI : ∀ z : KW, (OpTabK.empty : OpTabK KW).DownI (fun z : KW => z.Θ.OK) :=
        fun _ => OpTabK.empty_downI _
      have hTd : (opTableK lo (OpTabK.empty : OpTabK KW)).Down := opTableK_downI (hDI ⟨Θ, c, lo⟩)
      have hQd : ∀ y : KW, PostN.Down (fun k _ v ρ => vN (ℍ := ℍ) (VTy.inst T A) δ y.Θ k v ρ) :=
        fun y k _ v ρ h => vN_down _ δ y.Θ k v ρ h
      refine erwpK_pureSteps (x := (⟨Θ, c, lo⟩ : KW)) (hΦ _ hΘ) hTd hQd
        (nodeV_ret_steps A _ cv) ?_
      refine erwpK_pureSteps (x := (⟨Θ, c, lo⟩ : KW)) (hΦ _ hΘ) hTd hQd
        (PureSteps.plug (.appR (.val (.lam _)) .hole) hc) ?_
      refine erwpK_bind_leI (V := KW.PostK) (fun _ _ _ h₁ h₂ => KW.PostK.trans h₁ h₂)
        (Φ := fun z : KW => z.Θ.view z.c) (Inv := fun z : KW => z.Θ.OK) hΦ
        (fun _ _ h => by rw [h]) (fun _ _ h hx => by rw [h]; exact hx) (fl := fun z : KW => z.lo)
        (T := fun _ => OpTabK.empty)
        (fun _ _ h => tabLe_postK (fun z : KW => opTableK z.lo (OpTabK.empty : OpTabK KW)) h)
        (Q' := fun z k _ v ρ => vN (ℍ := ℍ) (VTy.inst S A) δ z.Θ k v ρ)
        (.appR (.val (.lam _)) .hole) (fun _ => by simp [Kont.HasHnd])
        (fun _ => by simp [Kont.Catches]) (fun _ _ _ _ _ h => by cases h)
        (fun _ _ _ _ h => by cases h) kg ?_ j hj (⟨Θ, c, lo⟩ : KW) hΘ ls M ρ (hM lo)
      rintro y hy k ls' w σ hk hw
      rw [← vNX_inst_poly S δ hA] at hw
      obtain ⟨w', hs, h'⟩ := map_okN C g S δ kg T _ (hW δ hag) A hA y.Θ k hk w σ hw
      rw [vNX_inst_poly T δ hA] at h'
      have hTy : (opTableK y.lo (OpTabK.empty : OpTabK KW)).Down := opTableK_downI (hDI y)
      refine erwpK_det (x := y) (Φ := fun z : KW => z.Θ.view z.c) (hΦ y hy) hTy hQd
        (fun μ => step1Only_plug (Head.beta μ _ w) rfl .hole) ?_
      have e : Expr.subst 0 w (.app (.app (.val (mapV A)) (.val ((hN C g).shift 1 0))) (.var 0))
          = .app (.app (.val (mapV A)) (.val (hN C g))) (.val w) := by
        simp [Expr.subst, Val.val_shift, Expr.shift_zero, closed_subst (mapV_closed A),
          subst_shift_succ]
      simp only [Kont.plug]
      rw [e]
      exact erwpK_pureSteps (x := y) (Φ := fun z : KW => z.Θ.view z.c) (hΦ y hy) hTy hQd hs
        (erwpK_val (KW.postK_refl y) h')
  | .eff m i q A B fin rc D, hD, _, δ, hag, Θ, hΘ, c, j, hj, cv, M, ls, ρ, hc, hM => fun lo => by
      have hΦ : ∀ z : KW, z.Θ.OK → (z.Θ.view z.c).Down := fun z hz => LocTy.view_down hz.1 z.c
      have hDI : ∀ z : KW, (tabN (ℍ := ℍ) (.eff m i q A B fin rc D) δ z).DownI
          (fun z : KW => z.Θ.OK) := fun z => tabN_downI_OK _ δ z
      have hR := EffLeaf.ans_poly (C := D) hD.2.2
      have hQd : ∀ y : KW, PostN.Down (fun k _ v ρ => retN (ℍ := ℍ) (D.instT T) δ y.Θ k v ρ) :=
        fun y k _ v ρ h => retN_down _ δ y.Θ k v ρ h
      show erwpK (ℍ := ℍ) KW.PostK (fun z => z.Θ.view z.c)
        (fun z => opTableK z.lo (tabN (ℍ := ℍ) ((CTy.eff m i q A B fin rc D).instT T) δ z))
        (fun z k _ v ρ => retN (ℍ := ℍ) (D.instT T) δ z.Θ k v ρ)
        (⟨Θ, c, lo⟩ : KW) j ls _ ρ
      rw [tabN_instT]
      have hTd : (opTableK lo (tabN (ℍ := ℍ) (.eff m i q A B fin rc D) δ ⟨Θ, c, lo⟩)).Down :=
        opTableK_downI (hDI ⟨Θ, c, lo⟩)
      refine erwpK_pureSteps (x := (⟨Θ, c, lo⟩ : KW)) (hΦ _ hΘ) hTd hQd
        (nodeV_eff_steps m i q A B fin D _ cv) ?_
      refine erwpK_pureSteps (x := (⟨Θ, c, lo⟩ : KW)) (hΦ _ hΘ) hTd hQd
        (PureSteps.plug (.appR (.val (.lam _)) .hole) hc) ?_
      have hM₀ : erwpK (ℍ := ℍ) KW.PostK (fun z => z.Θ.view z.c)
          (fun z => opTableK z.lo (tabN (ℍ := ℍ) (.eff m i q A B fin rc D) δ z))
          (fun z k _ v ρ => retN (ℍ := ℍ) (D.instT S) δ z.Θ k v ρ) (⟨Θ, c, lo⟩ : KW) j ls M ρ := by
        have h' := hM lo
        simp only [tabN_instT] at h'
        exact h'
      refine erwpK_bind_leI (V := KW.PostK) (fun _ _ _ h₁ h₂ => KW.PostK.trans h₁ h₂)
        (Φ := fun z : KW => z.Θ.view z.c) (Inv := fun z : KW => z.Θ.OK) hΦ
        (fun _ _ h => by rw [h]) (fun _ _ h hx => by rw [h]; exact hx) (fl := fun z : KW => z.lo)
        (T := fun z => tabN (ℍ := ℍ) (.eff m i q A B fin rc D) δ z)
        (fun _ _ h => tabLe_postK
          (fun z : KW => opTableK z.lo (tabN (ℍ := ℍ) (.eff m i q A B fin rc D) δ z)) h)
        (Q' := fun z k _ v ρ => retN (ℍ := ℍ) (D.instT S) δ z.Θ k v ρ)
        (.appR (.val (.lam _)) .hole) (fun _ => by simp [Kont.HasHnd])
        (fun _ => by simp [Kont.Catches])
        (fun z => tabN_ctxClosed_OK _ δ _ (fun _ => by simp [Kont.HasHnd]) (by simp [Kont.Catches]) z)
        (fun z m' i' en hT f y ρ' hy => (hDI z).wkI m' i' en hT f y ρ' hy) kg ?_ j hj
        (⟨Θ, c, lo⟩ : KW) hΘ ls M ρ hM₀
      rintro y hy k ls' w σ hk hw
      rw [← retNX_inst S δ hD.2.2, retNX_ans S _ hD.2.2] at hw
      obtain ⟨w', hs, h'⟩ := map_okN C g S δ kg T _ (hW δ hag) (effAns D) hR y.Θ k hk w σ hw
      have hTy : (opTableK y.lo (tabN (ℍ := ℍ) (.eff m i q A B fin rc D) δ y)).Down :=
        opTableK_downI (hDI y)
      refine erwpK_det (x := y) (Φ := fun z : KW => z.Θ.view z.c) (hΦ y hy) hTy hQd
        (fun μ => step1Only_plug (Head.beta μ _ w) rfl .hole) ?_
      have e : Expr.subst 0 w (.app (.app (.val (mapV (effAns D))) (.val ((hN C g).shift 1 0)))
          (.var 0)) = .app (.app (.val (mapV (effAns D))) (.val (hN C g))) (.val w) := by
        simp [Expr.subst, Val.val_shift, Expr.shift_zero,
          closed_subst (mapV_closed (effAns D)), subst_shift_succ]
      simp only [Kont.plug]
      rw [e]
      refine erwpK_pureSteps (x := y) (Φ := fun z : KW => z.Θ.view z.c) (hΦ y hy) hTy hQd hs
        (erwpK_val (KW.postK_refl y) ?_)
      show retN (ℍ := ℍ) (D.instT T) δ y.Θ k w' σ
      rw [← retNX_inst T δ hD.2.2, retNX_ans _ _ hD.2.2]
      exact h'
  | .amp D₁ D₂, hD, hfr, δ, hag, Θ, hΘ, c, j, hj, cv, M, ls, ρ, hc, hM =>
      ⟨cN_pureSteps (D₁.instT T) δ hΘ.1 c j ls ρ (nodeV_amp₁_steps D₁ D₂ _ cv)
        (node_okK C g S T δ₀ kg hW D₁ hD.1 (fun x hx => hfr x (Or.inl hx)) δ hag Θ hΘ c j hj _
          (.app M (.val (.inj₁ .unit))) ls ρ
          ((childV_steps cv _ rfl).trans (PureSteps.plug (.appL .hole _) hc)) hM.1),
       cN_pureSteps (D₂.instT T) δ hΘ.1 c j ls ρ (nodeV_amp₂_steps D₁ D₂ _ cv)
        (node_okK C g S T δ₀ kg hW D₂ hD.2 (fun x hx => hfr x (Or.inr hx)) δ hag Θ hΘ c j hj _
          (.app M (.val (.inj₂ .unit))) ls ρ
          ((childV_steps cv _ rfl).trans (PureSteps.plug (.appL .hole _) hc)) hM.2)⟩
  | .arr A D, hD, hfr, δ, hag, Θ, hΘ, _, j, hj, cv, M, ls, _, hc, hM =>
      fun c' k hk v ρv ρ' hcomp hv hcon =>
        cN_pureSteps (D.instT T) δ hΘ.1 c' k ls ρ' (nodeV_arr_steps A D _ cv v)
          (node_okK C g S T δ₀ kg hW D hD.2 hfr δ hag Θ hΘ c' k (le_trans hk hj) (childA cv v)
            (.app M (.val v)) ls ρ' ((childA_steps cv v).trans (PureSteps.plug (.appL .hole _) hc))
            (hM c' k hk v ρv ρ' hcomp hv hcon))
  | .all x b D, hD, hfr, δ, hag, Θ, hΘ, c, j, hj, cv, M, ls, ρ, hc, hM => fun α hα => by
      have hag' : ∀ y, VFree y T → δ₀.find? y = (δ.extend x α).find? y := by
        intro y hy
        have hxy : x ≠ y := fun h => hfr x (Or.inl rfl) (h ▸ hy)
        exact (hag y hy).trans (BoCa.Fig16.LogRel.find?_extend_ne δ α hxy).symm
      exact cN_pureSteps (D.instT T) (δ.extend x α) hΘ.1 c j ls ρ (nodeV_all_steps x b D _ cv)
        (node_okK C g S T δ₀ kg hW D hD (fun y hy => hfr y (Or.inr hy)) (δ.extend x α) hag' Θ hΘ
          c j hj (childA cv .unit) (.app M (.val .unit)) ls ρ
          ((childA_steps cv .unit).trans (PureSteps.plug (.appL .hole _) hc)) (hM α hα))
  | .top, hD, _, _, _, _, _, _, _, _, _, _, _, _, _, _
  | .nu _, hD, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => hD.elim

/-- **`nuOutK` at `SemJN`** (Core's `nuOutK_compatX`): the slot's value is `unfold step s`
(`codeRelN_etaN`); each observation runs the same path of the step (`etaN_obs`) and maps every
state `s′` to `unfold step s′`, in the code clause at the leaf's world (`node_okK`,
`etaN_codeRelN`).  `force x` at `νX. C` is `x` (`forceE`).  `[spec §68]` -/
theorem nuOutK_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {i : Nat} {C : CTy} {G S : VTy}
    (hC : C.NuOk) (hG : G.forceTy = some (.arr S (C.instT S))) (hS : C.BindsFresh S)
    (hGf : C.BindsFresh G) (h : Ctx.SoloP Γ i (codeTy C G S)) :
    SemJN (ℍ := ℍ) Δ Γ (.var i) (.comp (C.instT (codeTy C G S))) := by
  intro δ γ Θ c n ls ρ _ hΘ hc hlw hg
  obtain ⟨v, hv, hval⟩ := gN_soloP h (h.lt_of_liveWithin hlw) hg
  have he : substAll γ (.var i) = .val v := by
    show Expr.psub 0 γ (.var i) = _
    simp only [Expr.psub, if_neg (Nat.not_lt_zero i), Nat.sub_zero, hv, Val.shift_zero]
  show cN (ℍ := ℍ) (C.instT (codeTy C G S)) δ Θ c n ls (substAll γ (.var i)) ρ
  rw [he]
  obtain ⟨g, s, rfl, hgb, hs⟩ := codeRelN_etaN hval
  have hGU := vN_step_of_forceTy (ℍ := ℍ) (δ := δ) hG
  obtain ⟨-, hthunk⟩ := hgb Θ
  have hstep : cN (ℍ := ℍ) (C.instT S) δ Θ c n ls (.app (.val g) (.val s)) ρ :=
    hGU Θ n g _ hthunk Θ (LocTy.extR_refl Θ _) hΘ c (consistentX_empty c) ls c n le_rfl s ρ ρ
      (compS_empty_left ρ) hs hc
  have hW : ∀ δ', (∀ y, VFree y (codeTy C G S) → δ.find? y = δ'.find? y) → ∀ Θ' k w σ,
      k ≤ n → vN (ℍ := ℍ) S δ' Θ' k w σ → vN (ℍ := ℍ) (codeTy C G S) δ' Θ' k (etaN C g w) σ := by
    intro δ' hag Θ' k w σ hk hw
    have hS' : vN (ℍ := ℍ) S δ = vN (ℍ := ℍ) S δ' :=
      vN_congr S (fun y hy => hag y (Or.inl (Or.inr (Or.inl hy))))
    rw [← vN_congr _ hag]
    exact etaN_codeRelN hC hS hGU (fun Θ'' => vN_le hk (hgb Θ'')) (hS' ▸ hw)
  cases C with
  | amp C₁ C₂ =>
      have hN := node_okK (ℍ := ℍ) (.amp C₁ C₂) g S (codeTy (.amp C₁ C₂) G S) δ n hW (.amp C₁ C₂)
        hC.1.nuLeaf (codeTy_fresh hC hGf hS) δ (fun _ _ => rfl) Θ hΘ c n le_rfl (rootV g s) _ ls ρ
        (rootV_steps g s) hstep
      exact ⟨cN_pureSteps _ δ hΘ.1 c n ls ρ (etaN_obs _ g s _) hN.1,
        cN_pureSteps _ δ hΘ.1 c n ls ρ (etaN_obs _ g s _) hN.2⟩
  | _ => exact hC.1.elim

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
