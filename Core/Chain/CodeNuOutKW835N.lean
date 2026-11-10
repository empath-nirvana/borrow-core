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
observation is read with `U X` at the code type's own relation instead: `node_okP` at
`P = 𝒱⟦Code⟨…⟩ (νX. C)⟧δ`, every leaf mapped into it (`map_okN` at the code type), each rest
`unfold step s′` in the code clause at the leaf's world (`etaN_codeRelN` at the state's world and
index), and that unfolding is `𝒞⟦C[Code⟨…⟩ (νX. C)/X]⟧` (`cBNP_unroll`).
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

/-- **`𝒞⟦C⟧` is closed under a pure step backwards** (`cBNP_step` at the relation itself). -/
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
      (cN_nu_unfold hS δ Θ c n ls _ ρ).mpr (cBNP_step _ (thunkRN_down (nuCand_down C δ)) C δ Θ hΘ c n ls ρ _ _
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

/-- **`nuOutK` at `SemJN`** (Core's `nuOutK_compatX`): the slot's value is `unfold step s`
(`codeRelN_etaN`); each observation runs the same path of the step (`etaN_obs`) and maps every
state `s′` to `unfold step s′`, in the code clause at the leaf's world (`node_okP` at the code
type's relation, `etaN_codeRelN`), read at the unrolled type by `cBNP_unroll`.  `force x` at `νX. C` is `x` (`forceE`).  `[spec §68]` -/
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
      k ≤ n → vN (ℍ := ℍ) S δ' Θ' k w σ → vN (ℍ := ℍ) (codeTy C G S) δ Θ' k (etaN C g w) σ := by
    intro δ' hag Θ' k w σ hk hw
    have hS' : vN (ℍ := ℍ) S δ = vN (ℍ := ℍ) S δ' :=
      vN_congr S (fun y hy => hag y (Or.inl (Or.inr (Or.inl hy))))
    exact etaN_codeRelN hC hS hGU (fun Θ'' => vN_le hk (hgb Θ'')) (hS' ▸ hw)
  have hP : ∀ δ' : LSub, (∀ y, VFree y (codeTy C G S) → δ.find? y = δ'.find? y) →
      vN (ℍ := ℍ) (codeTy C G S) δ = vN (ℍ := ℍ) (codeTy C G S) δ' := fun _ hag => vN_congr _ hag
  have hfr := codeTy_fresh hC hGf hS
  have hN := node_okP (ℍ := ℍ) C g S n (codeTy C G S) _ (vN_down (codeTy C G S) δ) _ δ hW C hC.1.nuLeaf hfr δ
    (fun _ _ => rfl) Θ hΘ c n le_rfl (rootV g s) _ ls ρ (rootV_steps g s) hstep
  rw [cBNP_unroll _ _ _ δ hP hC.1.nuLeaf hfr δ (fun _ _ => rfl)] at hN
  cases C with
  | amp C₁ C₂ =>
      exact ⟨cN_pureSteps _ δ hΘ.1 c n ls ρ (etaN_obs _ g s _) hN.1,
        cN_pureSteps _ δ hΘ.1 c n ls ρ (etaN_obs _ g s _) hN.2⟩
  | _ => exact hC.1.elim

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
