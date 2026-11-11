import Core.CodeRules

/-!
# Core — `unfold` at the step's code and `νX. C` read at its code  `[spec §68]`

The two rules of K4, at `SemV`/`SemC`:

* `unfoldK_compatX`: `unfold : !G ⊸ !Code⟨hCode C; !G ⊗ 1⟩ (S ⊸ F Code⟨etaCode C; !G ⊗ (S ⊗ 1)⟩
  (νX. C))`, `G` forced at `S ⊸ C[S/X]` (`U(S ⊸ C[S/X])` or a code type of it). `unfold step` is
  `hCode C` closed by `[step]` (`hN_code`); `unfold step s` is in the code clause by `etaN_codeRel`.
* `nuOutK_compatX`: `x : Code⟨etaCode C; !G ⊗ (S ⊗ 1)⟩ (νX. C)` ⟹ `x : C[Code⟨…⟩ (νX. C)/X]`.
  `nuOutK_step` puts `x` in one unfolding of `νX. C` at the code's candidate `codeCand`; the
  unrolling at the code type (`cB_unrollK`) reads that unfolding as `𝒞⟦C[Code⟨…⟩ (νX. C)/X]⟧`.

**The unrolling at a code type.** `U X` read at `codeCand C G S δ₀` is `𝒱⟦Code⟨…⟩ (νX. C)⟧δ`
(`nuP_codeCand`), at a `δ` agreeing with `δ₀` on the code type's free variables: the candidate's
Kripke quantifier over the list is `vC_local`'s. One unfolding does not read the type the
environment gives `X` (`cB_poly_ty`), so at a polynomial leaf `nuEnv C (codeCand …)` is `X ↦ the
code type` (`vCE_codeEnv`, the analogue of `vC_inst_envS` and `vCE_nuEnv_at`), and one unfolding
is `𝒞⟦D[Code⟨…⟩ (νX. C)/X]⟧` (`cB_unrollK`, the analogue of `cB_unroll`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### Types and codes -/

/-- **`unfold step s`'s type**, `Code⟨etaCode C; !G ⊗ (S ⊗ 1)⟩ (νX. C)`.  `[spec §68]` -/
abbrev codeTy (C : CTy) (G S : VTy) : VTy := .code (etaCode C) (etaEnv G S) (.nu C)

/-- **The code of `unfold step`**: `λs. λo. self x₀ s o`, the step `x₀` captured.  `[spec §68]` -/
def hCode (C : CTy) : Expr :=
  .lam (.val (.lam (.app (.app (.app (.val (selfNu C)) (.var 2)) (.var 1)) (.var 0))))

/-- The environment type of `hCode`: the step at `!G`.  `[spec §68]` -/
abbrev hEnv (G : VTy) : VTy := .tensor (.bang G) .unit

/-- **`unfoldK`'s type**, `!G ⊸ !Code⟨hCode C; !G ⊗ 1⟩ (S ⊸ F Code⟨etaCode C; !G ⊗ (S ⊗ 1)⟩
(νX. C))`.  `[spec §68]` -/
abbrev unfoldKTy (C : CTy) (G S : VTy) : VTy :=
  .lolli (.bang G) (.bang (.code (hCode C) (hEnv G) (.arr S (.ret (codeTy C G S)))))

theorem hCode_occs (C : CTy) : Expr.occs 0 (hCode C) = [0] := by
  simp [hCode, Expr.occs, occs_eq_nil_of_closedAt _ 2
    (closedAt_mono _ (selfNu_closed C) (Nat.zero_le 2))]

/-- `hCode C` is its own code: its one capture is `0`.  `[spec §68]` -/
theorem hCode_capNorm (C : CTy) : Expr.capNorm (hCode C) = hCode C := by
  refine Expr.ren_eq_self _ _ 0 (fun i hi => ?_)
  rw [hCode_occs] at hi
  simp only [Expr.capIdx, Expr.capVars, hCode_occs]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  subst hi; rfl

/-- **`unfold step` is its code closed by `[step]`.**  `[spec §68]` -/
theorem hN_code (C : CTy) (g : Val) : (hN C g).1 = Expr.psub 0 [g] (hCode C) := by
  simp [hN, hCode, Expr.psub, Val.lam, psub_closedAt _ _ (selfNu_closed C) (Nat.zero_le 2)]

/-- A type forced at `S ⊸ C[S/X]` erases to `U(S ⊸ C[S/X])`. -/
theorem step_of_forceTy {G S : VTy} {C : CTy} (hG : G.forceTy = some (.arr S (C.instT S)))
    {δ : LSub} : ∀ ls v ρ, vC true G ls δ v ρ → vC true (.thunk (.arr S (C.instT S))) ls δ v ρ :=
  fun _ _ _ h => vC_thunk_of_forceTy hG h

/-- No leaf binder of `C` is free in the code type when none is free in `G` and `S`. -/
theorem codeTy_fresh {C : CTy} (hC : C.NuOk) {G S : VTy} (hG : C.BindsFresh G)
    (hS : C.BindsFresh S) : ∀ x, C.LeafBinds x → ¬ VFree x (codeTy C G S) := by
  intro x hx hf
  simp only [VFree, CFree, or_false] at hf
  rcases hf with (hg | hs) | hc
  · exact hG x hx hg
  · exact hS x hx hs
  · exact hC.2 x hx hc

/-! ### `unfoldK` -/

/-- **`unfoldK`'s compatibility**: `unfold_compatX`'s proof at the step's code.  `unfold step` is
`hCode C` closed by `[step]` with `(step, ())` in `!G ⊗ 1` at `∅`; `unfold step s` is in the code
clause at `etaCode C` with environment `[step, s]` (`etaN_codeRel`), the step read at `U` through
`G`'s code clause (`vC_thunk_of_forceTy`).  `[spec §68]` -/
theorem unfoldK_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {C : CTy} (hC : C.NuOk) {G S : VTy}
    (hG : G.forceTy = some (.arr S (C.instT S))) (hS : C.BindsFresh S) (hΓ : Ctx.DeadP Γ) :
    SemV Δ Γ (.val (unfoldV C)) (unfoldKTy C G S) := by
  intro δ γ ls ρ _ hg₀
  have hρ : ρ = PMap.empty := gSepC_deadP hΓ (gDenC_iff.mp hg₀).2
  subst hρ
  rw [substAll_closed (unfoldV_closed C)]
  refine wpTS_val _ _ _ _ ?_
  intro ls₁ _ g ρ₁ τ₀ hv₁ hcomp
  have hρ₁ : ρ₁ = PMap.empty := hv₁.1
  subst hρ₁
  have hg : ∀ ls, vC true (.bang G) ls δ g PMap.empty := fun ls' =>
    vC_local true _ (ext_empty ls₁ ls') hv₁
  rw [eq_of_compS_empty_left hcomp]
  refine wpTS_lolli _ _ g _ _ ?_
  rw [unfoldV_subst]
  refine wpTS_val _ _ _ _ ⟨rfl, ⟨[g], hN_code C g, ?_⟩, ?_⟩
  · exact ⟨g, .unit, PMap.empty, PMap.empty, compS_empty_left _, ⟨rfl, rfl⟩,
      PMap.empty, PMap.empty, compS_empty_left _, hg ls₁, ⟨rfl, rfl⟩⟩
  · intro ls₂ _ s ρ₂ τ hs hc
    rw [eq_of_compS_empty_left hc]
    refine wpTS_lolli _ _ s _ _ ?_
    rw [hN_subst]
    exact wpTS_val _ _ _ _ (etaN_codeRel hC hS (step_of_forceTy hG) hg hs)

/-! ### The unrolling at a code type -/

/-- **`U X` at the code's candidate is `𝒱⟦Code⟨etaCode C; !G ⊗ (S ⊗ 1)⟩ (νX. C)⟧`**, the candidate
at `δ₀` and the type read at `δ`, agreeing on the code type's free variables.  `[spec §68]` -/
theorem nuP_codeCand {C : CTy} {G S : VTy} {δ₀ δ : LSub}
    (hag : ∀ y, VFree y (codeTy C G S) → δ₀.find? y = δ.find? y) :
    nuP (codeCand C G S δ₀) = fun b ls => vC b (codeTy C G S) ls δ := by
  funext b ls v
  cases b with
  | false => rfl
  | true =>
      funext ρ
      refine propext ⟨fun h => ?_, fun h ls' hext => ?_⟩
      · obtain ⟨v', he, hv'⟩ := h ls (Ext.refl _ _)
        obtain rfl : v = v' := Val.ext he
        rw [← vC_congr _ hag true ls]
        exact hv'
      · refine ⟨v, rfl, ?_⟩
        show vC true (codeTy C G S) ls' δ₀ v ρ
        rw [vC_congr _ hag true ls']
        exact vC_local true _ hext h

/-- **At a polynomial type, `X` at the code's candidate is `X` read as the code type** (the
analogue of `vC_inst_envS` and `vCE_nuEnv_at` at a code type).  `[spec §68]` -/
theorem vCE_codeEnv {C : CTy} {G S : VTy} {δ₀ δ : LSub}
    (hag : ∀ y, VFree y (codeTy C G S) → δ₀.find? y = δ.find? y) {A : VTy} (hA : A.Poly)
    (b : Bool) (ls : List SRec) :
    vCE (some (nuEnv C (codeCand C G S δ₀))) b A ls δ = vC b (VTy.inst (codeTy C G S) A) ls δ := by
  rw [vC_inst_envS, nuEnv, vCE_poly_ty _ _ (codeTy C G S) _ A hA b, nuP_codeCand hag]
  rfl

/-- The answer of an effectful observation at the code's candidate is the answer at the code
type's unrolling (the analogue of `effRetE_unroll`). -/
theorem effRetE_unrollK {C : CTy} {G S : VTy} {δ₀ δ : LSub}
    (hag : ∀ y, VFree y (codeTy C G S) → δ₀.find? y = δ.find? y) :
    ∀ {D : CTy}, D.EffLeaf →
    effRetE (some (nuEnv C (codeCand C G S δ₀))) D δ = effRet (D.instT (codeTy C G S)) δ
  | .ret A, hA => by
      funext ls v
      simp only [effRetE, effRet, CTy.instT]
      rw [vCE_codeEnv hag hA]
  | .eff _ _ _ _ _ _ _ D, hD => by
      simp only [effRetE, effRet, CTy.instT]
      exact effRetE_unrollK hag (D := D) hD.2.2

/-- **One unfolding at the code's candidate is `𝒞⟦D[Code⟨etaCode C; !G ⊗ (S ⊗ 1)⟩ (νX. C)/X]⟧`**
(the analogue of `cB_unroll` at a code type), the candidate at `δ₀` and the tree read at `δ`,
agreeing on the code type's free variables.  Under a `∀'x` leaf the tree is read at
`δ[x ↦ α]`, which still agrees with `δ₀` there because `'x` is not free in the code type.
`[spec §68]` -/
theorem cB_unrollK (C : CTy) (G S : VTy) (δ₀ : LSub) : ∀ {D : CTy}, D.NuLeaf →
    (∀ x, D.LeafBinds x → ¬ VFree x (codeTy C G S)) → ∀ (δ : LSub),
    (∀ y, VFree y (codeTy C G S) → δ₀.find? y = δ.find? y) → ∀ (ls : List SRec),
    cB (some (nuEnv C (codeCand C G S δ₀))) D ls δ = cC (D.instT (codeTy C G S)) ls δ
  | .ret A, hA, _, δ, hag, ls => by
      funext e
      show wpTS ls e (fun ls'' => vCE _ true A ls'' δ)
        = wpTS ls e (fun ls'' => vC true (VTy.inst _ A) ls'' δ)
      simp only [vCE_codeEnv hag hA]
  | .amp D₁ D₂, hD, hfr, δ, hag, ls => by
      funext e ρ
      show (cB _ D₁ ls δ _ ρ ∧ cB _ D₂ ls δ _ ρ)
        = (cC (D₁.instT _) ls δ _ ρ ∧ cC (D₂.instT _) ls δ _ ρ)
      rw [cB_unrollK C G S δ₀ hD.1 (fun x hx => hfr x (Or.inl hx)) δ hag ls,
        cB_unrollK C G S δ₀ hD.2 (fun x hx => hfr x (Or.inr hx)) δ hag ls]
  | .eff n i q A B fin rc D, hD, _, δ, hag, ls => by
      funext e
      show effWp _ _ _ ls e = effWp _ _ _ ls e
      rw [effRetE_unrollK hag (D := D) hD.2.2, ← effTab_instT (codeTy C G S) δ D,
        ← CTy.divAt_instT (codeTy C G S) (.eff n i q A B fin rc D)]
      rfl
  | .arr A D, hD, hfr, δ, hag, ls => by
      funext e ρ
      show (∀ v, (vC true A ls δ v ─⋆ cB _ D ls δ (.app e (.val v))) ρ)
        = (∀ v, (vC true A ls δ v ─⋆ cC (D.instT _) ls δ (.app e (.val v))) ρ)
      rw [cB_unrollK C G S δ₀ hD.2 hfr δ hag ls]
  | .all x c D, hD, hfr, δ, hag, ls => by
      funext e ρ
      have hag' : ∀ α, ∀ y, VFree y (codeTy C G S) → δ₀.find? y = (δ.extend x α).find? y := by
        intro α y hy
        have hxy : x ≠ y := fun h => hfr x (Or.inl rfl) (h ▸ hy)
        exact (hag y hy).trans (find?_extend_ne δ α hxy).symm
      show (∀ α, (⌜LtLife δ c α⌝ ─⋆ cB _ D ls (δ.extend x α) (.app e (.val .unit))) ρ)
        = (∀ α, (⌜LtLife δ c α⌝ ─⋆ cC (D.instT _) ls (δ.extend x α) (.app e (.val .unit))) ρ)
      refine propext (forall_congr' fun α => ?_)
      rw [cB_unrollK C G S δ₀ (D := D) hD (fun y hy => hfr y (Or.inr hy)) (δ.extend x α)
        (hag' α) ls]
  | .top, hD, _, _, _, _ | .nuSys _ _ _, hD, _, _, _, _ => hD.elim

/-! ### `nuOutK` -/

/-- **`nuOutK`'s compatibility**: a value of `Code⟨etaCode C; !G ⊗ (S ⊗ 1)⟩ (νX. C)` is in one
unfolding of `νX. C` at the code's candidate (`nuOutK_step`), which is
`𝒞⟦C[Code⟨etaCode C; !G ⊗ (S ⊗ 1)⟩ (νX. C)/X]⟧` (`cB_unrollK`).  `force x` at `νX. C` is `x`
(`forceE`).  `[spec §68]` -/
theorem nuOutK_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {i : Nat} {C : CTy} {G S : VTy} (hC : C.NuOk)
    (hG : G.forceTy = some (.arr S (C.instT S))) (hS : C.BindsFresh S) (hGf : C.BindsFresh G)
    (h : Ctx.SoloP Γ i (codeTy C G S)) :
    SemC Δ Γ (.var i) (C.instT (codeTy C G S)) := by
  intro δ γ ls ρ _ hg
  obtain ⟨hlen, hs⟩ := gDenC_iff.mp hg
  obtain ⟨v, hv, hval⟩ := gSepC_soloP h (h.lt_of_liveWithin hlen) hs
  have he : substAll γ (.var i) = .val v := by
    show Expr.psub 0 γ (.var i) = _
    simp only [Expr.psub, if_neg (Nat.not_lt_zero i), Nat.sub_zero, hv, Val.shift_zero]
  rw [he]
  have hstep := nuOutK_step hC hS (step_of_forceTy hG) ls (.val v) ρ ⟨v, rfl, hval⟩
  rw [← cB_unrollK C G S δ hC.1.nuLeaf (codeTy_fresh hC hGf hS) δ (fun _ _ => rfl) ls]
  exact hstep

end BoCa.Fig16.LogRel.Core

end
