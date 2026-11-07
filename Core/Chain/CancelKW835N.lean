import Core.Chain.ClaimKW835N
import Core.Chain.RulesKW835N

/-!
# The suspending lend at the typed world  `[spec §62]`

Core's `withbor2U_compatX` (`Core/EffBorrow.lean`) at a suspending row at `SemJN`
(`withbor2S_compat`), step for step, over `Cancel791N`'s and `ClaimKW835N`'s frames. The lender runs
at a floor no higher than the lend's lifetime (`KW.flr`, `erwpK_flr`), so every stop the lend's run
makes owes its continuation at a world whose location typing above the lend is the lender's
(`LocTy.ExtP.above_eq`): the claim's content, in the lend's family read above the lend, is a value
of the source's type at every world the lender's run reaches. The Mut Frame takes the callback as a
thunk of `cN` reads it (`erwpK_M_frameCR_cN`); the claim is consistent with the view of the world it
is raised at (`erwpK_claimXK`); the finaliser frame consumes it with `d` (`erwpK_ubindClaimRWK`,
`fin_claim`).
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
open BoCa.BoLo (Heap Kont Head ubindE)

/-- A row's table at the typed world does not read its base. -/
theorem tabN_effOf_base (S : Row) (R₁ R₂ : VTy) (δ : LSub) (x : KW) :
    tabN (ℍ := ℍ) (CTy.effOf S R₁) δ x = tabN (ℍ := ℍ) (CTy.effOf S R₂) δ x := by
  induction S with
  | nil => simp only [CTy.effOf, tabN]
  | cons o S ih => simp only [CTy.effOf, tabN, ih]

/-- An abortive entry of a `Row.Suspend` row's table is at a nonzero name. -/
theorem tabN_suspend_raise {S : Row} {x : LifeVar} {bnd : Lifetime.Life} (hS : S.Suspend x bnd)
    (R : VTy) (δ : LSub) :
    ∀ (z : KW) m i en, tabNK (ℍ := ℍ) (fun A δ Θ k v ρ => vN (ℍ := ℍ) A δ Θ k v ρ) id
      (CTy.effOf S R) δ z m i = some en → en.abort = true → m ≠ 0 := by
  intro z m i en h _
  rw [tabNK_vN, tabN_eq] at h
  obtain ⟨o, hf, -⟩ := tabF_effOf_some_find h
  obtain ⟨ho, hn, -⟩ := Row.find_mem hf
  rw [← hn]
  exact (hS o ho).2.1

/-- The finaliser `λ_. d ℓ` consumes the lend's claim at `SemJN`: `d`'s judgment at `Ref A ⊸ 1`,
applied to the cell owned again with its content in `A`'s family. -/
theorem fin_claim {A : VTy} {d : Expr} (hdc : closedAt 0 d = true)
    (hd : SemJN (ℍ := ℍ) LifeCtx.empty [] d (.val (.lolli (.ref A) .unit))) {δ δ' : LSub}
    (hδ : vN (ℍ := ℍ) A δ' = vN (ℍ := ℍ) A δ) {Θ : LocTy} (hΘ : Θ.OK)
    {c : Loc → Option Life} {l : Loc} {α : Life} {k : Nat} {ls : List SRec} {ρ : WRes}
    (h : claimR l α (fun j u r => vN (ℍ := ℍ) A δ' Θ j u r.1) k ρ) (hc : ConsistentX c ρ) :
    rwp (ℍ := ℍ) (Θ.view c) (fun _ _ v ρ' => v = Val.unit ∧ ρ' = PMap.empty) k ls
      (.app (.val (Val.lam (.app d (.val (Val.loc l))))) (.val .unit)) ρ := by
  have hΦ := LocTy.view_down hΘ.1 c
  obtain ⟨w, σ, hσ, hF, hcl⟩ := h
  have hF' : vN (ℍ := ℍ) A δ Θ k w σ := by rw [← hδ]; exact hF
  refine Hardest791.rwp_det'' (Q := fun _ v ρ' => v = Val.unit ∧ ρ' = PMap.empty) hΦ
    (fun μ => step1Only_plug (Head.beta μ _ Val.unit) rfl .hole) ?_
  have e : Kont.hole.plug (Expr.subst 0 Val.unit (.app d (.val (Val.loc l)))) =
      (Kont.appL .hole (Val.loc l)).plug d := by
    simp [Kont.plug, Expr.subst, subst_closedAt d (s := _) hdc (Nat.zero_le _), Val.loc]
  rw [e]
  refine rwp_bind hΦ _ ?_
  have hd0 := hd δ [] Θ c k ls PMap.empty (models_empty_any _) hΘ (consistentX_empty c) trivial rfl
  rw [show substAll [] d = d from psub_closedAt d [] hdc (Nat.zero_le 0)] at hd0
  have hfr := rwp_frame (fun _ τ => τ = ρ) (fun _ _ _ _ h => h) (compS_empty_left ρ)
    (rwp_of_erwp_empty (erwp_of_cN_ret hd0)) rfl
  refine rwp_mono_le (fun k' hk' ls' v τ hv => ?_) (rwp_consistentXV hfr hc)
  obtain ⟨⟨τ₁, τ₂, hcτ, hP, rfl⟩, hcτ', hvτ⟩ := hv
  have := hP Θ (LocTy.extR_refl Θ _) hΘ c (consistentX_left hcτ hcτ' hvτ) ls'
    c k' le_rfl (Val.loc l) τ₂ τ hcτ ⟨l, w, σ, rfl, hcl, vN_le hk' hF'⟩ hcτ'
  exact rwp_of_erwp_empty (erwp_of_cN_ret this)

/-- **A run at `cN`'s table from the lowered floor's world is a run from the world**
(`erwpK_flr` at `vN`). -/
theorem erwpK_flr_tabN {F : CTy} {δ : LSub} (a : Life) {Q : KW → PostN}
    (hQ : ∀ (x : KW) k ls v ρ, Q (x.flr a) k ls v ρ → Q x k ls v ρ) :
    ∀ n (x : KW) ls e ρ,
      erwpK (ℍ := ℍ) KW.PostK (fun z => z.Θ.view z.c)
        (fun z => opTableK z.lo (tabN (ℍ := ℍ) F δ z)) Q (x.flr a) n ls e ρ →
      erwpK (ℍ := ℍ) KW.PostK (fun z => z.Θ.view z.c)
        (fun z => opTableK z.lo (tabN (ℍ := ℍ) F δ z)) Q x n ls e ρ := by
  intro n x ls e ρ h
  have h' := erwpK_flr (ℍ := ℍ) (vr := fun A δ Θ k v ρ => vN (ℍ := ℍ) A δ Θ k v ρ) (F := F)
    (δ := δ) a hQ n x ls e ρ (by simpa only [tabNK_vN] using h)
  simpa only [tabNK_vN] using h'

/-- **The lender's worlds across a suspending lend at `α`**: the location typing valid, the floor
no higher than `α`, and the location typing above `α` the lend's. Every world a stop at a floor no
higher than the run's owes its continuation at keeps it (`LocTy.ExtP.above_eq`). -/
def LendInv (Θ₀ : LocTy) (α : Life) (z : KW) : Prop :=
  z.Θ.OK ∧ z.lo ≤ α ∧ z.Θ.above α = Θ₀.above α

theorem lendInv_owed {Θ₀ : LocTy} {α : Life} (x : KW) (hx : LendInv Θ₀ α x) (f : Life)
    (hf : f ≤ x.lo) (y : KW) (ρ : WRes) (hy : x.Owed f y ρ) : LendInv Θ₀ α y :=
  ⟨hy.2.1, le_trans hy.2.2.2.1 hx.2.1, (hy.1.above_eq (le_trans hf hx.2.1)).trans hx.2.2⟩

/-- **`withbor (2)` at a suspending row is a value of `!` its type, at `SemJN`**:
`withborU d`, at
`Ref A ⊸ (∀'x ⊏ @bnd. Mut 'x A ⊸ F_Σ(['x] B)) ⊸ F_Σ(Ref A ⊗ B)` with `Σ` a `Row.Suspend x bnd`
row, cleanup that performs included.

At the world `Θ` and view `c`, at every floor, the source cell `ℓ ↦ own(w₀) ● σ₀` is lent at a
lifetime `α` with `FoldInv α` at `Θ` (`LocTy.exists_foldInv`) and below the bound, the side
condition's `@bδ` and the callback's stratum (`vN_outlivesLe`). The lender runs at the floor no
higher than `α` (`erwpK_flr`), at the worlds `LendInv Θ α`. The callback runs at the lend's world
`x.lend ℓ α (famL α 𝒱⟦A⟧ Θ)` from the borrow (`lend_mutL`), consistent (`consistentX_compS`), as
the thunk `cN` reads (`erwpK_M_frameCR_cN`); the lender's run carries the view's consistency to its
claim (`erwpK_claimXK`); the finaliser frame `then b. (ℓ, b) unwind d ℓ` consumes the claim with `d`
at the world it is raised at (`erwpK_ubindClaimRWK`, `fin_claim`), the claim's content a value of
`A` there (`vN_above` at `LendInv`). The callback's result `['x] B` returns to the world without the
lend by `vN_local`.

Premises those of the rule; `hd` is `d`'s judgment at `SemJN`. -/
theorem withbor2S_compat {x : LifeVar} {bnd : Lifetime.Life} {A B : VTy} {S : Row} {d : Expr}
    (hbnd : LifeCtx.empty.Defines bnd)
    (hO : ∃ b, LifeCtx.empty.Defines b ∧ VOutlivesLe LifeCtx.empty b A)
    (hA : ¬ VFree x A) (hB : ¬ VFree x B) (hS : S.Suspend x bnd) (hdc : closedAt 0 d = true)
    (hd : SemJN (ℍ := ℍ) LifeCtx.empty [] d (.val (.lolli (.ref A) .unit))) (δ : LSub)
    (Θ₀ : LocTy) (n : Nat) :
    vN (ℍ := ℍ) (.bang (withbor2UTy x bnd A B S)) δ Θ₀ n (withborUV d) PMap.empty := by
  refine ⟨rfl, fun Θ _ hΘ c₁ _ ls => ?_⟩
  intro c₂ k hk u ρv ρu hc hu _
  obtain rfl := eq_of_compS_empty_left hc
  intro c k' hk' f ρf ρ'' hc' hf hcon
  obtain ⟨l, w₀, σ₀, rfl, hcl, hw₀⟩ := vN_le hk' hu
  rw [cN_effOf]
  intro lo
  refine erwpK_of_valid fun hv'' => ?_
  set Fo := CTy.effOf S (.tensor (.ref A) B) with hFo
  set Qo : KW → PostN := fun z k _ v ρ => vN (ℍ := ℍ) (.tensor (.ref A) B) δ z.Θ k v ρ with hQo
  have hQoD : ∀ z, (Qo z).Down := fun z k _ v ρ h => vN_down _ δ z.Θ k v ρ h
  -- the parts of the start are consistent with the view, and miss `ℓ` in their exclusive walks
  have hvu : ResU.Valid ρu := (ResU.Valid.split hc' hv'').1
  have hcf : ConsistentX c ρf := consistentX_right hc' hcon hv''
  have hcσ : ConsistentX c σ₀ := consistentX_right hcl (consistentX_left hc' hcon hv'') hvu
  have hko : (CellU.ownOf (Loc := Loc) w₀).kind ≠ Kind.imm := by simp
  have hown : ρu.get l = some (CellU.ownOf w₀) :=
    (ResU.CompS.get_left_of_ne_imm hcl (ResU.single_get_self _ _) hko).2
  -- the lend's lifetime: `FoldInv` at `Θ`, below the bound, the source's content's stratum and
  -- the callback's
  obtain ⟨γ, hγ⟩ := hbnd δ (models_empty_any _)
  -- `[TR]` 6.60 at the side condition `⊢ A ⊒ @b`: every value of `A` below `@bδ`
  obtain ⟨b, hdef, hOb⟩ := hO
  obtain ⟨βP, hβP⟩ : ∃ β : Life, b.interp δ = some β := hdef δ (models_empty_any _)
  obtain ⟨βf, hβf⟩ := ResU.exists_stratum ρf
  obtain ⟨α, hαle, hfold⟩ := LocTy.exists_foldInv hΘ.2 (↓(βP ⊓ βf ⊓ γ))
  have hfr : Θ.Fresh α := hfold.1
  have hαlt : α < βP ⊓ βf ⊓ γ := lt_of_le_of_lt hαle (Life.down_sqsubset _)
  have hαP : α < βP := lt_of_lt_of_le hαlt (inf_le_left.trans inf_le_left)
  have hunif : ∀ (Θ' : LocTy) (j : Nat) (u : Val) (r : WRes), vN (ℍ := ℍ) A δ Θ' j u r →
      r.InStratum α :=
    vN_outlivesLe (models_empty_any _) hβP hαP hOb
  have houtP : σ₀.InStratum α := hunif Θ k' w₀ σ₀ hw₀
  have houtf : ρf.InStratum (↓α) := hβf.mono
    ((Life.down_sqsubset α).le.trans (hαlt.le.trans (inf_le_left.trans inf_le_right)))
  have hLt : LtLife δ bnd α := ⟨γ, hγ, lt_of_lt_of_le hαlt inf_le_right⟩
  set δ' := δ.extend x α with hδ'
  have hAδ : vN (ℍ := ℍ) A δ' = vN (ℍ := ℍ) A δ := vN_extend_of_not_free hA δ α
  have hBδ : vN (ℍ := ℍ) B δ' = vN (ℍ := ℍ) B δ := vN_extend_of_not_free hB δ α
  set P : CPredL := fun Θ' j u r => vN (ℍ := ℍ) A δ' Θ' j u r with hP
  set Fam : Nat → Val → SPropS Loc Val α := famL α P Θ with hFam
  have hFamD : DownFam α Fam := vN_fam_down A δ' α Θ
  have hwit : Fam k' w₀ ⟨σ₀, houtP⟩ := (vN_above A δ' Θ houtP).mpr (by rw [hAδ]; exact hw₀)
  -- the content of the lend's family is a value of `A` at every world `LendInv` holds at
  have hFamV : ∀ (z : KW), LendInv Θ α z → ∀ j w σ (hσ : σ.InStratum α), Fam j w ⟨σ, hσ⟩ →
      vN (ℍ := ℍ) A δ' z.Θ j w σ := by
    intro z hz j w σ hσ hF
    have hF' : vN (ℍ := ℍ) A δ' (Θ.above α) j w σ := hF
    rw [← hz.2.2] at hF'
    exact (vN_above A δ' z.Θ hσ).mp hF'
  -- the callback's world and view
  set Θ' := Θ.add l α Fam with hΘ'
  set c' := setLife c l α with hc'def
  have hOK' : Θ'.OK := by
    obtain ⟨N, hN⟩ := hΘ.2
    exact ⟨LocTy.down_add hΘ.1 l hFamD, ⟨min N (↓α), LocTy.fresh_add hN (min_le_left _ _)
      (lt_of_le_of_lt (min_le_right _ _) (Life.down_sqsubset α)) l Fam⟩⟩
  have hcf' : ConsistentX c' ρf := consistentX_setLife hcf (exS_none_of_part hc' hv'' hown hko) α
  have hcσ' : ConsistentX c' σ₀ :=
    consistentX_setLife hcσ (exS_none_of_part hcl hvu (ResU.single_get_self _ _) hko) α
  set Rc := claimR l α Fam with hRc
  have hFS : Fo.SuspendC x bnd := suspendC_effOf hS _
  -- the lender at the floor no higher than `α`
  set x₁ : KW := KW.flr α ⟨Θ, c, lo⟩ with hx₁
  have hx₁I : LendInv Θ α x₁ := ⟨hΘ, min_le_right _ _, rfl⟩
  suffices hx₁ : erwpK (ℍ := ℍ) KW.PostK (fun z => z.Θ.view z.c)
      (fun z => opTableK z.lo (tabN (ℍ := ℍ) Fo δ z)) Qo x₁ k' ls
      (((forceE (CTy.arr (.ref A) (CTy.arr (cbUTy x bnd (.mut (.var x) A) B S) Fo))
        (withborUV d).1).app (.val (Val.loc l))).app (.val f)) ρ'' by
    have h := erwpK_flr (ℍ := ℍ) (vr := fun A δ Θ k v ρ => vN (ℍ := ℍ) A δ Θ k v ρ) (F := Fo)
      (δ := δ) α (Q := Qo) (fun _ _ _ _ _ h => h) k' ⟨Θ, c, lo⟩ ls _ ρ''
      (by simpa only [tabNK_vN] using hx₁)
    simpa only [tabNK_vN] using h
  have hΦ₁ : (x₁.Θ.view x₁.c).Down := LocTy.view_down hΘ.1 c
  have hTd₁ : (opTableK x₁.lo (tabN (ℍ := ℍ) Fo δ x₁)).Down :=
    opTableK_downI (tabN_downI_OK Fo δ x₁)
  refine erwpK_det (Φ := fun z : KW => z.Θ.view z.c) (x := x₁) hΦ₁ hTd₁ hQoD
    (fun μ => step1Only_plug (Head.beta μ _ (Val.loc l)) rfl (.appL .hole f)) ?_
  refine erwpK_det (Φ := fun z : KW => z.Θ.view z.c) (x := x₁) hΦ₁ hTd₁ hQoD
    (fun μ => step1Only_plug (Head.beta μ _ f) rfl .hole) ?_
  have e₃ : Kont.hole.plug (Expr.subst 0 f (Expr.subst (0 + 1) (Val.shift 1 0 (Val.loc l))
        (thenE ((Expr.var 2).pair (Expr.var 0)) (d.app (Expr.var 2))
          (((Expr.var 0).app (Expr.val Val.unit)).app (Expr.var 1))))) =
      ubindE (.pair (NFv l) (DFv d l)) (.app (.app (.val f) (.val .unit)) (.val (Val.loc l))) := by
    simp [Kont.plug, Expr.subst, Expr.shift, thenE, ubindE, NFv, DFv, Val.shift, Val.pair,
      Val.loc, Val.lam, Expr.val, Val.prim,
      subst_closedAt d (s := _) hdc (Nat.zero_le _)]
  rw [e₃]
  -- the lender's post: at a world whose location typing above `α` is the lend's, the pair
  set Ql : KW → PostN := fun z k _ b ρ => z.Θ.above α = Θ.above α →
    vN (ℍ := ℍ) (.tensor (.ref A) B) δ z.Θ k (Val.pair (Val.loc l) b) ρ with hQl
  -- the Mut Frame, the callback read as `cN` reads it
  have hM := erwpK_M_frameCR_cN (ℍ := ℍ) hbnd hLt hFamD hFS (Q := Ql)
    (Qc := fun z k _ v ρ => vN (ℍ := ℍ) (.box (.var x) B) δ' z.Θ k v ρ) ?_ k' k' le_rfl x₁ hfold
    ls (.app (.app (.val f) (.val .unit)) (.val (Val.loc l))) w₀ σ₀ ρu ρf ρ'' houtP houtf
    (Fam k') (fun _ _ h => h) hwit hcl hc' ?_
  · -- the claim consistent, the finaliser frame consuming it at the world it is raised at
    have hM' := erwpK_claimXK k' x₁ ls _ ρ'' hcon hM
    have hfin := erwpK_ubindClaimRWK (ℍ := ℍ) valRelOK_vN (RW := claimXK Rc)
      (Inv := LendInv Θ α) (fun z hz => LocTy.view_down hz.1.1 z.c) lendInv_owed
      (F := Fo) (δ := δ) (tabN_suspend_raise hS _ δ) (NFv l) (DFv d l) ?_ hQoD ?_ k' x₁ hx₁I ls
      _ ρ'' hM'
    · simpa only [tabNK_vN] using hfin
    · rintro z hz j ls' ρ ⟨⟨w, σ, hσ, hF, hclm⟩, hcR⟩
      exact fin_claim hdc hd hAδ hz.1 ⟨w, σ, hσ, hFamV z hz j w σ hσ hF, hclm⟩ hcR
    · intro z hz j ls' bv ρ hq
      have hTdz : (opTableK z.lo (tabNK (ℍ := ℍ) (fun A δ Θ k v ρ => vN (ℍ := ℍ) A δ Θ k v ρ)
          id Fo δ z)).Down := opTableK_downI (tabNK_downI valRelOK_vN id Fo δ z)
      refine erwpK_det (Φ := fun z : KW => z.Θ.view z.c) (x := z) (LocTy.view_down hz.1.1 z.c)
        hTdz hQoD
        (fun μ => step1Only_plug (Head.beta μ _ bv) rfl .hole) ?_
      simp [Kont.plug, Expr.subst]
      exact erwpK_val (KW.postK_refl z) (v := Val.pair (Val.loc l) bv) (hq hz.2.2)
  · -- the callback's post: the cell handed back, the pair at the lender's world
    intro z j ls' bv ρ' hb
    obtain ⟨β, hβ, hbB, hst⟩ := hb
    rw [interp_ext_self] at hβ
    cases Option.some.inj hβ
    refine ⟨hst, fun w Y hY σ ⟨hσ, hFσ⟩ Z hZ habove => ?_⟩
    obtain ⟨Wc, hWc, hZ'⟩ :=
      (ResU.CompS.assoc ρ' (ResU.single l (CellU.ownOf w)) σ Z).mpr ⟨Y, hY, hZ⟩
    have hwσ : vN (ℍ := ℍ) A δ z.Θ j w σ := by
      rw [← hAδ]
      have hF' : vN (ℍ := ℍ) A δ' (Θ.above α) j w σ := hFσ
      rw [← habove] at hF'
      exact (vN_above A δ' z.Θ hσ).mp hF'
    have hbB' : vN (ℍ := ℍ) B δ z.Θ j bv ρ' :=
      vN_local B δ z.Θ l α Fam j bv ρ' hst (by rw [← hBδ]; exact hbB)
    exact ⟨Val.loc l, bv, Wc, ρ', rfl, ResU.CompS.comm hZ', ⟨l, w, σ, rfl, hWc, hwσ⟩, hbB'⟩
  · -- the callback, at the lend's world and view, from the borrow
    intro BM hBM
    have h1 := (hf Θ' ((LocTy.extA_add hfr l Fam).extR ρf) hOK' c' hcf' ls) α hLt
    have hcell : vN (ℍ := ℍ) (.mut (.var x) A) δ' Θ' k' (Val.loc l)
        (ResU.single l (CellU.mutOf α w₀ σ₀ houtP (Fam k') hwit)) :=
      ⟨α, interp_ext_self δ x α, α, le_rfl, lend_mutL Θ l α P le_rfl houtP hwit,
        fun Θ'' j u r h => hunif Θ'' j u r (by rw [← hAδ]; exact h)⟩
    have hcBM : ConsistentX c' BM := consistentX_compS hBM hcf'
      (consistentX_single_mut hcσ' (by simp [hc'def, setLife]))
    have h2 := h1 c' k' le_rfl (Val.loc l) _ BM hBM hcell hcBM
    rw [cN_effOf] at h2
    have h3 := h2 α
    simp only [tabN_effOf_base S (.box (.var x) B) (.tensor (.ref A) B)] at h3
    exact h3

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
