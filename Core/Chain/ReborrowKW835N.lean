import Core.Chain.CancelKW835N

/-!
# The suspending reborrow at the typed world  `[spec §62]`

Core's `withbor3U_compatX` at a suspending row at `SemJN` (`withbor3S_compat`), step for step,
over `Reborrow791N`'s frames: the anti-frame at the source's own
entry (`erwpK_M_antiFrameCR_tab`, its invariant `KW.SealInv`), the opened cell lent at a lifetime
`α` below the source's (`erwpK_M_frameCRG_cN`, the guarded Mut Frame with the callback read as a
thunk of `cN`), the lender at the floor no higher than `α` (`erwpK_flr`, `LendInv`), the claim
consistent with the view of the world it is raised at (`erwpK_claimXK`), and the finaliser frame
consuming it with `d` (`erwpK_ubindClaimRWK`, `fin_claimM`).
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

/-- **The guarded Mut Frame at `cN`'s tables, its callback a run at its own table from the lend's
world** (`erwpK_M_frameCRG_tab` at `vN`, its callback moved by `erwpK_lend_comap`): the callback is
read as a thunk of `cN` reads it, at `tabN F δ′` from `x.lend ℓ α F`, its posts `Qc`; the lender
runs at its guarded twin `tabGK` at `vN`, its stops guarded by the fold, ending at the lend's
claim. -/
theorem erwpK_M_frameCRG_cN {xv : LifeVar} {bnd : Lifetime.Life}
    (hbnd : LifeCtx.empty.Defines bnd) {α : Life} {δ : LSub} (hLt : LtLife δ bnd α) {l : Loc}
    {Fam : Nat → Val → SPropS Loc Val α} (hFam : DownFam α Fam) {F : CTy}
    (hF : F.SuspendC xv bnd) {Q Qc : KW → PostN}
    (hQ : ∀ x k ls v ρ, Qc (x.lend l α Fam) k ls v ρ → MFPost l α Fam (Q x) k ls v ρ) :
    ∀ n j, n ≤ j → ∀ (x : KW), x.Θ.FoldInv α → ∀ ls e (v : Val) (ρP ρlP ρb ρ : WRes)
      (houtP : ρP.InStratum α), ρb.InStratum (↓α) → ∀ (P : Val → SPropS Loc Val α),
      (∀ u r, SPropS.toU (P u) r → SPropS.toU (Fam j u) r) → ∀ (hwit : P v ⟨ρP, houtP⟩),
      ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP → ResU.CompS ρlP ρb ρ →
      (∀ BM, ResU.CompS ρb (ResU.single l (CellU.mutOf α v ρP houtP P hwit)) BM →
        erwpK (ℍ := ℍ) KW.PostK (fun z => z.Θ.view z.c)
          (fun z => opTableK z.lo (tabN F (δ.extend xv α) z)) Qc (x.lend l α Fam) n ls e BM) →
      erwpK (ℍ := ℍ) KW.PostK (fun z => z.Θ.view z.c)
        (fun y => opTableGRK y.lo (tabGK (ℍ := ℍ) (claimR l α Fam) (CellFold l α Fam)
          (fun A δ Θ k v ρ => vN (ℍ := ℍ) A δ Θ k v ρ) id F δ y) (CellFold l α Fam)
          (claimR l α Fam)) Q x n ls e ρ := by
  intro n j hnj x hx ls e v ρP ρlP ρb ρ houtP houtb P hPF hwit hcl hcρ hcb
  refine erwpK_M_frameCRG_tab (ℍ := ℍ) valRelOK_vN (V := KW.PostK) (Φ := fun z => z.Θ.view z.c)
    hLt hFam hF (Q := Q) n j hnj x hx ls e v ρP ρlP ρb ρ houtP houtb P hPF hwit hcl hcρ
    (fun BM hBM => ?_)
  have hΦ : (fun y : KW => (y.Θ.view y.c).set l α Fam) =
      fun y : KW => (y.lend l α Fam).Θ.view (y.lend l α Fam).c :=
    funext fun y => (KW.lend_view y l α Fam).symm
  rw [hΦ]
  refine erwpK_lend_comap hbnd hLt l Fam hF (Q := Qc) (Q' := fun y => MFPost l α Fam (Q y))
    (fun x' y k ls v ρ hy hq => ⟨x', rfl, ?_⟩) n x ls e BM (hcb BM hBM)
  have hy' : y = x'.lend l α Fam := hy
  subst hy'
  exact hQ x' k ls v ρ hq

/-- **The finaliser consumes the source, at `SemJN`**: `λ_. d ℓ` from a `Mut @a A` value at `ℓ`,
by `d`'s judgment at `Mut @a A ⊸ 1`. -/
theorem fin_claimM {a : Lifetime.Life} {A : VTy} {d : Expr} (hdc : closedAt 0 d = true)
    (hd : SemJN (ℍ := ℍ) LifeCtx.empty [] d (.val (.lolli (.mut a A) .unit))) {δ : LSub}
    {Θ : LocTy} (hΘ : Θ.OK) {c : Loc → Option Life} {l : Loc} {k : Nat} {ls : List SRec}
    {ρ : WRes} (h : vN (ℍ := ℍ) (.mut a A) δ Θ k (Val.loc l) ρ) (hc : ConsistentX c ρ) :
    rwp (ℍ := ℍ) (Θ.view c) (fun _ _ v ρ' => v = Val.unit ∧ ρ' = PMap.empty) k ls
      (.app (.val (Val.lam (.app d (.val (Val.loc l))))) (.val .unit)) ρ := by
  have hΦ := LocTy.view_down hΘ.1 c
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
    c k' le_rfl (Val.loc l) τ₂ τ hcτ (vN_le hk' h) hcτ'
  exact rwp_of_erwp_empty (erwp_of_cN_ret this)

/-- **`withbor (3)` at a suspending row is a value of `!` its type, at `SemJN`**:
`withborU d`, at `Mut @a A ⊸ (∀'x ⊏ @bnd. Mut 'x A ⊸ F_Σ(['x] B)) ⊸ F_Σ(Mut @a A ⊗ B)` with `Σ`
a `Row.Suspend x bnd` row. Its steps at every floor:

* the source `ℓ ↦ mut(β, w₀, σ₀, F_o j₀)`, `Θ (ℓ, β) = F_o`, and `c ℓ = β` (`consistentX_get`):
  the anti-frame's invariant `KW.SealInv` at the start;
* the lend's lifetime `α` with `FoldInv α` at `Θ` (`LocTy.exists_foldInv`), below `β`, the bound
  and the callback's stratum; the lender at the floor no higher than `α` (`erwpK_flr`), its worlds
  `LendInv Θ α`;
* the anti-frame at the source (`erwpK_M_antiFrameCR_tab`), the opened cell lent at `α`
  (`erwpK_M_frameCRG_cN`), the callback read as `cN` reads it;
* the content handed back in `F_i k` is in `F_o k` (`vN_above`), the resealed cell a `Mut @a A`
  value in `Res_α` (`Rout`), beside the result and in every raise's claim, a value at every world
  `LendInv Θ α` holds at (`vN_above`); the claim consistent (`erwpK_claimXK`); the finaliser frame
  consumes it with `d` (`erwpK_ubindClaimRWK`, `fin_claimM`).

Premises those of the rule; `hd` is `d`'s judgment at `SemJN`. -/
theorem withbor3S_compat {a : Lifetime.Life} {x : LifeVar} {bnd : Lifetime.Life} {A B : VTy}
    {S : Row} {d : Expr} (hbnd : LifeCtx.empty.Defines bnd) (hA : ¬ VFree x A) (hB : ¬ VFree x B)
    (hS : S.Suspend x bnd)
    (hdc : closedAt 0 d = true)
    (hd : SemJN (ℍ := ℍ) LifeCtx.empty [] d (.val (.lolli (.mut a A) .unit))) (δ : LSub)
    (Θ₀ : LocTy) (n : Nat) :
    vN (ℍ := ℍ) (.bang (withbor3UTy a x bnd A B S)) δ Θ₀ n (withborUV d) PMap.empty := by
  refine ⟨rfl, fun Θ _ hΘ c₁ _ ls => ?_⟩
  intro c₂ k hk u ρv ρu hc hu _
  obtain rfl := eq_of_compS_empty_left hc
  intro c k' hk' f ρf ρ'' hc' hf hcon
  set P : CPredL := fun Θ' j u r => vN (ℍ := ℍ) A δ Θ' j u r with hP
  obtain ⟨α₀, hα₀, (β : Life), hα₀β, hm, hunif⟩ := vN_le hk' hu
  obtain ⟨l, w₀, σ₀, hσ₀, j₀, hw₀, hkj, rfl, hl, rfl⟩ := id hm
  rw [cN_effOf]
  intro lo
  refine erwpK_of_valid fun hv'' => ?_
  set Fo := CTy.effOf S (.tensor (.mut a A) B) with hFo
  set Qo : KW → PostN := fun z k _ v ρ => vN (ℍ := ℍ) (.tensor (.mut a A) B) δ z.Θ k v ρ
    with hQo
  have hQoD : ∀ z, (Qo z).Down := fun z k _ v ρ h => vN_down _ δ z.Θ k v ρ h
  -- the source's cell
  set cellβ := ResU.single l (CellU.mutOf β w₀ σ₀ hσ₀ (famL β P Θ j₀) hw₀) with hcellβ
  have hvu : ResU.Valid cellβ := (ResU.Valid.split hc' hv'').1
  have hkm : (CellU.mutOf β w₀ σ₀ hσ₀ (famL β P Θ j₀) hw₀).kind ≠ Kind.imm := by
    rw [CellU.kind_mutOf]; exact fun c => Kind.noConfusion c
  have hget : ρ''.get l = some (CellU.mutOf β w₀ σ₀ hσ₀ (famL β P Θ j₀) hw₀) :=
    (ResU.CompS.get_left_of_ne_imm hc' (ResU.single_get_self _ _) hkm).2
  -- the source's cell is at its view lifetime: the anti-frame's invariant at the start
  have hcl : c l = some β := by
    have h := consistentX_get hcon hv'' hget (CellU.kind_mutOf _ _ _ _ _ _)
    rwa [CellU.at_mutOf] at h
  -- the parts of the start are consistent with the view
  have hcf : ConsistentX c ρf := consistentX_right hc' hcon hv''
  have hcσ : ConsistentX c σ₀ := consistentX_mut_wit (consistentX_left hc' hcon hv'') hvu
  -- the lend's lifetime: `FoldInv` at `Θ`, below `β`, the bound and the callback's stratum
  obtain ⟨γ, hγ⟩ := hbnd δ (models_empty_any _)
  obtain ⟨βf, hβf⟩ := ResU.exists_stratum ρf
  obtain ⟨α, hαle, hfold⟩ := LocTy.exists_foldInv hΘ.2 (↓(β ⊓ βf ⊓ γ))
  have hfr : Θ.Fresh α := hfold.1
  have hαlt : α < β ⊓ βf ⊓ γ := lt_of_le_of_lt hαle (Life.down_sqsubset _)
  have hαβlt : α < β := lt_of_lt_of_le hαlt (inf_le_left.trans inf_le_left)
  have hαβ : α ≤ β := hαβlt.le
  have houtP : σ₀.InStratum α := hσ₀.mono hαβ
  have houtf : ρf.InStratum (↓α) := hβf.mono
    ((Life.down_sqsubset α).le.trans (hαlt.le.trans (inf_le_left.trans inf_le_right)))
  have hLt : LtLife δ bnd α := ⟨γ, hγ, lt_of_lt_of_le hαlt inf_le_right⟩
  set δ' := δ.extend x α with hδ'
  have hAδ : vN (ℍ := ℍ) A δ' = vN (ℍ := ℍ) A δ := vN_extend_of_not_free hA δ α
  have hBδ : vN (ℍ := ℍ) B δ' = vN (ℍ := ℍ) B δ := vN_extend_of_not_free hB δ α
  set P' : CPredL := fun Θ' j u r => vN (ℍ := ℍ) A δ' Θ' j u r with hP'
  set Fam : Nat → Val → SPropS Loc Val α := famL α P' Θ with hFam
  have hFamD : DownFam α Fam := vN_fam_down A δ' α Θ
  have hwit : Fam j₀ w₀ ⟨σ₀, houtP⟩ :=
    (vN_above A δ' Θ houtP).mpr (by rw [hAδ]; exact (vN_above A δ Θ hσ₀).mp hw₀)
  -- the content handed back in `F_i k` is in `F_o k`
  have hoi : ∀ k w σ (h : σ.InStratum α), Fam k w ⟨σ, h⟩ →
      ∃ h' : σ.InStratum β, famL β P Θ k w ⟨σ, h'⟩ := by
    intro k w σ h hw
    have hv : vN (ℍ := ℍ) A δ Θ k w σ := by rw [← hAδ]; exact (vN_above A δ' Θ h).mp hw
    exact ⟨hunif Θ k w σ hv, (vN_above A δ Θ (hunif Θ k w σ hv)).mpr hv⟩
  have hG : ∀ k ls ρ, CellFold l α Fam k ls ρ → CellFold l β (famL β P Θ) k ls ρ := by
    rintro k ls ρ ⟨w, χ, h, hw, R, rest, h1, h2⟩
    obtain ⟨h', hw'⟩ := hoi k w χ h hw
    exact ⟨w, χ, h', hw', R, rest, h1, h2⟩
  have hRin : ∀ k ρ, claimR l α Fam k ρ → claimR l β (famL β P Θ) k ρ := by
    rintro k ρ ⟨w, σ, h, hw, hcl'⟩
    obtain ⟨h', hw'⟩ := hoi k w σ h hw
    exact ⟨w, σ, h', hw', hcl'⟩
  -- the resealed source: a `Mut @a A` value at `Θ`, in `Res_α`
  set Rout : Nat → WProp := fun k ρ =>
    vN (ℍ := ℍ) (.mut a A) δ Θ k (Val.loc l) ρ ∧ ρ.InStratum α with hRoutd
  have hRout : ∀ k (w : Val) (σ : WRes) (h : σ.InStratum β) (hw : famL β P Θ k w ⟨σ, h⟩),
      Rout k (ResU.single l (CellU.mutOf β w σ h (famL β P Θ k) hw)) :=
    fun k w σ h hw => ⟨⟨α₀, hα₀, β, hα₀β, ⟨l, w, σ, h, k, hw, le_rfl, rfl, hl, rfl⟩, hunif⟩,
      ResU.inStratum_single l (show (CellU.mutOf β w σ h (famL β P Θ k) hw).InStratum α
        from hαβlt)⟩
  -- a value at `Θ` in `Res_α` is one at every world `LendInv Θ α` holds at
  have hmove : ∀ (T : VTy) (z : KW), LendInv Θ α z → ∀ k (v : Val) (ρ : WRes), ρ.InStratum α →
      vN (ℍ := ℍ) T δ Θ k v ρ → vN (ℍ := ℍ) T δ z.Θ k v ρ := by
    intro T z hz k v ρ hρ h
    have h' := (vN_above T δ Θ hρ).mpr h
    rw [← hz.2.2] at h'
    exact (vN_above T δ z.Θ hρ).mp h'
  -- the callback's world and view
  set Θ' := Θ.add l α Fam with hΘ'
  set c' := setLife c l α with hc'def
  have hOK' : Θ'.OK := by
    obtain ⟨N, hN⟩ := hΘ.2
    exact ⟨LocTy.down_add hΘ.1 l hFamD, ⟨min N (↓α), LocTy.fresh_add hN (min_le_left _ _)
      (lt_of_le_of_lt (min_le_right _ _) (Life.down_sqsubset α)) l Fam⟩⟩
  have hcf' : ConsistentX c' ρf :=
    consistentX_setLife hcf (exS_none_of_part hc' hv'' (ResU.single_get_self _ _) hkm) α
  have hcσ' : ConsistentX c' σ₀ := consistentX_setLife hcσ (exS_wit_none hvu) α
  set Rc := claimR l α Fam with hRc
  set Gc := CellFold l α Fam with hGc
  have hFS : Fo.SuspendC x bnd := suspendC_effOf hS _
  -- the lender at the floor no higher than `α`
  set x₁ : KW := KW.flr α ⟨Θ, c, lo⟩ with hx₁
  have hx₁I : LendInv Θ α x₁ := ⟨hΘ, min_le_right _ _, rfl⟩
  suffices hx₁ : erwpK (ℍ := ℍ) KW.PostK (fun z => z.Θ.view z.c)
      (fun z => opTableK z.lo (tabN (ℍ := ℍ) Fo δ z)) Qo x₁ k' ls
      (((forceE (CTy.arr (.mut a A) (CTy.arr (cbUTy x bnd (.mut (.var x) A) B S) Fo))
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
      Val.loc, Val.lam, Expr.val, Val.prim, subst_closedAt d (s := _) hdc (Nat.zero_le _)]
  rw [e₃]
  -- the lender's post: at a world whose location typing above `α` is the lend's, the pair
  set Ql : KW → PostN := fun z k _ b ρ => z.Θ.above α = Θ.above α →
    vN (ℍ := ℍ) (.tensor (.mut a A) B) δ z.Θ k (Val.pair (Val.loc l) b) ρ with hQl
  -- the anti-frame at the source, across the callback's stops, raises and layered cancel runs
  have hAF := erwpK_M_antiFrameCR_tab (ℍ := ℍ) (vr := fun A δ Θ k v ρ => vN (ℍ := ℍ) A δ Θ k v ρ)
    (V := KW.PostK) hFS δ hG hRin hRout (Q := Ql) k' x₁ ⟨hΘ, hl, hcl⟩ ls
    (.app (.app (.val f) (.val .unit)) (.val (Val.loc l))) w₀ σ₀ hσ₀ j₀ hw₀ ρf ρ'' hc'
    (fun W X hW hX => ?_)
  · -- the claim consistent, the finaliser frame consuming it at the world it is raised at
    have hM' := erwpK_claimXK k' x₁ ls _ ρ'' hcon hAF
    have hfin := erwpK_ubindClaimRWK (ℍ := ℍ) valRelOK_vN (RW := claimXK Rout)
      (Inv := LendInv Θ α) (fun z hz => LocTy.view_down hz.1.1 z.c) lendInv_owed
      (F := Fo) (δ := δ) (tabN_suspend_raise hS _ δ) (NFv l) (DFv d l) ?_ hQoD ?_ k' x₁ hx₁I ls
      _ ρ'' hM'
    · simpa only [tabNK_vN] using hfin
    · rintro z hz j ls' ρ ⟨⟨hR, hRs⟩, hcR⟩
      exact fin_claimM hdc hd hz.1 (hmove _ z hz j _ ρ hRs hR) hcR
    · intro z hz j ls' bv ρ hq
      have hTdz : (opTableK z.lo (tabNK (ℍ := ℍ) (fun A δ Θ k v ρ => vN (ℍ := ℍ) A δ Θ k v ρ)
          id Fo δ z)).Down := opTableK_downI (tabNK_downI valRelOK_vN id Fo δ z)
      refine erwpK_det (Φ := fun z : KW => z.Θ.view z.c) (x := z) (LocTy.view_down hz.1.1 z.c)
        hTdz hQoD (fun μ => step1Only_plug (Head.beta μ _ bv) rfl .hole) ?_
      simp [Kont.plug, Expr.subst]
      exact erwpK_val (KW.postK_refl z) (v := Val.pair (Val.loc l) bv) (hq hz.2.2)
  -- the opened cell lent at `α`
  refine erwpK_M_frameCRG_cN (ℍ := ℍ) hbnd hLt hFamD hFS (Q := fun z => AFPost l β (famL β P Θ) (Ql z))
    (Qc := fun z k _ v ρ => vN (ℍ := ℍ) (.box (.var x) B) δ' z.Θ k v ρ) ?_ k' j₀ hkj x₁ hfold ls
    _ w₀ σ₀ W ρf X houtP houtf (Fam j₀) (fun _ _ h => h) hwit (ResU.CompS.comm hW)
    (ResU.CompS.comm hX) ?_
  · -- the callback's post: the content back in `F_o`, the cell resealed, the pair
    intro z j ls' bv ρ' hb
    obtain ⟨β', hβ', hbB, hst⟩ := hb
    rw [interp_ext_self] at hβ'
    cases Option.some.inj hβ'
    refine ⟨hst, fun w Y hY σ ⟨hσ, hFσ⟩ Z hZ => ?_⟩
    obtain ⟨h', hw'⟩ := hoi j w σ hσ hFσ
    obtain ⟨ac, hac, hacZ⟩ := compS_exch hY hZ
    have hbB' : vN (ℍ := ℍ) B δ z.Θ j bv ρ' :=
      vN_local B δ z.Θ l α Fam j bv ρ' hst (by rw [← hBδ]; exact hbB)
    refine ⟨w, σ, h', hw', ρ', ac, ResU.CompS.comm hacZ, ResU.CompS.comm hac,
      fun X' hX' habove => ?_⟩
    obtain ⟨hRo, hRs⟩ := hRout j w σ h' hw'
    have hRo' : vN (ℍ := ℍ) (.mut a A) δ z.Θ j (Val.loc l)
        (ResU.single l (CellU.mutOf β w σ h' (famL β P Θ j) hw')) := by
      have h₁ := (vN_above (.mut a A) δ Θ hRs).mpr hRo
      rw [← habove] at h₁
      exact (vN_above (.mut a A) δ z.Θ hRs).mp h₁
    exact ⟨Val.loc l, bv, _, ρ', rfl, ResU.CompS.comm hX', hRo', hbB'⟩
  · -- the callback, at the lend's world and view, from the borrow
    intro BM hBM
    have h1 := (hf Θ' ((LocTy.extA_add hfr l Fam).extR ρf) hOK' c' hcf' ls) α hLt
    have hcell : vN (ℍ := ℍ) (.mut (.var x) A) δ' Θ' k' (Val.loc l)
        (ResU.single l (CellU.mutOf α w₀ σ₀ houtP (Fam j₀) hwit)) :=
      ⟨α, interp_ext_self δ x α, α, le_rfl, lend_mutL Θ l α P' hkj houtP hwit,
        fun Θ'' j u r h => (hunif Θ'' j u r (by rw [← hAδ]; exact h)).mono hαβ⟩
    have hcBM : ConsistentX c' BM := consistentX_compS hBM hcf'
      (consistentX_single_mut hcσ' (by simp [hc'def, setLife]))
    have h2 := h1 c' k' le_rfl (Val.loc l) _ BM hBM hcell hcBM
    rw [cN_effOf] at h2
    have h3 := h2 α
    simp only [tabN_effOf_base S (.box (.var x) B) (.tensor (.mut a A) B)] at h3
    exact h3

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
