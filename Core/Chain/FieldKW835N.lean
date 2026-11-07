import Core.Chain.ReborrowKW835N

/-!
# The suspending field reborrow at the typed world  `[spec §62]`

`withborF` at a suspending row at `SemJN` (`withborFS_compat`), step for step: `withbor3S_compat`'s
proof at the source `Mut @a (Ref A)`, with the `load` from the opened cell (`rwp_load`,
`erwpK_bindR`) and the opened cell `ℓ ↦ own(loc ℓ₂)` framed outside the guarded Mut Frame at the
field (`erwpK_frameGR_tab`).
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
open BoCa.Fig16.Tree.Wp.Goal791 (withborFSTy withborFV withborFE)
open BoCa.BoLo (Heap Kont Head ubindE)

/-- **`withborF` at a suspending row is a value of `!` its type, at `SemJN`**:
`withborF d` at
`Mut @a (Ref A) ⊸ (∀'x ⊏ @bnd. Mut 'x A ⊸ F_Σ(['x] B)) ⊸ F_Σ(Mut @a (Ref A) ⊗ B)`, `Σ` a
`Row.Suspend x bnd` row. `withbor3S_compat`'s steps at the source `Mut @a (Ref A)`, with three
changes: the source's content read as a `Ref A` value
`ℓ₂ ↦ own(u₀) ● σ_u`; the `load` from the opened cell `ℓ ↦ own(loc ℓ₂)` (`rwp_load`); the guarded
Mut Frame at `ℓ₂` (`erwpK_M_frameCRG_cN`), the opened cell framed outside it
(`erwpK_frameGR_tab`), `hunif` at `A` and the inclusion into `F_o` from `hunif` at `Ref A`.

Premises those of the rule; `hd` is `d`'s judgment at `SemJN`. -/
theorem withborFS_compat {a : Lifetime.Life} {x : LifeVar} {bnd : Lifetime.Life} {A B : VTy}
    {S : Row} {d : Expr} (hbnd : LifeCtx.empty.Defines bnd) (hA : ¬ VFree x A) (hB : ¬ VFree x B)
    (hS : S.Suspend x bnd)
    (hdc : closedAt 0 d = true)
    (hd : SemJN (ℍ := ℍ) LifeCtx.empty [] d (.val (.lolli (.mut a (.ref A)) .unit))) (δ : LSub)
    (Θ₀ : LocTy) (n : Nat) :
    vN (ℍ := ℍ) (.bang (withborFSTy a x bnd A B S)) δ Θ₀ n (withborFV d) PMap.empty := by
  refine ⟨rfl, fun Θ _ hΘ c₁ _ ls => ?_⟩
  intro c₂ k hk u ρv ρu hc hu _
  obtain rfl := eq_of_compS_empty_left hc
  intro c k' hk' f ρf ρ'' hc' hf hcon
  set P : CPredL := fun Θ' j u r => vN (ℍ := ℍ) (.ref A) δ Θ' j u r with hP
  obtain ⟨α₀, hα₀, (β : Life), hα₀β, hm, hunif⟩ := vN_le hk' hu
  obtain ⟨l, w₀, σ₀, hσ₀, j₀, hw₀, hkj, rfl, hl, rfl⟩ := id hm
  -- the source's content is the field `ℓ₂ ↦ own(u₀) ● σ_u`
  obtain ⟨l₂, u₀, σu, rfl, hσ₀s, hu₀⟩ := (vN_above (.ref A) δ Θ hσ₀).mp hw₀
  rw [cN_effOf]
  intro lo
  refine erwpK_of_valid fun hv'' => ?_
  set Fo := CTy.effOf S (.tensor (.mut a (.ref A)) B) with hFo
  set Qo : KW → PostN := fun z k _ v ρ => vN (ℍ := ℍ) (.tensor (.mut a (.ref A)) B) δ z.Θ k v ρ
    with hQo
  have hQoD : ∀ z, (Qo z).Down := fun z k _ v ρ h => vN_down _ δ z.Θ k v ρ h
  -- the source's cell
  set cellβ := ResU.single l
    (CellU.mutOf β (Val.loc l₂) σ₀ hσ₀ (famL β P Θ j₀) hw₀) with hcellβ
  have hvu : ResU.Valid cellβ := (ResU.Valid.split hc' hv'').1
  have hkm : (CellU.mutOf β (Val.loc l₂) σ₀ hσ₀ (famL β P Θ j₀) hw₀).kind ≠ Kind.imm := by
    rw [CellU.kind_mutOf]; exact fun c => Kind.noConfusion c
  have hget : ρ''.get l = some (CellU.mutOf β (Val.loc l₂) σ₀ hσ₀ (famL β P Θ j₀) hw₀) :=
    (ResU.CompS.get_left_of_ne_imm hc' (ResU.single_get_self _ _) hkm).2
  have hcl : c l = some β := by
    have h := consistentX_get hcon hv'' hget (CellU.kind_mutOf _ _ _ _ _ _)
    rwa [CellU.at_mutOf] at h
  have hcf : ConsistentX c ρf := consistentX_right hc' hcon hv''
  have hcσ : ConsistentX c σ₀ := consistentX_mut_wit (consistentX_left hc' hcon hv'') hvu
  -- the field's cell
  have hkown : (CellU.ownOf (Loc := Loc) u₀).kind ≠ Kind.imm := by rw [CellU.kind_ownOf]; decide
  have hσ₀l₂ : σ₀.get l₂ = some (CellU.ownOf u₀) :=
    (ResU.CompS.get_left_of_ne_imm hσ₀s (ResU.single_get_self _ _) hkown).2
  have hσu : σu.InStratum β := ResU.CompS.inStratum_right hσ₀s hσ₀
  obtain ⟨-, eβ, -, heβ, -, -⟩ := hvu
  obtain ⟨e₀, he₀, he₀β⟩ := exS_mut_wit_get heβ
  have hcσu : ConsistentX c σu := consistentX_leftE (ResU.CompS.comm hσ₀s) hcσ he₀
  -- every value of `A` is in `Res_β`, as its cell is a `Ref A` value
  have hunifA : ∀ (Θ' : LocTy) (j : Nat) (u : Val) (r : WRes), vN (ℍ := ℍ) A δ Θ' j u r →
      r.InStratum β := by
    intro Θ' j u r h
    obtain ⟨l', hl'⟩ := PMap.exists_fresh loc_infinite r
    obtain ⟨X, hX⟩ := (ResU.compS_defined_iff r (ResU.single l' (CellU.ownOf u))).mpr
      (compatS_single_of_get_none hl')
    exact ResU.CompS.inStratum_left hX
      (hunif Θ' j (Val.loc l') X ⟨l', u, r, rfl, ResU.CompS.comm hX, h⟩)
  -- the lend's lifetime: `FoldInv` at `Θ`, below `β`, the bound and the callback's stratum
  obtain ⟨γ, hγ⟩ := hbnd δ (models_empty_any _)
  obtain ⟨βf, hβf⟩ := ResU.exists_stratum ρf
  obtain ⟨α, hαle, hfold⟩ := LocTy.exists_foldInv hΘ.2 (↓(β ⊓ βf ⊓ γ))
  have hfr : Θ.Fresh α := hfold.1
  have hαlt : α < β ⊓ βf ⊓ γ := lt_of_le_of_lt hαle (Life.down_sqsubset _)
  have hαβlt : α < β := lt_of_lt_of_le hαlt (inf_le_left.trans inf_le_left)
  have hαβ : α ≤ β := hαβlt.le
  have houtP : σu.InStratum α := hσu.mono hαβ
  have houtf : ρf.InStratum (↓α) := hβf.mono
    ((Life.down_sqsubset α).le.trans (hαlt.le.trans (inf_le_left.trans inf_le_right)))
  have hLt : LtLife δ bnd α := ⟨γ, hγ, lt_of_lt_of_le hαlt inf_le_right⟩
  set δ' := δ.extend x α with hδ'
  have hAδ : vN (ℍ := ℍ) A δ' = vN (ℍ := ℍ) A δ := vN_extend_of_not_free hA δ α
  have hBδ : vN (ℍ := ℍ) B δ' = vN (ℍ := ℍ) B δ := vN_extend_of_not_free hB δ α
  set P' : CPredL := fun Θ' j u r => vN (ℍ := ℍ) A δ' Θ' j u r with hP'
  set Fam : Nat → Val → SPropS Loc Val α := famL α P' Θ with hFam
  have hFamD : DownFam α Fam := vN_fam_down A δ' α Θ
  have hwit : Fam j₀ u₀ ⟨σu, houtP⟩ :=
    (vN_above A δ' Θ houtP).mpr (by rw [hAδ]; exact hu₀)
  -- the field's content handed back, with its cell, is in `F_o k`
  have hoi : ∀ k w σ (h : σ.InStratum α) (X : WRes), Fam k w ⟨σ, h⟩ →
      ResU.CompS (ResU.single l₂ (CellU.ownOf w)) σ X →
      ∃ h' : X.InStratum β, famL β P Θ k (Val.loc l₂) ⟨X, h'⟩ := by
    intro k w σ h X hw hX
    have hv : vN (ℍ := ℍ) A δ Θ k w σ := by rw [← hAδ]; exact (vN_above A δ' Θ h).mp hw
    have hr : vN (ℍ := ℍ) (.ref A) δ Θ k (Val.loc l₂) X := ⟨l₂, w, σ, rfl, hX, hv⟩
    exact ⟨hunif Θ k _ X hr, (vN_above (.ref A) δ Θ (hunif Θ k _ X hr)).mpr hr⟩
  -- the opened cell, framed outside the Mut Frame at `ℓ₂`
  set Fr : WProp := fun ρ => ρ = ResU.single l (CellU.ownOf (Val.loc l₂)) with hFr
  set Rc := claimR l₂ α Fam with hRc
  set Gc := CellFold l₂ α Fam with hGc
  set G : ShareG := Gc.sep fun _ => Fr with hGdef
  set Rin : Nat → WProp := fun k => Rc k ⋆ Fr with hRindef
  have hG : ∀ k ls ρ, G k ls ρ → CellFold l β (famL β P Θ) k ls ρ := by
    rintro k ls ρ ⟨ρ₁, ρ₂, h12, ⟨w, χ, h, hw, R, rest, h1, h2⟩, rfl⟩
    obtain ⟨X, hX, hXR⟩ := compS_reassoc' h2 h1
    obtain ⟨h', hw'⟩ := hoi k w χ h X hw hX
    exact ⟨Val.loc l₂, X, h', hw', R, ρ₁, ResU.CompS.comm h12, hXR⟩
  have hRin : ∀ k ρ, Rin k ρ → claimR l β (famL β P Θ) k ρ := by
    rintro k ρ ⟨ρ₁, ρ₂, h12, ⟨w, σ, h, hw, hcl'⟩, rfl⟩
    obtain ⟨h', hw'⟩ := hoi k w σ h ρ₁ hw hcl'
    exact ⟨Val.loc l₂, ρ₁, h', hw', ResU.CompS.comm h12⟩
  -- the resealed source: a `Mut @a (Ref A)` value at `Θ`, in `Res_α`
  set Rout : Nat → WProp := fun k ρ =>
    vN (ℍ := ℍ) (.mut a (.ref A)) δ Θ k (Val.loc l) ρ ∧ ρ.InStratum α with hRoutd
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
  set Θ' := Θ.add l₂ α Fam with hΘ'
  set c' := setLife c l₂ α with hc'def
  have hOK' : Θ'.OK := by
    obtain ⟨N, hN⟩ := hΘ.2
    exact ⟨LocTy.down_add hΘ.1 l₂ hFamD, ⟨min N (↓α), LocTy.fresh_add hN (min_le_left _ _)
      (lt_of_le_of_lt (min_le_right _ _) (Life.down_sqsubset α)) l₂ Fam⟩⟩
  have hcf' : ConsistentX c' ρf := by
    obtain ⟨-, ex, -, hex, -, -⟩ := hv''
    refine consistentX_setLife hcf (exS_none_of_walk hc' hex fun e₁ he₁ => ?_) α
    obtain ⟨e₀', he₀', hget'⟩ := exS_mut_wit_get he₁
    exact ⟨_, hget' l₂ _ (ExS.get_of_ne_imm he₀' hσ₀l₂ hkown) hkown, hkown⟩
  have hcσu' : ConsistentX c' σu := consistentX_setLife hcσu
    (exS_none_of_walk hσ₀s he₀ fun e₁ he₁ =>
      ⟨_, ExS.get_of_ne_imm he₁ (ResU.single_get_self _ _) hkown, hkown⟩) α
  have hFS : Fo.SuspendC x bnd := suspendC_effOf hS _
  -- the lender at the floor no higher than `α`
  set x₁ : KW := KW.flr α ⟨Θ, c, lo⟩ with hx₁
  have hx₁I : LendInv Θ α x₁ := ⟨hΘ, min_le_right _ _, rfl⟩
  refine erwpK_flr_tabN α (Q := Qo) (fun _ _ _ _ _ h => h) k' ⟨Θ, c, lo⟩ ls _ ρ'' ?_
  have hΦ₁ : (x₁.Θ.view x₁.c).Down := LocTy.view_down hΘ.1 c
  have hTd₁ : (opTableK x₁.lo (tabN (ℍ := ℍ) Fo δ x₁)).Down :=
    opTableK_downI (tabN_downI_OK Fo δ x₁)
  refine erwpK_det (Φ := fun z : KW => z.Θ.view z.c) (x := x₁) hΦ₁ hTd₁ hQoD
    (fun μ => step1Only_plug (Head.beta μ _ (Val.loc l)) rfl (.appL .hole f)) ?_
  refine erwpK_det (Φ := fun z : KW => z.Θ.view z.c) (x := x₁) hΦ₁ hTd₁ hQoD
    (fun μ => step1Only_plug (Head.beta μ _ f) rfl .hole) ?_
  have e₃ : Kont.hole.plug (Expr.subst 0 f (Expr.subst (0 + 1) (Val.shift 1 0 (Val.loc l))
        (thenE ((Expr.var 2).pair (Expr.var 0)) (d.app (Expr.var 2))
          (((Expr.var 0).app (Expr.val Val.unit)).app
            ((Expr.val (Val.prim .load)).app (Expr.var 1)))))) =
      ubindE (.pair (NFv l) (DFv d l)) (.app (.app (.val f) (.val .unit))
        (.app (.val (Val.prim .load)) (.val (Val.loc l)))) := by
    simp [Kont.plug, Expr.subst, Expr.shift, thenE, ubindE, NFv, DFv, Val.shift, Val.pair,
      Val.loc, Val.lam, Expr.val, Val.prim, subst_closedAt d (s := _) hdc (Nat.zero_le _)]
  rw [e₃]
  -- the lender's post: at a world whose location typing above `α` is the lend's, the pair
  set Ql : KW → PostN := fun z k _ b ρ => z.Θ.above α = Θ.above α →
    vN (ℍ := ℍ) (.tensor (.mut a (.ref A)) B) δ z.Θ k (Val.pair (Val.loc l) b) ρ with hQl
  -- the anti-frame at the source, across stops, raises and layered cancel runs
  have hAF := erwpK_M_antiFrameCR_tab (ℍ := ℍ) (vr := fun A δ Θ k v ρ => vN (ℍ := ℍ) A δ Θ k v ρ)
    (V := KW.PostK) hFS δ hG hRin hRout (Q := Ql) k' x₁ ⟨hΘ, hl, hcl⟩ ls
    (.app (.app (.val f) (.val .unit)) (.app (.val (Val.prim .load)) (.val (Val.loc l))))
    (Val.loc l₂) σ₀ hσ₀ j₀ hw₀ ρf ρ'' hc' (fun W X hW hX => ?_)
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
  -- the `load` from the opened cell `ℓ ↦ own(loc ℓ₂)`
  obtain ⟨X'', hX''1, hX''2⟩ := compS_reassoc' hW hX
  show erwpK (ℍ := ℍ) KW.PostK (fun y => y.Θ.view y.c)
    (fun y => opTableGRK y.lo (tabGK (ℍ := ℍ) Rin G (fun A δ Θ k v ρ => vN (ℍ := ℍ) A δ Θ k v ρ)
      id Fo δ y) G Rin) (fun y => AFPost l β (famL β P Θ) (Ql y)) x₁ k' ls
    ((Kont.appR (.app (.val f) (.val .unit)) .hole).plug
      (.app (.val (Val.prim .load)) (.val (Val.loc l)))) X
  refine erwpK_bindR (Φ := fun z : KW => z.Θ.view z.c) (x := x₁)
    (fun _ => or_local (performStopGK_local _ _ _) (raiseStopRK_free _ _)) hΦ₁
    (Kont.appR (.app (.val f) (.val .unit)) .hole) ?_
  refine rwp_load ls l (Val.loc l₂) _
    ⟨_, X'', ResU.CompS.comm hX''2, rfl, fun ρ₁ ρ₂ h1 h2 => ?_⟩
  subst h1
  -- the opened cell framed outside the Mut Frame
  set Q₁ : KW → PostN := fun z k ls' v Z =>
    ∀ X₁, ResU.CompS Z (ResU.single l (CellU.ownOf (Val.loc l₂))) X₁ →
      AFPost l β (famL β P Θ) (Ql z) k ls' v X₁ with hQ₁
  refine erwpK_mono (Tb := fun z => opTableGRK z.lo (tabGK (ℍ := ℍ) (fun k => Rc k ⋆ Fr)
      (Gc.sep fun _ => Fr) (fun A δ Θ k v ρ => vN (ℍ := ℍ) A δ Θ k v ρ) id Fo δ z)
      (Gc.sep fun _ => Fr) (fun k => Rc k ⋆ Fr))
    (Q := fun y k ls' v => Q₁ y k ls' v ⋆ Fr) (fun _ _ h => h)
    (fun z k ls' b ρ' (hb : (Q₁ z k ls' b ⋆ Fr) ρ') => by
      obtain ⟨ρa, ρb, hab, hq, hρb⟩ := hb
      exact hq _ (by rw [hρb] at hab; exact hab))
    (fun z k ls t Ψ Ψ' ρ hΨ h =>
      or_local (performStopGK_local _ _ _) (raiseStopRK_free _ _) k ls t Ψ Ψ' ρ hΨ h)
    _ x₁ ls _ ρ₂
    (erwpK_frameGR_tab (ℍ := ℍ) (V := KW.PostK) (Φ := fun z => z.Θ.view z.c) hFS
      (fun A δ Θ k v ρ => vN (ℍ := ℍ) A δ Θ k v ρ) δ Rc Gc (Q := Q₁) Fr _ x₁ ls _ X'' _ ρ₂ h2
      rfl ?_)
  -- the field lent at `α`
  refine erwpK_M_frameCRG_cN (ℍ := ℍ) hbnd hLt hFamD hFS (Q := Q₁)
    (Qc := fun z k _ v ρ => vN (ℍ := ℍ) (.box (.var x) B) δ' z.Θ k v ρ) ?_ (k' - 1) j₀
    (by omega) x₁ hfold ls _ u₀ σu σ₀ ρf X'' houtP houtf (Fam j₀) (fun _ _ h => h) hwit hσ₀s
    (ResU.CompS.comm hX''1) ?_
  · -- the callback's post: the field's cell with its content in `F_o k`, the source resealed
    intro z j ls' bv ρ' hb
    obtain ⟨β', hβ', hbB, hst⟩ := hb
    rw [interp_ext_self] at hβ'
    cases Option.some.inj hβ'
    refine ⟨hst, fun w Y hY σ ⟨hσ, hFσ⟩ Z hZ X₁ hX₁ => ?_⟩
    obtain ⟨σ', hσ', hρ'σ'⟩ := compS_reassoc hY hZ
    obtain ⟨h', hw'⟩ := hoi j w σ hσ σ' hFσ hσ'
    have hbB' : vN (ℍ := ℍ) B δ z.Θ j bv ρ' :=
      vN_local B δ z.Θ l₂ α Fam j bv ρ' hst (by rw [← hBδ]; exact hbB)
    refine ⟨Val.loc l₂, σ', h', hw', ρ', Z, ResU.CompS.comm hX₁, ResU.CompS.comm hρ'σ',
      fun X' hX' habove => ?_⟩
    obtain ⟨hRo, hRs⟩ := hRout j _ σ' h' hw'
    have hRo' : vN (ℍ := ℍ) (.mut a (.ref A)) δ z.Θ j (Val.loc l)
        (ResU.single l (CellU.mutOf β (Val.loc l₂) σ' h' (famL β P Θ j) hw')) := by
      have h₁ := (vN_above (.mut a (.ref A)) δ Θ hRs).mpr hRo
      rw [← habove] at h₁
      exact (vN_above (.mut a (.ref A)) δ z.Θ hRs).mp h₁
    exact ⟨Val.loc l, bv, _, ρ', rfl, ResU.CompS.comm hX', hRo', hbB'⟩
  · -- the callback, at the lend's world and view, from the borrow
    intro BM hBM
    have h1 := (hf Θ' ((LocTy.extA_add hfr l₂ Fam).extR ρf) hOK' c' hcf' ls) α hLt
    have hcell : vN (ℍ := ℍ) (.mut (.var x) A) δ' Θ' (k' - 1) (Val.loc l₂)
        (ResU.single l₂ (CellU.mutOf α u₀ σu houtP (Fam j₀) hwit)) :=
      ⟨α, interp_ext_self δ x α, α, le_rfl, lend_mutL Θ l₂ α P' (by omega) houtP hwit,
        fun Θ'' j u r h => (hunifA Θ'' j u r (by rw [← hAδ]; exact h)).mono hαβ⟩
    have hcBM : ConsistentX c' BM := consistentX_compS hBM hcf'
      (consistentX_single_mut hcσu' (by simp [hc'def, setLife]))
    have h2 := h1 c' (k' - 1) (by omega) (Val.loc l₂) _ BM hBM hcell hcBM
    rw [cN_effOf] at h2
    have h3 := h2 α
    simp only [tabN_effOf_base S (.box (.var x) B) (.tensor (.mut a (.ref A)) B)] at h3
    exact h3

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
