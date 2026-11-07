import Core.Chain.WithloadKW835N

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

/-!
# The `imm` fold at the typed world  `[spec §47, §62]`

`FoldImm836N`'s `foldImm_compatN` at `SemJN`: the traversal stops nowhere, each leaf's `withload`
is `withload_rebT` at the empty table, and the algebras' `F` answers are read at the empty table
(`erwp_of_cN_ret`).
-/

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel (LtLife substAll)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Kont Head)

attribute [local simp] Expr.subst Val.val_shift Expr.shift_shift Expr.shift_zero

/-! ### `withload` with a sized callback (Core's `withload_sized`) -/

/-- **`withload ℓ v_f` at the empty row with a sized callback**: the borrow's cell witness has
the property `K`, and the callback is asked only at the views `χ` that are images `Reb β σ χ` of
the loaded witness `σ` (with `K σ`, observable at `T₁`), at `β ⊏ ⊤`. -/
theorem withload_sizedN {T₁ : VTy} (x : LifeVar) (hfree₁ : ¬ VFree x T₁) {a : Lifetime.Life}
    {δ : LSub} {Θ : LocTy} (hΘ : Θ.OK) {c : Loc → Option Life} {ℓ : Loc} {vf : Val}
    {ρ₁ ρ₂ τ : WRes} {n : Nat} {ls : List SRec} (K : WRes → Prop) (R : VTy)
    (hv : vN (ℍ := ℍ) (.imm a T₁) δ Θ n (.loc ℓ) ρ₁)
    (hK : ∀ s u σ h, ρ₁ = ResU.single ℓ (CellU.immOf s u σ h) → K σ)
    (hc : ResU.CompS ρ₁ ρ₂ τ) (hcτ : ConsistentX c τ)
    (hcb : ∀ β w χ Bχ, LtLife δ LifeCtx.empty.meetOfDom β →
      (∃ σ, K σ ∧ vO (ℍ := ℍ) T₁ δ Θ (n - 1) w σ ∧ ResU.Reb β σ χ) →
      vN (ℍ := ℍ) (T₁.immReborrow (.var x)) (δ.extend x β) Θ (n - 1) w χ → ResU.CompS ρ₂ χ Bχ →
      ConsistentX c Bχ →
      erwp (ℍ := ℍ) (Θ.view c) (opTableN OpTabN.empty) (RebPost β (vPostN R δ Θ)) (n - 1) ls
        (.app (.app (.val vf) (.val .unit)) (.val w)) Bχ) :
    erwp (ℍ := ℍ) (Θ.view c) (opTableN OpTabN.empty) (vPostN R δ Θ) n ls
      (.app (.app withload (.val (.loc ℓ))) (.val vf)) τ := by
  obtain ⟨α₀, _, ⟨l', s, w, σ, hσs, hl', rfl, _, hpay⟩, hwit⟩ := hv
  obtain rfl : ℓ = l' := loc_inj hl'
  have hΦ := LocTy.view_down hΘ.1 c
  have hQ := vPostN_down (ℍ := ℍ) R δ Θ
  refine erwp_headE hΦ hQ (.appL .hole vf) (fun μ => Head.beta μ _ (Val.loc ℓ)) rfl ?_
  refine erwp_headE hΦ hQ .hole (fun μ => Head.beta μ _ vf) rfl ?_
  have e₃ : Kont.hole.plug (Expr.subst 0 vf (Expr.subst (0 + 1) (Val.shift 1 0 (Val.loc ℓ))
        (.app (.app v0 unit') (.app load' v1)))) =
      (Kont.appR (.app (.val vf) (.val .unit)) .hole).plug
        (.app (.val (.prim .load)) (.val (Val.loc ℓ))) := by
    simp [Kont.plug, Expr.subst, Expr.shift, Val.shift, Val.loc, Expr.val, Val.prim, v0, v1,
      unit', load', Val.unit]
  rw [e₃]
  refine erwp_of_valid fun hvτ => ?_
  have hc₂ : ConsistentX c ρ₂ := consistentX_right hc hcτ hvτ
  refine erwp_bindR hΦ (opTableN_local _) (Kont.appR (.app (.val vf) (.val .unit)) .hole) ?_
  refine rwp_load_cell ls ℓ s w σ hσs _ hc ?_
  simp only [Kont.plug]
  exact withload_rebT (T := OpTabN.empty) (bnd := LifeCtx.empty.meetOfDom) ⟨_, rfl⟩ hfree₁
    (fun _ _ => ⟨fun _ _ _ h => absurd h (by simp [OpTabN.empty]),
      fun _ _ _ h => absurd h (by simp [OpTabN.empty]),
      fun _ _ _ h => absurd h (by simp [OpTabN.empty])⟩)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h => absurd h (by simp [OpTabN.empty])) (vO_le (Nat.sub_le n 1) hpay) (hwit ℓ s w σ hσs rfl)
    (fun β hLt u χ Bχ hχ hu hreb himg hBχ => by
      subst hu
      exact hcb β u χ Bχ hLt ⟨σ, hK s u σ hσs rfl, vO_le (Nat.sub_le n 1) hpay, hreb⟩ himg hBχ
        (consistentX_compS hBχ hc₂ (consistentX_allImm hχ c))) hc

/-! ### The measure at the view -/

/-- **The view `withload` hands over is `Good` at the loaded witness's size** (Core's
`good_of_image`). -/
theorem good_of_imageN {M : VTy} {x : LifeVar} {δ : LSub} {Θ : LocTy} {k k' : Nat} {β : Life}
    {w : Val} {σ χ : WRes} (hx : ¬ VFree x M) (hobs : vO (ℍ := ℍ) M δ Θ k w σ)
    (hreb : ResU.Reb β σ χ)
    (hview : vN (ℍ := ℍ) (M.immReborrow (.var x)) (δ.extend x β) Θ k' w χ) :
    Good M w χ (dsize σ) := by
  intro l S hp ψ e
  obtain ⟨u, P, B, hB, -, hle⟩ := own_split M (vO_vShape M δ Θ k w σ hobs) hp
  have hown : σ.get l = some (CellU.ownOf u) :=
    own_of_le hle (ResU.CompS.get_left_of_ne_imm hB (ResU.single_get_self _ _) (by simp)).2
  obtain ⟨q, hq, eχ, hqσ, hql, -⟩ :=
    typed_image_pos hx hp hown hreb (vN_vShape _ _ _ _ _ _ hview)
  rw [eχ] at e
  cases Option.some.inj e
  simpa using dsize_del_lt hqσ hql

/-- Every borrow's cell witness has a size (Core's `witLt_exists`). -/
theorem witLt_existsN {a : Lifetime.Life} {T : VTy} {δ : LSub} {Θ : LocTy} {k : Nat} {ℓ : Loc}
    {ρ : WRes} (hv : vN (ℍ := ℍ) (.imm a T) δ Θ k (.loc ℓ) ρ) : ∃ n, WitLt ℓ ρ n := by
  obtain ⟨-, -, ⟨l', s, u, σ, hσ, hl', rfl, -, -⟩, -⟩ := hv
  obtain rfl : ℓ = l' := loc_inj hl'
  refine ⟨dsize σ + 1, fun s' u' σ' h' hρ' => ?_⟩
  obtain ⟨-, e'⟩ := single_immOf_inj hρ'
  obtain ⟨rfl, rfl, rfl⟩ := CellU.immOf_inj e'
  exact Nat.lt_succ_self _

/-! ### Reductions -/

section Red
variable {Φ : LocFam} {Q : PostN}

end Red

/-- **The algebra applied**: `g [] r` at `β ⊏ ⊤` runs to a value of `R` (Core's `alg_call`). The
algebra holds the empty resource and is read at the run's world. -/
theorem alg_callN {A R : VTy} {y : LifeVar} {δ : LSub} {Θ₀ Θ : LocTy} (hΘ : Θ.OK)
    {c : Loc → Option Life} {N j : Nat} {ls : List SRec} {g r : Val} {β : Life} {ρ : WRes}
    (hyR : ¬ VFree y R) (hβ : LtLife δ LifeCtx.empty.meetOfDom β) (hj : j ≤ N)
    (hg : vN (ℍ := ℍ) (.bang (VTy.all y LifeCtx.empty.meetOfDom (VTy.lolli A R))) δ Θ₀ N g
      PMap.empty)
    (hr : vN (ℍ := ℍ) A (δ.extend y β) Θ j r ρ) (hc : ConsistentX c ρ) :
    erwp (ℍ := ℍ) (Θ.view c) (opTableN OpTabN.empty) (vPostN R δ Θ) j ls
      (.app (.app (.val g) (.val .unit)) (.val r)) ρ := by
  have hΦ := LocTy.view_down hΘ.1 c
  have hwp := hg.2 Θ (LocTy.extR_empty Θ₀ Θ) hΘ c (consistentX_empty c) ls β hβ
  have hwp' := cN_le (ℍ := ℍ) (C := .ret (VTy.lolli A R)) hΘ.1 hj hwp
  refine erwp_bind_frame hΦ (opTableN_local _) (.appL .hole r) (fun X => X = ρ)
    (compS_empty_left ρ) hc (erwp_of_cN_ret hwp') rfl ?_
  rintro k' hk' ls' f σ₁ X σ hcσ hf rfl hcσ' hvσ
  simp only [Kont.plug]
  have h2 := hf Θ (LocTy.extR_refl _ _) hΘ c (consistentX_left hcσ hcσ' hvσ) ls' c k' le_rfl r X σ
    hcσ (vN_le hk' hr) hcσ'
  refine erwp_mono (fun k _ v ρ' hv => ?_) (opTableN_local _) k' ls' _ σ (erwp_of_cN_ret h2)
  exact vN_cast (vN_extend_of_not_free hyR δ β) hv

/-! ### The traversal (Core's `trav_spec`) -/

section Trav
variable (M R : VTy) (y : LifeVar) (δ : LSub) (Θ : LocTy) (c : Loc → Option Life) (Nb : Nat)

/-- The recursive call through a sub-borrow `Imm 'y M` at witness size below `n` (Core's
`PSpec`). -/
def PSpecN (n : Nat) (h : Val) : Prop :=
  ∀ α ℓ ρ j ls, j ≤ Nb → vN (ℍ := ℍ) (.imm (.var y) M) (δ.extend y α) Θ j (.loc ℓ) ρ →
    WitLt ℓ ρ n → ConsistentX c ρ →
    erwp (ℍ := ℍ) (Θ.view c) (opTableN OpTabN.empty) (vPostN R δ Θ) j ls
      (.app (.app withload (.val (.loc ℓ))) (.val (cbOf h))) ρ

/-- The recursive call `h w` on a view `w` of `M` at `β` smaller than `K` (Core's `HSpec`). -/
def HSpecN (β : Life) (n K : Nat) (h : Val) : Prop :=
  ∀ w χ j ls, j ≤ Nb → sizeOf w.1 < K →
    vN (ℍ := ℍ) (M.immReborrow (.var y)) (δ.extend y β) Θ j w χ → Good M w χ n →
    ConsistentX c χ →
    erwp (ℍ := ℍ) (Θ.view c) (opTableN OpTabN.empty) (vPostN R δ Θ) j ls (.app (.val h) (.val w)) χ

/-- **The traversal** (Core's `trav_spec`). -/
theorem trav_specKN (hΘ : Θ.OK) {β : Life} {n K : Nat} {h : Val} (hyR : ¬ VFree y R)
    (hP : PSpecN (ℍ := ℍ) M R y δ Θ c Nb n h) (hH : HSpecN (ℍ := ℍ) M R y δ Θ c Nb β n K h) :
    ∀ (G : FShape), G.WF → ∀ w χ j ls, j ≤ Nb → sizeOf w.1 ≤ K → (G = .varX → sizeOf w.1 < K) →
      vN (ℍ := ℍ) ((VTy.inst M G.ty).immReborrow (.var y)) (δ.extend y β) Θ j w χ →
      Good (VTy.inst M G.ty) w χ n → ConsistentX c χ →
      erwp (ℍ := ℍ) (Θ.view c) (opTableN OpTabN.empty) (vPostN (G.res y R) (δ.extend y β) Θ) j ls
        (.app (.app (.val (travK G)) (.val h)) (.val w)) χ
  | .leaf A, hA, w, χ, j, ls, _, _, _, hview, _, _ => by
      refine travK_appN (LocTy.view_down hΘ.1 c) (vPostN_down _ _ Θ) _ h w ?_
      rw [tB_leaf]
      have e : VTy.inst M A = A := VTy.subst_closed0 hA _
      simp only [FShape.ty, e] at hview
      exact erwp_val hview
  | .refX, _, w, χ, j, ls, hj, _, _, hview, hgood, hc => by
      refine travK_appN (LocTy.view_down hΘ.1 c) (vPostN_down _ _ Θ) _ h w ?_
      rw [tB_refX]
      change vN (ℍ := ℍ) (.imm (.var y) M) (δ.extend y β) Θ j w χ at hview
      obtain ⟨ℓ, rfl⟩ : ∃ ℓ, w = Val.loc ℓ := by
        obtain ⟨-, -, ⟨ℓ, -, -, -, -, hw, -, -, -⟩, -⟩ := hview
        exact ⟨ℓ, hw⟩
      refine erwp_mono (fun k _ v ρ hv => ?_) (opTableN_local _) j ls _ χ
        (hP β ℓ χ j ls hj hview (Good.witLt hgood) hc)
      exact vN_cast (vN_extend_of_not_free hyR δ β).symm hv
  | .varX, _, w, χ, j, ls, hj, _, hlt, hview, hgood, hc => by
      refine travK_appN (LocTy.view_down hΘ.1 c) (vPostN_down _ _ Θ) _ h w ?_
      rw [tB_varX]
      refine erwp_mono (fun k _ v ρ hv => ?_) (opTableN_local _) j ls _ χ
        (hH w χ j ls hj (hlt rfl) hview hgood hc)
      exact vN_cast (vN_extend_of_not_free hyR δ β).symm hv
  | .tensor F G, hFG, w, χ, j, ls, hj, hK, _, hview, hgood, hc => by
      have hΦ := LocTy.view_down hΘ.1 c
      obtain ⟨v₁, v₂, χ₁, χ₂, rfl, hcχ, h₁, h₂⟩ := hview
      have hs₁ : sizeOf v₁.1 < K := by rw [sizeOf_pair] at hK; omega
      have hs₂ : sizeOf v₂.1 < K := by rw [sizeOf_pair] at hK; omega
      refine travK_appN hΦ (vPostN_down _ _ Θ) _ h _ ?_
      rw [tB_tensor]
      refine erwp_headE hΦ (vPostN_down _ _ Θ) .hole (fun μ => Head.letpair μ v₁ v₂ _) rfl ?_
      simp only [Kont.plug]
      rw [tensor_body]
      refine erwp_of_valid fun hvχ => ?_
      refine erwp_bind_frame hΦ (opTableN_local _)
        (.appR (.val (.lam (bindE (.app (.app (.val (travK G)) (.val (h.shift 1 0)))
          (.val (v₂.shift 1 0))) (.pair (.var 1) (.var 0))))) .hole)
        (fun X => X = χ₂) hcχ hc
        (trav_specKN hΘ hyR hP hH F hFG.1 v₁ χ₁ j ls hj (le_of_lt hs₁) (fun _ => hs₁) h₁
          (Good.tensorL hgood hcχ) (consistentX_left hcχ hc hvχ)) rfl ?_
      rintro k₁ hk₁ ls₁ r₁ σ₁ X σ hcσ hr₁ rfl hcσ' hvσ
      simp only [Kont.plug]
      refine erwp_headE hΦ (vPostN_down _ _ Θ) .hole (fun μ => Head.beta μ _ r₁) rfl ?_
      rw [tensor_body₂]
      refine erwp_bind_frame hΦ (opTableN_local _)
        (.appR (.val (.lam (.pair (.val (r₁.shift 1 0)) (.var 0)))) .hole)
        (fun Y => Y = σ₁) (ResU.CompS.comm hcσ) hcσ'
        (trav_specKN hΘ hyR hP hH G hFG.2 v₂ X k₁ ls₁ (hk₁.trans hj) (le_of_lt hs₂) (fun _ => hs₂)
          (vN_le hk₁ h₂) (Good.tensorR hgood hcχ) (consistentX_right hcσ hcσ' hvσ)) rfl ?_
      rintro k₂ hk₂ ls₂ r₂ τ₁ Y τ hcτ hr₂ rfl _ _
      simp only [Kont.plug]
      refine erwp_headE hΦ (vPostN_down _ _ Θ) .hole (fun μ => Head.beta μ _ r₂) rfl ?_
      rw [tensor_body₃]
      exact erwp_val ⟨r₁, r₂, Y, τ₁, rfl, ResU.CompS.comm hcτ, vN_le hk₂ hr₁, hr₂⟩
  | .sum F G, hFG, w, χ, j, ls, hj, hK, _, hview, hgood, hc => by
      have hΦ := LocTy.view_down hΘ.1 c
      rcases hview with ⟨v, rfl, hv⟩ | ⟨v, rfl, hv⟩
      · have hsz : sizeOf v.1 < K := by
          have : sizeOf (Val.inj₁ v).1 = 1 + sizeOf v.1 := rfl
          omega
        refine travK_appN hΦ (vPostN_down _ _ Θ) _ h _ ?_
        rw [tB_sum]
        refine erwp_headE hΦ (vPostN_down _ _ Θ) .hole (fun μ => Head.case₁ μ v _ _) rfl ?_
        simp only [Kont.plug]
        rw [sum_branch F h v Expr.inj₁ (fun _ _ _ => rfl)]
        refine erwp_bind_frame hΦ (opTableN_local _) (.appR (.val (.lam (Expr.inj₁ (.var 0)))) .hole)
          (fun E => E = PMap.empty) (ResU.comp_empty_right χ) hc
          (trav_specKN hΘ hyR hP hH F hFG.1 v χ j ls hj (le_of_lt hsz) (fun _ => hsz) hv
            (Good.sumL hgood) hc) rfl ?_
        rintro k' _ ls' r σ₁ E σ hcσ hr rfl _ _
        obtain rfl := ResU.CompS.functional hcσ (ResU.comp_empty_right σ₁)
        simp only [Kont.plug]
        refine erwp_headE hΦ (vPostN_down _ _ Θ) .hole (fun μ => Head.beta μ _ r) rfl ?_
        exact erwp_val (v := Val.inj₁ r) (.inl ⟨r, rfl, hr⟩)
      · have hsz : sizeOf v.1 < K := by
          have : sizeOf (Val.inj₂ v).1 = 1 + sizeOf v.1 := rfl
          omega
        refine travK_appN hΦ (vPostN_down _ _ Θ) _ h _ ?_
        rw [tB_sum]
        refine erwp_headE hΦ (vPostN_down _ _ Θ) .hole (fun μ => Head.case₂ μ v _ _) rfl ?_
        simp only [Kont.plug]
        rw [sum_branch G h v Expr.inj₂ (fun _ _ _ => rfl)]
        refine erwp_bind_frame hΦ (opTableN_local _) (.appR (.val (.lam (Expr.inj₂ (.var 0)))) .hole)
          (fun E => E = PMap.empty) (ResU.comp_empty_right χ) hc
          (trav_specKN hΘ hyR hP hH G hFG.2 v χ j ls hj (le_of_lt hsz) (fun _ => hsz) hv
            (Good.sumR hgood) hc) rfl ?_
        rintro k' _ ls' r σ₁ E σ hcσ hr rfl _ _
        obtain rfl := ResU.CompS.functional hcσ (ResU.comp_empty_right σ₁)
        simp only [Kont.plug]
        refine erwp_headE hΦ (vPostN_down _ _ Θ) .hole (fun μ => Head.beta μ _ r) rfl ?_
        exact erwp_val (v := Val.inj₂ r) (.inr ⟨r, rfl, hr⟩)

end Trav

/-! ### Induction on the witness size, then on the view -/

section Ind
variable {M R : VTy} {y : LifeVar} {δ : LSub} {Θ : LocTy} {c : Loc → Option Life} {Nb : Nat}

/-- No borrow has a witness of fewer than `0` cells (Core's `pSpec_zero`). -/
theorem pSpec_zeroN {h : Val} : PSpecN (ℍ := ℍ) M R y δ Θ c Nb 0 h := by
  intro α ℓ ρ j ls _ hv hn _
  obtain ⟨-, -, ⟨l', s, u, σ, hσ, hl', rfl, -, -⟩, -⟩ := hv
  exact absurd (hn s u σ hσ (by rw [loc_inj hl'])) (Nat.not_lt_zero _)

/-- **A sub-borrow at witness size below `m + 1`** (Core's `pSpec_succ`): `withload_sizedN` at
the borrow; the view it hands over is `Good` at the loaded witness's size, at most `m`. Its result
leaves the callback's `['x]` because `R` outlives every lifetime (6.60). -/
theorem pSpec_succN (hΘ : Θ.OK) {m : Nat} {h : Val} (hyM : ¬ VFree y M) (hyR : ¬ VFree y R)
    (hR : ∀ Δ a, VOutlives Δ a R)
    (hH : ∀ β, LtLife δ LifeCtx.empty.meetOfDom β → ∀ K,
      HSpecN (ℍ := ℍ) M R y δ Θ c Nb β m K h) :
    PSpecN (ℍ := ℍ) M R y δ Θ c Nb (m + 1) h := by
  intro α ℓ ρ j ls hj hv hn hc
  have hΦ := LocTy.view_down hΘ.1 c
  have hrun := withload_sizedN (T₁ := M) y hyM hΘ (vf := cbOf h) (ls := ls) (K := fun σ => dsize σ < m + 1)
    (R := R) hv hn (ResU.comp_empty_right ρ) hc ?_
  · refine erwp_mono (fun k _ v ρ' hv' => ?_) (opTableN_local _) j ls _ ρ hrun
    exact vN_cast (vN_extend_of_not_free hyR δ α) hv'
  intro β w χ Bχ hLt ⟨σ, hKσ, hobs, hreb⟩ hview hcomp hcB
  obtain rfl := eq_of_compS_empty_left hcomp
  refine cbOf_appN hΦ (fun k _ v ρ h => ⟨vN_down _ _ _ _ _ _ h.1, h.2⟩) h w ?_
  have hgood := (good_of_imageN hyM hobs hreb hview).mono (Nat.lt_succ_iff.mp hKσ)
  have e := vN_congr (ℍ := ℍ) (M.immReborrow (.var y)) (δ := (δ.extend y α).extend y β)
    (δ' := δ.extend y β) (fun z _ => find?_extend_twice δ y α β z)
  obtain ⟨γ, hγ, hβγ⟩ := hLt
  have hrun' := hH β ⟨γ, hγ, hβγ⟩ (sizeOf w.1 + 1) w Bχ (j - 1) ls
    (le_trans (Nat.sub_le j 1) hj) (Nat.lt_succ_self _) (vN_cast e hview) hgood hcB
  refine erwp_mono (fun k _ v ρ₀ hv => ⟨vN_cast (vN_extend_of_not_free hyR δ α).symm hv, ?_⟩)
    (opTableN_local _) (j - 1) ls _ Bχ hrun'
  exact vN_outlives (Δ := LifeCtx.empty) (a := .var y) (models_empty_any _)
    (find?_extend_self δ y β) (hR _ _) Θ k v ρ₀
    (vN_cast (vN_extend_of_not_free hyR δ β).symm hv)

/-- **The recursive call on a view**, at every witness bound `n` (Core's `hSpec_all`). -/
theorem hSpec_allN {F : FShape} (hF : F.WF) (hG : F.Guarded) (hΘ : Θ.OK) {g : Val} {Θ₀ : LocTy}
    (hyM : ¬ VFree y (.mu F.ty)) (hyR : ¬ VFree y R) (hR : ∀ Δ a, VOutlives Δ a R)
    (hg : vN (ℍ := ℍ) (algTy F y R) δ Θ₀ Nb g PMap.empty) :
    ∀ n β, LtLife δ LifeCtx.empty.meetOfDom β → ∀ K,
      HSpecN (ℍ := ℍ) (.mu F.ty) R y δ Θ c Nb β n K (hV F g) := by
  have hΦ := LocTy.view_down hΘ.1 c
  have step : ∀ n, PSpecN (ℍ := ℍ) (.mu F.ty) R y δ Θ c Nb n (hV F g) →
      ∀ β, LtLife δ LifeCtx.empty.meetOfDom β → ∀ K,
        HSpecN (ℍ := ℍ) (.mu F.ty) R y δ Θ c Nb β n K (hV F g) := by
    intro n hP β hβ K
    induction K with
    | zero => intro w χ j ls _ hlt; exact absurd hlt (Nat.not_lt_zero _)
    | succ K ihK =>
        intro w χ j ls hj hlt hview hgood hc
        refine hV_appN hΦ (vPostN_down _ _ Θ) F g w ?_
        have hview' := (vN_immReborrow_mu_iff (ℍ := ℍ) (A := F.ty) (FShape.Cl_ty hF) (.var y)).mp
          hview
        refine erwp_bind_frame hΦ (opTableN_local _)
          (.appR (.val (.lam (.app (.app (.val (g.shift 1 0)) (.val .unit)) (.var 0)))) .hole)
          (fun E => E = PMap.empty) (ResU.comp_empty_right χ) hc
          (trav_specKN (.mu F.ty) R y δ Θ c Nb hΘ hyR hP ihK F hF w χ j ls hj
            (Nat.lt_succ_iff.mp hlt) (fun e => by subst e; exact hG.elim) hview'
            (hgood.unroll (FShape.Cl_ty hF)) hc) rfl ?_
        rintro k' hk' ls' r σ₁ E σ hcσ hr rfl hcσ' _
        obtain rfl := ResU.CompS.functional hcσ (ResU.comp_empty_right σ₁)
        simp only [Kont.plug]
        refine erwp_headE hΦ (vPostN_down _ _ Θ) .hole (fun μ => Head.beta μ _ r) rfl ?_
        rw [alg_subst]
        exact alg_callN hΘ hyR hβ (hk'.trans hj) hg hr hcσ'
  intro n
  induction n with
  | zero => exact step 0 pSpec_zeroN
  | succ m ih => exact step (m + 1) (pSpec_succN hΘ hyM hyR hR ih)

theorem pSpec_allN {F : FShape} (hF : F.WF) (hG : F.Guarded) (hΘ : Θ.OK) {g : Val} {Θ₀ : LocTy}
    (hyM : ¬ VFree y (.mu F.ty)) (hyR : ¬ VFree y R) (hR : ∀ Δ a, VOutlives Δ a R)
    (hg : vN (ℍ := ℍ) (algTy F y R) δ Θ₀ Nb g PMap.empty) :
    ∀ n, PSpecN (ℍ := ℍ) (.mu F.ty) R y δ Θ c Nb n (hV F g)
  | 0 => pSpec_zeroN
  | m + 1 => pSpec_succN hΘ hyM hyR hR (hSpec_allN hF hG hΘ hyM hyR hR hg m)

end Ind

/-! ### The rule -/

/-- **The borrowed fold at `SemJN`** (Core's `foldImm_compatX`): `foldImm : !U(∀'y ⊏ ⊤. A_R ⊸
F R) ⊸ !U(∀'y ⊏ @c. Imm 'y (μX. T) ⊸ F R)` at every `T` of the class `FShape`, at a result type
`R` that outlives every lifetime, with `'y` free in neither `μX. T` nor `R`. -/
theorem foldImm_compatN {Δ : LifeCtx} {Γ : Ctx VTy} (F : FShape) (hF : F.WF) (hG : F.Guarded)
    (y : LifeVar) (c : Lifetime.Life) (R : VTy) (hΓ : Ctx.DeadP Γ)
    (hyM : ¬ VFree y (.mu F.ty)) (hyR : ¬ VFree y R) (hR : ∀ Δ a, VOutlives Δ a R) :
    SemJN (ℍ := ℍ) Δ Γ (.val (foldImmV F)) (.val (.lolli (algTy F y R) (foldTy F y c R))) := by
  intro δ γ Θ cv n ls ρ _ hΘ _ _ hg₀
  have hρ : ρ = PMap.empty := gN_deadP hΓ hg₀
  subst hρ
  refine cN_ret_of ?_
  show erwp (ℍ := ℍ) _ _ _ n ls (substAll γ (.val (foldImmV F))) _
  rw [substAll_closed (foldImmV_closed F)]
  refine erwp_val ?_
  intro Θ₁ _ hOK₁ c₁ _ ls₁ c₂ k₁ _ g ρv ρ' hcomp hv₁ _
  have hρv : ρv = PMap.empty := hv₁.1
  subst hρv
  obtain rfl := eq_of_compS_empty_left hcomp
  have hΦ := LocTy.view_down hOK₁.1 c₂
  refine cN_ret_of ?_
  refine erwp_headE hΦ (vPostN_down _ δ Θ₁) .hole (fun μ => Head.beta μ _ g) rfl ?_
  rw [foldImmV_subst]
  refine erwp_val ⟨rfl, ?_⟩
  intro Θ₂ _ hOK₂ c₃ _ ls₂ α hα
  have hΦ₂ := LocTy.view_down hOK₂.1 c₃
  refine cN_ret_of ?_
  refine erwp_headE hΦ₂ (vPostN_down _ _ Θ₂) .hole (fun μ => Head.beta μ _ Val.unit) rfl ?_
  rw [foldCl_subst]
  refine erwp_val ?_
  intro Θ₃ _ hOK₃ c₄ _ ls₃ c₅ k₂ hk₂ v ρv ρ'' hcomp' hv hc₅
  obtain rfl := eq_of_compS_empty_left hcomp'
  have hΦ₃ := LocTy.view_down hOK₃.1 c₅
  obtain ⟨ℓ, rfl⟩ : ∃ ℓ, v = Val.loc ℓ := by
    obtain ⟨-, -, ⟨ℓ, -, -, -, -, hw, -, -, -⟩, -⟩ := hv
    exact ⟨ℓ, hw⟩
  refine cN_ret_of ?_
  refine erwp_headE hΦ₃ (vPostN_down _ _ Θ₃) .hole (fun μ => Head.beta μ _ (Val.loc ℓ)) rfl ?_
  rw [foldLam_subst]
  refine travK_appN hΦ₃ (vPostN_down _ _ Θ₃) _ _ _ ?_
  rw [tB_refX]
  obtain ⟨m, hm⟩ := witLt_existsN hv
  refine erwp_mono (fun k _ v' ρ₀ hv' => vN_cast (vN_extend_of_not_free hyR δ α).symm hv')
    (opTableN_local _) k₂ ls₃ _ ρ'' ?_
  exact pSpec_allN (Nb := k₂) (c := c₅) hF hG hOK₃ hyM hyR hR (vN_le hk₂ hv₁) m α ℓ ρ'' k₂ ls₃
    le_rfl hv hm hc₅

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N


end
