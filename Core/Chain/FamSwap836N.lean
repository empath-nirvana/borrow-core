import Core.Chain.FamSlice836N

/-!
# Swapping two leaves of a `mut` slice at `SemJN₀`  `[spec §9]`

Core's `sliceSwapM_compatX` (`Core/SliceOps.lean`): both indices in range, the two picked leaves
are `Mut @a A` borrows. At one leaf (`i = j`) one Mut Anti-Frame opens the cell, which is read
twice and written twice; at two leaves each is opened by its own Mut Anti-Frame
(`sepRange_pick2N`), the two contents are read and written crosswise, and both leaves are sealed
again, each holding the other's content. On the chain each anti-frame is `erwp_M_antiFrame` at the
view, the leaf's cell at its view lifetime (`consistentX_get`), as in `sliceReplaceM_compatN₀`; the
inner anti-frame runs at the outer one's table (`erwp_mono`: the empty table stops nowhere). The
steps inside are taken at the index each one costs, and the content moved into the other cell keeps
its witness, which is in that cell's stratum (the leaf's uniformity clause).
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
open BoCa.BoLo (Heap Kont Head eLoad eStore)

/-- **Two distinct leaves of a range, `i < j`** (Core's `sepRange_pick2R`), the range rebuilt at
any weaker predicate: the rest is read at the weaker one. -/
theorem sepRange_pick2RW {P : Loc → WProp} {ℓ : Loc} {n i j : Nat} (hij : i < j) (hj : j < n)
    {ρ : WRes} (h : sepRange P ℓ n ρ) :
    ∃ ρi ρj ρr ρ₁, ResU.CompS ρj ρr ρ₁ ∧ ResU.CompS ρi ρ₁ ρ ∧ P (ℓ + i) ρi ∧ P (ℓ + j) ρj ∧
      ∀ Q : Loc → WProp, (∀ m ρ, P m ρ → Q m ρ) →
        ∀ σi σj σ₁ ρ', ResU.CompS σj ρr σ₁ → ResU.CompS σi σ₁ ρ' → Q (ℓ + i) σi →
          Q (ℓ + j) σj → sepRange Q ℓ n ρ' := by
  obtain ⟨m, rfl⟩ : ∃ m, n = j + (m + 1) := ⟨n - j - 1, by omega⟩
  obtain ⟨A, B, hAB, hA, ρj, C, hjC, hPj, hC⟩ := sepRange_split h
  obtain ⟨ρi, Ar, hiA, hPi, hbackA⟩ := sepRange_pickW hij hA
  obtain ⟨X, hX, hρ⟩ := compS_reassoc hiA hAB
  obtain ⟨Y, hY, hX'⟩ := compS_lcomm hjC hX
  refine ⟨ρi, ρj, Y, X, hX', hρ, hPi, hPj, fun Q hPQ σi σj σ₁ ρ' h₁ h₂ hPi' hPj' => ?_⟩
  obtain ⟨B', hB', hσ₁⟩ := compS_lcomm hY h₁
  obtain ⟨A', hA', hρ'⟩ := compS_reassoc' hσ₁ h₂
  exact sepRange_append hρ' (hbackA Q hPQ σi A' hA' hPi')
    ⟨σj, C, hB', hPj', sepRange_mono' hPQ hC⟩

/-- `sepRange_pick2RW` at two distinct leaves in either order (Core's `sepRange_pick2N`). -/
theorem sepRange_pick2NW {P : Loc → WProp} {ℓ : Loc} {n i j : Nat} (hij : i ≠ j) (hi : i < n)
    (hj : j < n) {ρ : WRes} (h : sepRange P ℓ n ρ) :
    ∃ ρi ρj ρr ρ₁, ResU.CompS ρj ρr ρ₁ ∧ ResU.CompS ρi ρ₁ ρ ∧ P (ℓ + i) ρi ∧ P (ℓ + j) ρj ∧
      ∀ Q : Loc → WProp, (∀ m ρ, P m ρ → Q m ρ) →
        ∀ σi σj σ₁ ρ', ResU.CompS σj ρr σ₁ → ResU.CompS σi σ₁ ρ' → Q (ℓ + i) σi →
          Q (ℓ + j) σj → sepRange Q ℓ n ρ' := by
  rcases Nat.lt_or_gt_of_ne hij with hlt | hgt
  · exact sepRange_pick2RW hlt hj h
  · obtain ⟨ρj, ρi, ρr, ρ₁, h₁, h₂, hPj, hPi, hback⟩ := sepRange_pick2RW hgt hi h
    obtain ⟨ρ₁', h₁', h₂'⟩ := compS_lcomm h₁ h₂
    refine ⟨ρi, ρj, ρr, ρ₁', h₁', h₂', hPi, hPj, fun Q hPQ σi σj σ₁ ρ' k₁ k₂ kPi kPj => ?_⟩
    obtain ⟨σ₁', k₁', k₂'⟩ := compS_lcomm k₁ k₂
    exact hback Q hPQ σj σi σ₁' ρ' k₁' k₂' kPj kPi

/-- `swapV`'s body after the first β step. -/
theorem swap_body₁ (v : Val) :
    Expr.subst 0 v (.letpair (.var 0) (.letpair (.var 0)
      (.case (.app (.val (.prim .idx)) (.pair (.var 3) (.var 1)))
        (.case (.app (.val (.prim .idx)) (.pair (.var 4) (.var 1))) slSwapCellsE (.var 5))
        (.var 4)))) =
      .letpair (.val v) (.letpair (.var 0)
        (.case (.app (.val (.prim .idx)) (.pair (.var 3) (.var 1)))
          (.case (.app (.val (.prim .idx)) (.pair (.var 4) (.var 1))) slSwapCellsE (.var 5))
          (.var 4))) := by
  simp [Expr.subst, slSwapCellsE]

theorem sliceSwapM_compatN₀ {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {A : VTy}
    (hΓ : Ctx.DeadP Γ) : SemJN₀ (ℍ := ℍ) Δ Γ (.val swapV) (.val (sliceSwapMTy a A)) := by
  refine sem_constN₀ hΓ rfl fun δ Θ n _ _ => ⟨rfl, ?_⟩
  intro Θ' _ hΘ' _ _ ls' c'' k _ v σ τ hcomp hv hcon
  rw [eq_of_compS_empty_left hcomp] at hcon ⊢
  obtain ⟨v₁, v₂, σ₁, σ₂, rfl, hc, ⟨ℓ, cn, rfl, hn, hs⟩, w₁, w₂, ρ₀, ρ₀', rfl, hc₂,
    ⟨⟨i, rfl⟩, rfl⟩, ⟨⟨j, rfl⟩, rfl⟩⟩ := hv
  rw [eq_of_compS_empty_left hc₂] at hc
  obtain rfl := ResU.CompS.functional hc (ResU.comp_empty_right σ₁)
  have hΦ := LocTy.view_down hΘ'.1 c''
  have hQd : PostN.Down (fun k _ v ρ => vN₀ (ℍ := ℍ) (.sliceMut a A) δ Θ' k v ρ) :=
    fun k _ v ρ h => vN_down₀ _ δ Θ' k v ρ h
  have hTd := opTableN_down OpTabN.empty_down
  refine erwp_det hΦ hTd hQd (fun μ => step1Only_plug (Head.beta μ _ _) rfl .hole) ?_
  simp only [Kont.plug]
  rw [swap_body₁]
  refine erwp_det hΦ hTd hQd
    (fun μ => step1Only_plug (Head.letpair μ (Val.arr ℓ cn) (Val.pair (Val.i32 i) (Val.i32 j)) _)
      rfl .hole) ?_
  simp only [Kont.plug]
  refine erwp_det hΦ hTd hQd
    (fun μ => step1Only_plug (Head.letpair μ (Val.i32 i) (Val.i32 j) _) rfl .hole) ?_
  simp only [Kont.plug]
  show erwp _ _ _ _ _ (slSwapBody ℓ cn i j) _
  refine erwp_det hΦ hTd hQd
    (fun μ => step1Only_plug (Head.idx μ ℓ cn i) rfl (.case .hole _ _)) ?_
  simp only [Kont.plug]
  rcases idxAns_cases ℓ cn i with ⟨hi, he⟩ | he
  swap
  · rw [he]
    refine erwp_det hΦ hTd hQd (fun μ => step1Only_plug (Head.case₂ μ Val.unit _ _) rfl .hole) ?_
    exact erwp_val (v := Val.arr ℓ cn) (vN_fam_mk₀ hn hs)
  rw [he]
  refine erwp_det hΦ hTd hQd
    (fun μ => step1Only_plug (Head.case₁ μ (Val.loc (ℓ + i.toNat)) _ _) rfl .hole) ?_
  show erwp _ _ _ _ _ (.case (.app (.val (.prim .idx)) (.val (Val.pair (Val.arr ℓ cn) (Val.i32 j))))
    (.app (.val (.lam (.app (.val (.lam
      (.seq (.app (.app (.val (.prim .store)) (.val (.loc (ℓ + i.toNat)))) (.var 0))
        (.seq (.app (.app (.val (.prim .store)) (.var 2)) (.var 1)) (.val (Val.arr ℓ cn))))))
      (.app (.val (.prim .load)) (.var 1)))))
      (eLoad (ℓ + i.toNat)))
    (.val (Val.arr ℓ cn))) _
  refine erwp_det hΦ hTd hQd
    (fun μ => step1Only_plug (Head.idx μ ℓ cn j) rfl (.case .hole _ _)) ?_
  simp only [Kont.plug]
  rcases idxAns_cases ℓ cn j with ⟨hj, he'⟩ | he'
  swap
  · rw [he']
    refine erwp_det hΦ hTd hQd (fun μ => step1Only_plug (Head.case₂ μ Val.unit _ _) rfl .hole) ?_
    exact erwp_val (v := Val.arr ℓ cn) (vN_fam_mk₀ hn hs)
  rw [he']
  refine erwp_det hΦ hTd hQd
    (fun μ => step1Only_plug (Head.case₁ μ (Val.loc (ℓ + j.toNat)) _ _) rfl .hole) ?_
  show erwp _ _ _ _ _ (slSwapCells ℓ cn (ℓ + i.toNat) (ℓ + j.toNat)) _
  refine erwp_of_valid fun hv => ?_
  set P : CPredL := fun Θ₀ j u r => vN₀ (ℍ := ℍ) A δ Θ₀ j u r with hP
  by_cases hij : i = j
  · -- one leaf, read twice and written twice
    subst hij
    obtain ⟨ρi, ρr, hci, hPi, hback⟩ := sepRange_pickW hi hs
    obtain ⟨α₀, hα₀, b, hα₀b, hm₁, hunif⟩ := hPi
    obtain ⟨l', w₀, σ₀, hσ₀, j₀, hw₀, hkj, hl', hlΘ, rfl⟩ := id hm₁
    obtain rfl : ℓ + i.toNat = l' := loc_inj hl'
    have hkm : (CellU.mutOf b w₀ σ₀ hσ₀ (famL b P Θ' j₀) hw₀).kind ≠ Kind.imm := by
      rw [CellU.kind_mutOf]; exact fun c => Kind.noConfusion c
    have hget : σ.get (ℓ + i.toNat) = some (CellU.mutOf b w₀ σ₀ hσ₀ (famL b P Θ' j₀) hw₀) :=
      (ResU.CompS.get_left_of_ne_imm hci (ResU.single_get_self _ _) hkm).2
    have hcb : c'' (ℓ + i.toNat) = some b := by
      have h := consistentX_get hcon hv hget (CellU.kind_mutOf _ _ _ _ _ _)
      rwa [CellU.at_mutOf] at h
    refine erwp_M_antiFrame hΦ (LocTy.view_some hcb hlΘ) (T := OpTabN.empty)
      (fun _ _ _ h => by cases h) _ ls' _ w₀ σ₀ hσ₀ j₀ hw₀ ρr σ hci (fun W X hW hX => ?_)
    have hwA : vN₀ (ℍ := ℍ) A δ Θ' j₀ w₀ σ₀ := (vN_above₀ A δ Θ' hσ₀).mp hw₀
    -- `X = own(w₀) ● rest`, `rest = ρr ● σ₀`
    obtain ⟨rest, hrest, hXr⟩ := compS_lcomm (ResU.CompS.comm hW) hX
    refine erwp_bindR hΦ (opTableG_local _ _) (.appR (.val (.lam _)) .hole) ?_
    refine rwp_load ls' _ w₀ _ ⟨_, rest, hXr, rfl, fun c₁ p₁ hc₁ hp₁ => ?_⟩
    obtain rfl := hc₁
    obtain rfl : X = p₁ := ResU.CompS.functional (ResU.CompS.comm hXr) hp₁
    simp only [Kont.plug]
    rcases k with _ | m
    · exact erwp_zero
    rcases m with _ | m
    · exact erwp_zero
    rw [Nat.add_sub_cancel]
    refine erwp_step (opTableG_local _ _)
      (fun μ => step1Only_plug (Head.beta μ _ w₀) rfl .hole) ?_
    simp only [Kont.plug]
    rw [slSwap_x]
    refine erwp_bindR hΦ (opTableG_local _ _) (.appR (.val (.lam _)) .hole) ?_
    refine rwp_load ls' _ w₀ _ ⟨_, rest, hXr, rfl, fun c₂ p₂ hc₂ hp₂ => ?_⟩
    obtain rfl := hc₂
    obtain rfl : X = p₂ := ResU.CompS.functional (ResU.CompS.comm hXr) hp₂
    simp only [Kont.plug]
    rcases m with _ | m
    · exact erwp_zero
    rw [Nat.add_sub_cancel]
    rcases m with _ | m
    · exact erwp_zero
    refine erwp_step (opTableG_local _ _)
      (fun μ => step1Only_plug (Head.beta μ _ w₀) rfl .hole) ?_
    simp only [Kont.plug]
    rw [slSwap_y, eStore_storeV]
    refine erwp_bindR hΦ (opTableG_local _ _) (.seq .hole _) ?_
    refine rwp_store ls' _ w₀ w₀ _ ⟨_, rest, hXr, rfl, fun c₃ p₃ hc₃ hp₃ => ?_⟩
    obtain rfl := hc₃
    simp only [Kont.plug]
    rcases m with _ | m
    · exact erwp_zero
    rw [Nat.add_sub_cancel]
    rcases m with _ | m
    · exact erwp_zero
    refine erwp_step (opTableG_local _ _) (fun μ => step1Only_plug (Head.seq μ _) rfl .hole) ?_
    simp only [Kont.plug]
    refine erwp_bindR hΦ (opTableG_local _ _) (.seq .hole _) ?_
    refine rwp_store ls' _ w₀ w₀ _
      ⟨_, rest, ResU.CompS.comm hp₃, rfl, fun c₄ p₄ hc₄ hp₄ => ?_⟩
    obtain rfl := hc₄
    simp only [Kont.plug]
    rcases m with _ | m
    · exact erwp_zero
    rw [Nat.add_sub_cancel]
    rcases m with _ | m
    · exact erwp_zero
    refine erwp_step (opTableG_local _ _) (fun μ => step1Only_plug (Head.seq μ _) rfl .hole) ?_
    refine erwp_val (v := Val.arr ℓ cn) ?_
    -- the cell sealed again at its content; the leaf back in the family
    have hwx : famL b P Θ' m w₀ ⟨σ₀, hσ₀⟩ := (vN_above₀ A δ Θ' hσ₀).mpr (vN_le₀ (by omega) hwA)
    refine ⟨w₀, σ₀, hσ₀, hwx, ρr, rest, ResU.CompS.comm hp₄, ResU.CompS.comm hrest,
      fun X' hX' => ?_⟩
    have hleaf : vN₀ (ℍ := ℍ) (.mut a A) δ Θ' m (Val.loc (ℓ + i.toNat))
        (ResU.single (ℓ + i.toNat) (CellU.mutOf b w₀ σ₀ hσ₀ (famL b P Θ' m) hwx)) :=
      ⟨α₀, hα₀, b, hα₀b, ⟨ℓ + i.toNat, w₀, σ₀, hσ₀, m, hwx, le_rfl, rfl, hlΘ, rfl⟩, hunif⟩
    exact vN_fam_mk₀ hn (hback _ (fun _ _ h => vN_le₀ (by omega) h) _ X' (ResU.CompS.comm hX') hleaf)
  · -- two leaves, each opened by its own Anti-Frame
    have hij' : i.toNat ≠ j.toNat := fun h => hij (UInt32.toNat_inj.mp h)
    obtain ⟨ρi, ρj, ρr, ρ₁, h₁r, hi₁, hPi, hPj, hback⟩ := sepRange_pick2NW hij' hi hj hs
    obtain ⟨αi, hαi, bi, hαbi, hmi, hunifi⟩ := hPi
    obtain ⟨αj, hαj, bj, hαbj, hmj, hunifj⟩ := hPj
    obtain ⟨li, wi, σi, hσi, ji, hwi, hkji, hli, hliΘ, rfl⟩ := id hmi
    obtain rfl : ℓ + i.toNat = li := loc_inj hli
    obtain ⟨lj, wj, σj, hσj, jj, hwj, hkjj, hlj, hljΘ, rfl⟩ := id hmj
    obtain rfl : ℓ + j.toNat = lj := loc_inj hlj
    -- each cell at its view lifetime
    have hkmi : (CellU.mutOf bi wi σi hσi (famL bi P Θ' ji) hwi).kind ≠ Kind.imm := by
      rw [CellU.kind_mutOf]; exact fun c => Kind.noConfusion c
    have hkmj : (CellU.mutOf bj wj σj hσj (famL bj P Θ' jj) hwj).kind ≠ Kind.imm := by
      rw [CellU.kind_mutOf]; exact fun c => Kind.noConfusion c
    have hgeti : σ.get (ℓ + i.toNat) = some (CellU.mutOf bi wi σi hσi (famL bi P Θ' ji) hwi) :=
      (ResU.CompS.get_left_of_ne_imm hi₁ (ResU.single_get_self _ _) hkmi).2
    have hgetj : ρ₁.get (ℓ + j.toNat) = some (CellU.mutOf bj wj σj hσj (famL bj P Θ' jj) hwj) :=
      (ResU.CompS.get_left_of_ne_imm h₁r (ResU.single_get_self _ _) hkmj).2
    have hcbi : c'' (ℓ + i.toNat) = some bi := by
      have h := consistentX_get hcon hv hgeti (CellU.kind_mutOf _ _ _ _ _ _)
      rwa [CellU.at_mutOf] at h
    have hcbj : c'' (ℓ + j.toNat) = some bj := by
      have h := consistentX_get (consistentX_right hi₁ hcon hv) (ResU.Valid.split hi₁ hv).2 hgetj
        (CellU.kind_mutOf _ _ _ _ _ _)
      rwa [CellU.at_mutOf] at h
    have hwAi : vN₀ (ℍ := ℍ) A δ Θ' ji wi σi := (vN_above₀ A δ Θ' hσi).mp hwi
    have hwAj : vN₀ (ℍ := ℍ) A δ Θ' jj wj σj := (vN_above₀ A δ Θ' hσj).mp hwj
    refine erwp_M_antiFrame hΦ (LocTy.view_some hcbi hliΘ) (T := OpTabN.empty)
      (fun _ _ _ h => by cases h) _ ls' _ wi σi hσi ji hwi ρ₁ σ hi₁ (fun W X hW hX => ?_)
    -- `X = ρj ● G`, `G = ρr ● W`
    obtain ⟨G, hG, hXG⟩ := compS_reassoc h₁r hX
    -- the inner anti-frame at the outer one's table: the empty table stops nowhere
    refine erwp_mono (fun _ _ _ _ h => h) (fun _ _ _ _ _ _ _ h => ?_) _ _ _ _
      (erwp_M_antiFrame hΦ (LocTy.view_some hcbj hljΘ) (T := OpTabN.empty)
        (fun _ _ _ h => by cases h) _ ls' _ wj σj hσj jj hwj G X hXG (fun W' X' hW' hX' => ?_))
    · rcases h with ⟨_, _, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ <;>
        obtain ⟨⟨-, -, hTe, -⟩, -⟩ := pure_sep_iff.mp h <;> cases hTe
    -- `X' = own_i ● K`, `K = H ● W'`, `H = ρr ● σi`
    obtain ⟨H, hH, hGo⟩ := compS_lcomm (ResU.CompS.comm hW) hG
    obtain ⟨K, hK, hX'K⟩ := compS_reassoc hGo hX'
    refine erwp_bindR hΦ (opTableG_local _ _) (.appR (.val (.lam _)) .hole) ?_
    refine rwp_load ls' _ wi _ ⟨_, K, hX'K, rfl, fun c₁ p₁ hc₁ hp₁ => ?_⟩
    obtain rfl := hc₁
    obtain rfl : X' = p₁ := ResU.CompS.functional (ResU.CompS.comm hX'K) hp₁
    simp only [Kont.plug]
    rcases k with _ | m
    · exact erwp_zero
    rcases m with _ | m
    · exact erwp_zero
    rw [Nat.add_sub_cancel]
    refine erwp_step (opTableG_local _ _)
      (fun μ => step1Only_plug (Head.beta μ _ wi) rfl .hole) ?_
    simp only [Kont.plug]
    rw [slSwap_x]
    -- `X' = own_j ● M`, `M = own_i ● L`, `L = H ● σj`
    obtain ⟨L, hL, hKL⟩ := compS_lcomm (ResU.CompS.comm hW') hK
    obtain ⟨M, hM, hX'M⟩ := compS_lcomm hKL hX'K
    refine erwp_bindR hΦ (opTableG_local _ _) (.appR (.val (.lam _)) .hole) ?_
    refine rwp_load ls' _ wj _ ⟨_, M, hX'M, rfl, fun c₂ p₂ hc₂ hp₂ => ?_⟩
    obtain rfl := hc₂
    obtain rfl : X' = p₂ := ResU.CompS.functional (ResU.CompS.comm hX'M) hp₂
    simp only [Kont.plug]
    rcases m with _ | m
    · exact erwp_zero
    rw [Nat.add_sub_cancel]
    rcases m with _ | m
    · exact erwp_zero
    refine erwp_step (opTableG_local _ _)
      (fun μ => step1Only_plug (Head.beta μ _ wj) rfl .hole) ?_
    simp only [Kont.plug]
    rw [slSwap_y, eStore_storeV]
    -- `X' = own_i ● N`, `N = own_j ● L`
    obtain ⟨N, hN, hX'N⟩ := compS_lcomm hM hX'M
    refine erwp_bindR hΦ (opTableG_local _ _) (.seq .hole _) ?_
    refine rwp_store ls' _ wi wj _ ⟨_, N, hX'N, rfl, fun c₃ p₃ hc₃ hp₃ => ?_⟩
    obtain rfl := hc₃
    simp only [Kont.plug]
    rcases m with _ | m
    · exact erwp_zero
    rw [Nat.add_sub_cancel]
    rcases m with _ | m
    · exact erwp_zero
    refine erwp_step (opTableG_local _ _) (fun μ => step1Only_plug (Head.seq μ _) rfl .hole) ?_
    simp only [Kont.plug]
    rw [eStore_storeV]
    -- `p₃ = own_j ● N'`, `N' = own_i(wj) ● L`
    obtain ⟨N', hN', hp₃N'⟩ := compS_lcomm hN (ResU.CompS.comm hp₃)
    refine erwp_bindR hΦ (opTableG_local _ _) (.seq .hole _) ?_
    refine rwp_store ls' _ wj wi _ ⟨_, N', hp₃N', rfl, fun c₄ p₄ hc₄ hp₄ => ?_⟩
    obtain rfl := hc₄
    simp only [Kont.plug]
    rcases m with _ | m
    · exact erwp_zero
    rw [Nat.add_sub_cancel]
    rcases m with _ | m
    · exact erwp_zero
    refine erwp_step (opTableG_local _ _) (fun μ => step1Only_plug (Head.seq μ _) rfl .hole) ?_
    refine erwp_val (v := Val.arr ℓ cn) ?_
    -- each content moves to the other cell with its witness, in that cell's stratum
    have hσij : σi.InStratum bj := hunifj _ _ _ _ hwAi
    have hσji : σj.InStratum bi := hunifi _ _ _ _ hwAj
    have hwi' : famL bj P Θ' m wi ⟨σi, hσij⟩ :=
      (vN_above₀ A δ Θ' hσij).mpr (vN_le₀ (by omega) hwAi)
    have hwj' : famL bi P Θ' m wj ⟨σj, hσji⟩ :=
      (vN_above₀ A δ Θ' hσji).mpr (vN_le₀ (by omega) hwAj)
    -- the cell at `j` sealed at `wi`: `N' = σi ● R`, `R = own_i(wj) ● S`, `S = ρr ● σj`
    obtain ⟨S, hS, hLS⟩ := compS_reassoc (ResU.CompS.comm hH) hL
    obtain ⟨R, hR, hN'R⟩ := compS_lcomm hLS hN'
    refine ⟨wi, σi, hσij, hwi', R, N', ResU.CompS.comm hp₄, hN'R, fun Y hY => ?_⟩
    -- the cell at `i` sealed at `wj`: `Y = own_i(wj) ● T`, `T = σj ● R'`, `R' = ρr ● cell_j`
    obtain ⟨T, hT, hYT⟩ := compS_reassoc hR hY
    obtain ⟨R', hR', hTR'⟩ := compS_reassoc (ResU.CompS.comm hS) hT
    refine ⟨wj, σj, hσji, hwj', R', T, hYT, hTR', fun Z hZ => ?_⟩
    have hleafi : vN₀ (ℍ := ℍ) (.mut a A) δ Θ' m (Val.loc (ℓ + i.toNat))
        (ResU.single (ℓ + i.toNat) (CellU.mutOf bi wj σj hσji (famL bi P Θ' m) hwj')) :=
      ⟨αi, hαi, bi, hαbi, ⟨ℓ + i.toNat, wj, σj, hσji, m, hwj', le_rfl, rfl, hliΘ, rfl⟩, hunifi⟩
    have hleafj : vN₀ (ℍ := ℍ) (.mut a A) δ Θ' m (Val.loc (ℓ + j.toNat))
        (ResU.single (ℓ + j.toNat) (CellU.mutOf bj wi σi hσij (famL bj P Θ' m) hwi')) :=
      ⟨αj, hαj, bj, hαbj, ⟨ℓ + j.toNat, wi, σi, hσij, m, hwi', le_rfl, rfl, hljΘ, rfl⟩, hunifj⟩
    exact vN_fam_mk₀ hn (hback _ (fun _ _ h => vN_le₀ (by omega) h) _ _ R' Z
      (ResU.CompS.comm hR') (ResU.CompS.comm hZ) hleafi hleafj)

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
