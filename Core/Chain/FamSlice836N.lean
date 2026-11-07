import Core.Chain.Fam836N

/-!
# Writes through a `mut` slice at `SemJN₀`  `[spec §9]`

Core's `sliceReplaceM_compatX` (`Core/SliceOps.lean`) is `arrReplace_compatX` with the picked leaf
a `Mut @a A` borrow: the Mut Anti-Frame at the leaf (`wpTS_M_antiFrameX`) opens the cell for the
load and the store, and the leaf is sealed again holding the new element. On the chain the
anti-frame is `erwp_M_antiFrame` at the view, the leaf's cell at its view lifetime
(`consistentX_get`), as in `withswap_compatN`; the steps inside it are `arrReplace_compatN`'s, each
at the index it costs (the anti-frame's postcondition reads the cell's member at the index of the
end).
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

/-- **The leaf at `ℓ + i`, with the rest of the range framed** (`sepRange_pick`), the range
rebuilt at any weaker predicate: the rest is read at the weaker one. -/
theorem sepRange_pickW {P : Loc → WProp} {ℓ : Loc} {n i : Nat} (hi : i < n) {ρ : WRes}
    (h : sepRange P ℓ n ρ) :
    ∃ ρi ρr, ResU.CompS ρi ρr ρ ∧ P (ℓ + i) ρi ∧
      ∀ Q : Loc → WProp, (∀ m ρ, P m ρ → Q m ρ) →
        ∀ σ ρ', ResU.CompS σ ρr ρ' → Q (ℓ + i) σ → sepRange Q ℓ n ρ' := by
  have hn : n = i + ((n - i - 1) + 1) := by omega
  rw [hn] at h
  obtain ⟨ρa, ρb, hab, ha, ρi, ρc, hic, hi', hc⟩ := sepRange_split h
  obtain ⟨ρr, hr, hρ⟩ := compS_lcomm hic hab
  refine ⟨ρi, ρr, hρ, hi', fun Q hPQ σ ρ' hσ hP => ?_⟩
  obtain ⟨σc, hσc, hρ'⟩ := compS_lcomm hr hσ
  rw [hn]
  exact sepRange_append hρ' (sepRange_mono' hPQ ha) ⟨σ, ρc, hσc, hP, sepRange_mono' hPQ hc⟩

/-- **`slice_replace_mut` at `SemJN₀`** (Core's `sliceReplaceM_compatX`): in range, the picked
leaf's cell is opened by the Mut Anti-Frame at the view (`erwp_M_antiFrame`), read (`rwp_load`)
and written (`rwp_store`), and sealed again holding the new element, the leaf back in the family
beside the old element; out of range, the element is handed back. -/
theorem sliceReplaceM_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {A : VTy}
    (hΓ : Ctx.DeadP Γ) : SemJN₀ (ℍ := ℍ) Δ Γ (.val replaceV) (.val (sliceReplaceMTy a A)) := by
  refine sem_constN hΓ rfl fun δ Θ n _ _ => ⟨rfl, ?_⟩
  intro Θ' _ hΘ' _ _ ls' c'' k _ v σ τ hcomp hv hcon
  rw [eq_of_compS_empty_left hcomp] at hcon ⊢
  obtain ⟨v₁, v₂, σ₁, σ₂, rfl, hc, ⟨ℓ, cn, rfl, hn, hs⟩, w₁, x, ρ₀, σx, rfl, hc₂,
    ⟨⟨i, rfl⟩, rfl⟩, hx⟩ := hv
  rw [eq_of_compS_empty_left hc₂] at hc
  have hΦ := LocTy.view_down hΘ'.1 c''
  have hQd : PostN.Down (fun k _ v ρ => vN₀ (ℍ := ℍ)
      (.tensor (.sliceMut a A) (.sum A A)) δ Θ' k v ρ) :=
    fun k _ v ρ h => vN_down₀ _ δ Θ' k v ρ h
  have hTd := opTableN_down OpTabN.empty_down
  refine erwp_det hΦ hTd hQd (fun μ => step1Only_plug (Head.beta μ _ _) rfl .hole) ?_
  simp only [Kont.plug]
  rw [replace_body₁]
  refine erwp_det hΦ hTd hQd
    (fun μ => step1Only_plug (Head.letpair μ (Val.arr ℓ cn) (Val.pair (Val.i32 i) x) _) rfl .hole) ?_
  simp only [Kont.plug]
  rw [replace_body₂]
  refine erwp_det hΦ hTd hQd
    (fun μ => step1Only_plug (Head.letpair μ (Val.i32 i) x _) rfl .hole) ?_
  simp only [Kont.plug]
  rw [replace_body₃]
  refine erwp_det hΦ hTd hQd
    (fun μ => step1Only_plug (Head.idx μ ℓ cn i) rfl (.case .hole _ _)) ?_
  simp only [Kont.plug]
  rcases idxAns_cases ℓ cn i with ⟨hi, he⟩ | he
  · rw [he]
    refine erwp_det hΦ hTd hQd
      (fun μ => step1Only_plug (Head.case₁ μ (Val.loc (ℓ + i.toNat)) _ _) rfl .hole) ?_
    simp only [Kont.plug]
    rw [replace_in]
    refine erwp_of_valid fun hv => ?_
    obtain ⟨ρi, ρr, hci, hPi, hback⟩ := sepRange_pickW hi hs
    -- the leaf: a `Mut @a A` borrow, its cell at its view lifetime
    obtain ⟨α₀, hα₀, b, hα₀b, hm₁, hunif⟩ := hPi
    set P : CPredL := fun Θ₀ j u r => vN₀ (ℍ := ℍ) A δ Θ₀ j u r with hP
    obtain ⟨l', w₀, σ₀, hσ₀, j₀, hw₀, hkj, hl', hlΘ, rfl⟩ := id hm₁
    obtain rfl : ℓ + i.toNat = l' := loc_inj hl'
    -- `σ = cell ● F`, `F = ρr ● σx`
    obtain ⟨F, hF, hσ⟩ := compS_reassoc hci hc
    have hkm : (CellU.mutOf b w₀ σ₀ hσ₀ (famL b P Θ' j₀) hw₀).kind ≠ Kind.imm := by
      rw [CellU.kind_mutOf]; exact fun c => Kind.noConfusion c
    have hget : σ.get (ℓ + i.toNat) = some (CellU.mutOf b w₀ σ₀ hσ₀ (famL b P Θ' j₀) hw₀) :=
      (ResU.CompS.get_left_of_ne_imm hσ (ResU.single_get_self _ _) hkm).2
    have hcb : c'' (ℓ + i.toNat) = some b := by
      have h := consistentX_get hcon hv hget (CellU.kind_mutOf _ _ _ _ _ _)
      rwa [CellU.at_mutOf] at h
    refine erwp_M_antiFrame hΦ (LocTy.view_some hcb hlΘ) (T := OpTabN.empty)
      (fun _ _ _ h => by cases h) _ ls' _ w₀ σ₀ hσ₀ j₀ hw₀ F σ hσ (fun W X hW hX => ?_)
    have hwA : vN₀ (ℍ := ℍ) A δ Θ' j₀ w₀ σ₀ := (vN_above₀ A δ Θ' hσ₀).mp hw₀
    -- `X = own(w₀) ● rest`, `rest = F ● σ₀`
    obtain ⟨rest, hrest, hXr⟩ := compS_lcomm (ResU.CompS.comm hW) hX
    refine erwp_bindR hΦ (opTableG_local _ _)
      (.pairR (Val.arr ℓ cn) (.inj₁ (.appR (.val (.lam _)) .hole))) ?_
    refine rwp_load ls' _ w₀ _ ⟨_, rest, hXr, rfl, fun c₁ p₁ hc₁ hp₁ => ?_⟩
    obtain rfl := hc₁
    obtain rfl : X = p₁ := ResU.CompS.functional (ResU.CompS.comm hXr) hp₁
    simp only [Kont.plug]
    -- the steps inside the anti-frame, each at the index it costs
    rcases k with _ | m
    · exact erwp_zero
    rcases m with _ | m
    · exact erwp_zero
    rw [Nat.add_sub_cancel]
    refine erwp_step (opTableG_local _ _)
      (fun μ => step1Only_plug (Head.beta μ _ w₀) rfl (.pairR (Val.arr ℓ cn) (.inj₁ .hole))) ?_
    simp only [Kont.plug]
    rw [replace_store, eStore_storeV]
    refine erwp_bindR hΦ (opTableG_local _ _)
      (.pairR (Val.arr ℓ cn) (.inj₁ (.seq .hole (.val w₀)))) ?_
    refine rwp_store ls' _ w₀ x _ ⟨_, rest, hXr, rfl, fun c₃ p₃ hc₃ hp₃ => ?_⟩
    obtain rfl := hc₃
    simp only [Kont.plug]
    rcases m with _ | m
    · exact erwp_zero
    rw [Nat.add_sub_cancel]
    rcases m with _ | m
    · exact erwp_zero
    refine erwp_step (opTableG_local _ _)
      (fun μ => step1Only_plug (Head.seq μ _) rfl (.pairR (Val.arr ℓ cn) (.inj₁ .hole))) ?_
    simp only [Kont.plug]
    refine erwp_val (v := Val.pair (Val.arr ℓ cn) (Val.inj₁ w₀)) ?_
    -- the cell sealed again at the new element; the leaf back in the family beside the old one
    have hσx : σx.InStratum b := hunif _ _ _ _ hx
    have hwx : famL b P Θ' m x ⟨σx, hσx⟩ := (vN_above₀ A δ Θ' hσx).mpr (vN_le₀ (by omega) hx)
    -- `rest = F ● σ₀`, `F = ρr ● σx`: `rest = σx ● R`, `R = ρr ● σ₀`
    obtain ⟨R, hR, hrestR⟩ := compS_reassoc (ResU.CompS.comm hF) hrest
    refine ⟨x, σx, hσx, hwx, R, rest, ResU.CompS.comm hp₃, hrestR, fun X' hX' => ?_⟩
    -- `X' = R ● leaf = (ρr ● leaf) ● σ₀`
    obtain ⟨L, hL, hX'L⟩ := compS_exch hR hX'
    have hleaf : vN₀ (ℍ := ℍ) (.mut a A) δ Θ' m (Val.loc (ℓ + i.toNat))
        (ResU.single (ℓ + i.toNat) (CellU.mutOf b x σx hσx (famL b P Θ' m) hwx)) :=
      ⟨α₀, hα₀, b, hα₀b, ⟨ℓ + i.toNat, x, σx, hσx, m, hwx, le_rfl, rfl, hlΘ, rfl⟩, hunif⟩
    have hfam : vN₀ (ℍ := ℍ) (.sliceMut a A) δ Θ' m (Val.arr ℓ cn) L :=
      vN_fam_mk hn (hback _ (fun _ _ h => vN_le₀ (by omega) h) _ L (ResU.CompS.comm hL) hleaf)
    exact ⟨_, _, L, σ₀, rfl, hX'L, hfam,
      .inl ⟨w₀, rfl, vN_le₀ (by omega) hwA⟩⟩
  · rw [he]
    refine erwp_det hΦ hTd hQd
      (fun μ => step1Only_plug (Head.case₂ μ Val.unit _ _) rfl .hole) ?_
    simp only [Kont.plug]
    rw [replace_out]
    exact erwp_val (v := Val.pair (Val.arr ℓ cn) (Val.inj₂ x))
      ⟨_, _, σ₁, σx, rfl, hc, vN_fam_mk hn hs, .inr ⟨x, rfl, hx⟩⟩

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
