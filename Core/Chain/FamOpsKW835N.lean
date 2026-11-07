import Core.Chain.CountKW835N

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

/-!
# The family operations at the typed world  `[spec §11, §42]`

`slice_borrow_mut` at the pure row (`sliceBorrowM_compatN`, its callback stopping nowhere, so the
family's frame is `rwp_M_frameListN` at `erwp`), `slice_replace` (`sliceReplaceM_compatN`),
`slice_swap` (`sliceSwapM_compatN`) and `array_new` (`arrNew_compatN`) at `SemJN`. A value's
judgment is `erwp` at the empty table (`cN_ret_of`); a callback's `F` answer is read back there
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

/-- A `mut` leaf at `α` is a value of `Mut 'x A` at `δ['x ↦ α]`. -/
theorem vN_mutLeaf {x : LifeVar} {A : VTy} (hx : ¬ VFree x A) {δ : LSub} {α : Life} {Θ : LocTy}
    {n : Nat} {m : Loc} {ρ : WRes} (h : mutLeafN (ℍ := ℍ) A δ α Θ n m ρ) :
    vN (ℍ := ℍ) (.mut (.var x) A) (δ.extend x α) Θ n (Val.loc m) ρ := by
  obtain ⟨b, hab, hm, hu⟩ := h
  have hAδ : vN (ℍ := ℍ) A (δ.extend x α) = vN (ℍ := ℍ) A δ := vN_extend_of_not_free hx δ α
  refine ⟨α, interp_ext_self δ x α, b, hab, ?_, fun Θ' j u r h => hu Θ' j u r (hAδ ▸ h)⟩
  rw [hAδ]; exact hm

/-- **One Mut Frame per place, around one expression** (Core's `wpTS_M_frameList`), at the chain:
the list induction over `rwp_M_frame`, each frame its own key in the world. `Ψ` is the
callback's postcondition at the world it ends at: in the stratum `β′`, and stable from a world
with one more key to the world without it at a resource in the key's stratum (`vN_local`). -/
theorem rwp_M_frameListN {A : VTy} {δ : LSub} {β β' : Life}
    (hunif : ∀ Θ j u r, vN (ℍ := ℍ) A δ Θ j u r → r.InStratum β)
    (Ψ : LocTy → PostN) (hΨs : ∀ Θ k ls v ρ, Ψ Θ k ls v ρ → ρ.InStratum β')
    (hΨl : ∀ (Θ : LocTy) (l : Loc) (α : Life) (F : Nat → Val → SPropS Loc Val α) k ls v ρ,
      ρ.InStratum α → Ψ (Θ.add l α F) k ls v ρ → Ψ Θ k ls v ρ)
    (e : Expr) (ls : List SRec) :
    ∀ (I : List Loc) (Θ : LocTy) (c : Loc → Option Life) (n : Nat) (ρo ρH ρ : WRes) (γ : Life),
      Θ.OK → ConsistentX c ρ → ResU.CompS ρo ρH ρ →
      sepList (fun m => vN (ℍ := ℍ) (.ref A) δ Θ n (Val.loc m)) I ρo →
      (∀ α, α < γ → ρH.InStratum α ∧ ∀ (Θ' : LocTy) (c' : Loc → Option Life), Θ.ExtA Θ' →
        Θ'.OK → ∀ ρm ρ', sepList (mutLeafN (ℍ := ℍ) A δ α Θ' n) I ρm → ResU.CompS ρH ρm ρ' →
          ConsistentX c' ρ' → rwp (ℍ := ℍ) (Θ'.view c') (Ψ Θ') n ls e ρ') →
      rwp (ℍ := ℍ) (Θ.view c) (fun k ls' v ρ' => ∃ ρ₁ ρ₂, ResU.CompS ρ₁ ρ₂ ρ' ∧
        sepList (fun m => vN (ℍ := ℍ) (.ref A) δ Θ k (Val.loc m)) I ρ₁ ∧ Ψ Θ k ls' v ρ₂)
        n ls e ρ
  | [], Θ, c, n, ρo, ρH, ρ, γ, hΘ, hc, hcρ, ho, hH => by
      obtain ⟨rfl, -⟩ := ho
      rw [eq_of_compS_empty_left hcρ] at hc ⊢
      have h := (hH (↓γ) (Life.down_sqsubset γ)).2 Θ c (LocTy.extA_refl Θ) hΘ PMap.empty ρH
        ⟨rfl, trivial⟩ (ResU.comp_empty_right ρH) hc
      exact rwp_mono (fun k ls' v σ h' =>
        ⟨PMap.empty, σ, compS_empty_left σ, ⟨rfl, trivial⟩, h'⟩) h
  | ℓ :: I, Θ, c, n, ρo, ρH, ρ, γ, hΘ, hc, hcρ, ho, hH => by
      obtain ⟨ρ0, ρr, hc0, hleaf, hrest⟩ := ho
      obtain ⟨l, u, σ, hl, hcl, hu⟩ := hleaf
      obtain rfl : ℓ = l := loc_inj hl
      -- `ρ = ρ0 ● F`, `F = ρr ● ρH`
      obtain ⟨F, hF, hρ⟩ := compS_reassoc hc0 hcρ
      refine rwp_of_erwp_empty (erwp_of_valid fun hv => erwp_of_rwp ?_)
      have hvρ0 : ResU.Valid ρ0 := (ResU.Valid.split hρ hv).1
      have hko : (CellU.ownOf (Loc := Loc) u).kind ≠ Kind.imm := by simp
      have hown : ρ0.get ℓ = some (CellU.ownOf u) :=
        (ResU.CompS.get_left_of_ne_imm hcl (ResU.single_get_self _ _) hko).2
      have hcF : ConsistentX c F := consistentX_right hρ hc hv
      have hcσ : ConsistentX c σ := consistentX_right hcl (consistentX_left hρ hc hv) hvρ0
      -- the outer frame's lifetime: fresh, below the frame's rest, `β` and `β′`
      obtain ⟨βF, hβF⟩ := ResU.exists_stratum F
      obtain ⟨α₁, hα₁le, hfr⟩ := LocTy.exists_fresh hΘ.2 (βF ⊓ β ⊓ β')
      have hα₁F : α₁ ≤ βF := hα₁le.trans (inf_le_left.trans inf_le_left)
      have hα₁β : α₁ ≤ β := hα₁le.trans (inf_le_left.trans inf_le_right)
      have hα₁β' : α₁ ≤ β' := hα₁le.trans inf_le_right
      set P : CPredL := fun Θ' j w r => vN (ℍ := ℍ) A δ Θ' j w r with hP
      set Fm : Nat → Val → SPropS Loc Val α₁ := famL α₁ P Θ with hFm
      have hFmD : DownFam α₁ Fm := vN_fam_down A δ α₁ Θ
      have houtP : σ.InStratum α₁ := (hunif Θ n u σ hu).mono hα₁β
      have hwit : Fm n u ⟨σ, houtP⟩ := (vN_above A δ Θ houtP).mpr hu
      set Θ₁ := Θ.add ℓ α₁ Fm with hΘ₁
      set c₁ := setLife c ℓ α₁ with hc₁
      have hOK₁ : Θ₁.OK := by
        obtain ⟨N, hN⟩ := hΘ.2
        exact ⟨LocTy.down_add hΘ.1 ℓ hFmD, ⟨min N (↓α₁), LocTy.fresh_add hN (min_le_left _ _)
          (lt_of_le_of_lt (min_le_right _ _) (Life.down_sqsubset α₁)) ℓ Fm⟩⟩
      have hE₁ : Θ.ExtA Θ₁ := LocTy.extA_add hfr ℓ Fm
      have hview : Θ₁.view c₁ = (Θ.view c).set ℓ α₁ Fm := LocTy.view_add Θ c ℓ α₁ Fm
      have hcF₁ : ConsistentX c₁ F := consistentX_setLife hcF (exS_none_of_part hρ hv hown hko) α₁
      have hcσ₁ : ConsistentX c₁ σ :=
        consistentX_setLife hcσ (exS_none_of_part hcl hvρ0 (ResU.single_get_self _ _) hko) α₁
      have hΦ : (Θ.view c).Down := LocTy.view_down hΘ.1 c
      refine rwp_M_frame hΦ hFmD le_rfl houtP (hβF.mono hα₁F) hwit hcl hρ (fun BM hBM => ?_)
      rw [← hview]
      -- `BM = ρr ● R`, `R = ρH ● cell`
      obtain ⟨R, hR, hBMR⟩ := compS_reassoc hF hBM
      have hcBM : ConsistentX c₁ BM := consistentX_compS hBM hcF₁
        (consistentX_single_mut hcσ₁ (by simp [hc₁, setLife]))
      obtain ⟨βR, hβR⟩ := ResU.exists_stratum R
      have hrest₁ : sepList (fun m => vN (ℍ := ℍ) (.ref A) δ Θ₁ n (Val.loc m)) I ρr :=
        sepList_mono' (fun m τ h => vN_extA (.ref A) δ hE₁ n _ τ h) hrest
      refine rwp_mono (fun k ls' v ρ' h => ?_)
        (rwp_M_frameListN hunif Ψ hΨs hΨl e ls I Θ₁ c₁ n ρr R BM (βR ⊓ α₁ ⊓ γ) hOK₁ hcBM hBMR
          hrest₁ (fun α₂ hα₂ => ⟨hβR.mono (le_of_lt (lt_of_lt_of_le hα₂
            (inf_le_left.trans inf_le_left))), ?_⟩))
      · -- the outer frame's postcondition from the inner ones'
        obtain ⟨ρ₁, ρ₂, hc12, ho1, hψ⟩ := h
        have hs1 : ρ₁.InStratum α₁ := sepList_closed (ResU.inStratum_empty α₁)
          (fun _ _ _ hc a b => inStratum_compS hc a b)
          (fun m τ hm => ownLeafN_inStratum hα₁β hunif hm) ho1
        have hs2 : ρ₂.InStratum α₁ := (hΨs _ _ _ _ _ hψ).mono hα₁β'
        refine ⟨inStratum_compS hc12 hs1 hs2, fun w Y hY σ' ⟨hσ', hFσ⟩ Z hZ => ?_⟩
        have ho1' : sepList (fun m => vN (ℍ := ℍ) (.ref A) δ Θ k (Val.loc m)) I ρ₁ :=
          sepList_mono_down (R := fun τ => τ.InStratum α₁)
            (fun _ _ _ hc h => ⟨ResU.CompS.inStratum_left hc h,
              ResU.CompS.inStratum_left (ResU.CompS.comm hc) h⟩)
            (fun m τ hτ hm => vN_local (.ref A) δ Θ ℓ α₁ Fm k _ τ hτ hm) hs1 ho1
        have hψ' := hΨl Θ ℓ α₁ Fm k ls' v ρ₂ hs2 hψ
        have hwA : vN (ℍ := ℍ) A δ Θ k w σ' := (vN_above A δ Θ hσ').mp hFσ
        obtain ⟨cp, hcp, hZ'⟩ := compS_reassoc hY hZ
        obtain ⟨oc, hoc, hZ''⟩ := compS_exch hc12 hZ'
        exact ⟨oc, ρ₂, hZ'', ⟨cp, ρ₁, ResU.CompS.comm hoc, ⟨ℓ, w, σ', rfl, hcp, hwA⟩, ho1'⟩, hψ'⟩
      · -- the inner frames' callback: the outer leaf, at `α₂ ⊑ α₁`, heads the family
        intro Θ' c' hE hOK' ρm₂ ρ' hm₂ hcomp hc'
        have hα₂γ : α₂ < γ := lt_of_lt_of_le hα₂ inf_le_right
        have hα₂α₁ : α₂ ≤ α₁ := le_of_lt (lt_of_lt_of_le hα₂ (inf_le_left.trans inf_le_right))
        obtain ⟨X, hX, hρ'X⟩ := compS_reassoc hR hcomp
        have hlead : mutLeafN (ℍ := ℍ) A δ α₂ Θ' n ℓ
            (ResU.single ℓ (CellU.mutOf α₁ u σ houtP (Fm n) hwit)) :=
          ⟨α₁, hα₂α₁, mutL_extR (hE.extR _) (lend_mutL Θ ℓ α₁ P le_rfl houtP hwit),
            fun Θ'' j w r h => (hunif Θ'' j w r h).mono hα₁β⟩
        exact (hH α₂ hα₂γ).2 Θ' c' (LocTy.extA_trans hE₁ hE) hOK' X ρ' ⟨_, ρm₂, hX, hlead, hm₂⟩
          hρ'X hc'

/-! ### `slice_borrow_mut` at the pure row -/

/-- **`slice_borrow_mut` is a value of its type** (Core's `sliceBorrowM_compatX`):
`withbor` at `Array A ⊸ (∀'x ⊏ @Δ. [Mut 'x A] ⊸ ['x] B) ⊸ Array A ⊗ B`. The source family at
the callback's world (`vN_extR`); the `n` Mut Frames around the callback (`rwp_M_frameListN` at
the family's range, `sepRange_eq_sepList`), the payloads' stratum and the result's from the side
conditions by 6.60 at `↓@bδ` (`vN_outlivesLe`), the callback's lifetimes below the bound and the
callback's stratum; inside, `withbor2_compatN`'s steps: `f ()` framed beside the leaves, the
result applied to the family `[Mut 'x A]` (`vN_mutLeaf` at each leaf), the result `['x] B` read at
`δ`. -/
theorem sliceBorrowM_sem {Δ : LifeCtx} {x : LifeVar} {A B : VTy} {δ : LSub} (hδ : Δ.Models δ)
    (hsideA : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A)
    (hsideB : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b B) (hA : ¬ VFree x A) (hB : ¬ VFree x B)
    (Θ₀ : LocTy) (n : Nat) :
    vN (ℍ := ℍ) (sliceBorrowMTy x Δ.meetOfDom A B) δ Θ₀ n withborVal PMap.empty := by
  intro Θ₂ _ hΘ₂ c₁ _ ls c₂ k hk u ρv ρu hc hu _
  obtain rfl := eq_of_compS_empty_left hc
  obtain ⟨l, cn, rfl, hn, hs⟩ := hu
  have hΦ₂ : (Θ₂.view c₂).Down := LocTy.view_down hΘ₂.1 c₂
  refine cN_ret_of ?_
  refine erwp_det hΦ₂ (opTableN_down OpTabN.empty_down) (fun k _ v ρ h => vN_down _ δ Θ₂ k v ρ h)
    (fun μ => step1Only_plug (Head.beta μ _ (Val.arr l cn)) rfl .hole) ?_
  have e₁ : Kont.hole.plug (Expr.subst 0 (Val.arr l cn)
      (Val.lam (.pair BoCa.v1 (.app (.app BoCa.v0 unit') BoCa.v1))).1) =
      (withborAtV (Val.arr l cn)).1 := by
    simp [Kont.plug, Expr.subst, withborAtV, BoCa.v0, BoCa.v1, unit', Val.lam,
      Expr.val, Val.unit, shift_arr]
  rw [e₁]
  refine erwp_val (v := withborAtV (Val.arr l cn)) ?_
  intro Θ' hE₃ hΘ' c _ ls' c' k' hk' f ρf ρ'' hc' hf hcon
  obtain ⟨l₁, cn₁, he, hn', hs'⟩ := vN_le hk'
    (vN_extR (.array A) δ k _ ρu hE₃ ⟨l, cn, rfl, hn, hs⟩)
  obtain ⟨rfl, rfl⟩ := Val.arr_inj he
  have hΦ : (Θ'.view c').Down := LocTy.view_down hΘ'.1 c'
  refine cN_ret_of ?_
  refine erwp_det hΦ (opTableN_down OpTabN.empty_down) (fun k _ v ρ h => vN_down _ δ Θ' k v ρ h)
    (fun μ => step1Only_plug (Head.beta μ _ f) rfl .hole) ?_
  have e₂ : Kont.hole.plug (Expr.subst 0 f
      (.pair (.val (Val.arr l cn)) (.app (.app BoCa.v0 unit') (.val (Val.arr l cn))))) =
      (Kont.pairR (Val.arr l cn) (Kont.appL Kont.hole (Val.arr l cn))).plug
        (.app (.val f) (.val Val.unit)) := by
    simp [Kont.plug, Expr.subst, BoCa.v0, unit', Expr.val, Val.unit, subst_arr]
  rw [e₂]
  refine erwp_of_valid fun hv'' => ?_
  -- the side conditions: the payloads' and the result's strata (6.60 at `↓@bδ`)
  obtain ⟨a, hdefa, hOa⟩ := hsideA
  obtain ⟨βP, hβP⟩ := hdefa δ hδ
  have hunif : ∀ Θ j w r, vN (ℍ := ℍ) A δ Θ j w r → r.InStratum (↓βP) :=
    vN_outlivesLe hδ hβP (Life.down_sqsubset βP) hOa
  obtain ⟨b, hdefb, hOb⟩ := hsideB
  obtain ⟨βB, hβB⟩ := hdefb δ hδ
  have hBs : ∀ Θ j w r, vN (ℍ := ℍ) B δ Θ j w r → r.InStratum (↓βB) :=
    vN_outlivesLe hδ hβB (Life.down_sqsubset βB) hOb
  obtain ⟨m, hm⟩ : ∃ m, Δ.meetOfDom.interp δ = some m :=
    Lifetime.Life.interp_defined_of_wf hδ (Lifetime.meetOfDomL_wf Δ.entries)
  obtain ⟨βf, hβf⟩ := ResU.exists_stratum ρf
  have hAδ : ∀ α, vN (ℍ := ℍ) A (δ.extend x α) = vN (ℍ := ℍ) A δ :=
    fun α => vN_extend_of_not_free hA δ α
  have hBδ : ∀ α, vN (ℍ := ℍ) B (δ.extend x α) = vN (ℍ := ℍ) B δ :=
    fun α => vN_extend_of_not_free hB δ α
  -- the frames' postcondition: the handle beside a result of `B`
  let Ψ : LocTy → PostN := fun Θ k _ v ρ => ∃ w, v = Val.pair (Val.arr l cn) w ∧
    vN (ℍ := ℍ) B δ Θ k w ρ
  refine erwp_of_rwp (rwp_mono (fun k ls₁ v ρ' h => ?_)
    (rwp_M_frameListN hunif Ψ (fun Θ k _ v ρ ⟨w, _, hw⟩ => hBs Θ k w ρ hw)
      (fun Θ l₀ α F k _ v ρ hρ ⟨w, hvw, hw⟩ => ⟨w, hvw, vN_local B δ Θ l₀ α F k w ρ hρ hw⟩)
      _ ls' (rangeLocs l cn.toNat) Θ' c' k' ρu ρf ρ'' (m ⊓ βf) hΘ' hcon hc'
      (by rw [← sepRange_eq_sepList]; exact hs') (fun α hα => ⟨hβf.mono (le_of_lt
        (lt_of_lt_of_le hα inf_le_right)), ?_⟩)))
  · -- the returned leaves are the array again, beside the callback's result
    obtain ⟨ρ₁, ρ₂, hc12, ho, w, rfl, hw⟩ := h
    exact ⟨Val.arr l cn, w, ρ₁, ρ₂, rfl, hc12,
      ⟨l, cn, rfl, hn', by rw [sepRange_eq_sepList]; exact ho⟩, hw⟩
  -- the callback, at the frames' world and view, from the leaves at `α`
  intro Θ'' c'' hE hOK'' ρm ρ₃ hml hcomp hc''
  refine rwp_of_erwp_empty (erwp_of_valid fun hv₃ => erwp_of_rwp ?_)
  have hLt : LtLife δ Δ.meetOfDom α := ⟨m, hm, lt_of_lt_of_le hα inf_le_left⟩
  have hΦi : (Θ''.view c'').Down := LocTy.view_down hOK''.1 c''
  have hcf : ConsistentX c'' ρf := consistentX_left hcomp hc'' hv₃
  have hcm : ConsistentX c'' ρm := consistentX_right hcomp hc'' hv₃
  have hfam : vN (ℍ := ℍ) (.sliceMut (.var x) A) (δ.extend x α) Θ'' k' (Val.arr l cn) ρm :=
    ⟨l, cn, rfl, hn', by rw [sepRange_eq_sepList]; exact sepList_mono' (fun _ _ h => vN_mutLeaf hA h) hml⟩
  refine rwp_bind hΦi _ ?_
  have hcb := (hf Θ'' (hE.extR ρf) hOK'' c'' hcf ls') α hLt
  have hfr' := rwp_frame (fun _ τ => τ = ρm) (fun _ _ _ _ h => h) hcomp (rwp_of_erwp_empty (erwp_of_cN_ret hcb)) rfl
  refine rwp_mono_le (fun j hj ls₂ g τ hg => ?_) (rwp_consistentXV hfr' hc'')
  obtain ⟨⟨τg, τm, hcτ, hgv, rfl⟩, hcτ', hvτ⟩ := hg
  have happ := hgv Θ'' (LocTy.extR_refl _ _) hOK'' c'' (consistentX_left hcτ hcτ' hvτ) ls₂
    c'' j le_rfl (Val.arr l cn) _ τ hcτ (vN_le hj hfam) hcτ'
  show rwp (ℍ := ℍ) _ _ j ls₂ ((Kont.pairR (Val.arr l cn) Kont.hole).plug
    (.app (.val g) (.val (Val.arr l cn)))) τ
  refine rwp_bind hΦi _ ?_
  refine rwp_mono_le (fun j' hj' ls₃ w ρw hw => ?_) (rwp_of_erwp_empty (erwp_of_cN_ret happ))
  refine rwp_val (v := Val.pair (Val.arr l cn) w) ?_
  obtain ⟨β, hβ, hwB, -⟩ := hw
  exact ⟨w, rfl, by rw [← hBδ α]; exact hwB⟩

/-- **`slice_borrow_mut` at `SemJN`** (Core's `sliceBorrowM_compatX`). -/
theorem sliceBorrowM_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {A B : VTy} (x : LifeVar)
    (hΓ : Ctx.DeadP Γ) (hsideA : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A)
    (hsideB : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b B) (hfree₁ : ¬ VFree x A)
    (hfree₂ : ¬ VFree x B) :
    SemJN (ℍ := ℍ) Δ Γ withbor (.val (sliceBorrowMTy x Δ.meetOfDom A B)) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  obtain rfl := gN_deadP hΓ hg
  refine cN_ret_of ?_
  show erwp (ℍ := ℍ) (Θ.view c) (opTableN OpTabN.empty) _ n ls (substAll γ withbor) _
  rw [show substAll γ withbor = withbor from psub_closedAt _ γ (by decide) (Nat.zero_le 0)]
  exact erwp_val (v := withborVal) (sliceBorrowM_sem hδ hsideA hsideB hfree₁ hfree₂ Θ n)

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel (LtLife substAll)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Kont Head eLoad eStore)

/-- **`slice_replace_mut` at `SemJN`** (Core's `sliceReplaceM_compatX`): in range, the picked
leaf's cell is opened by the Mut Anti-Frame at the view (`erwp_M_antiFrame`), read (`rwp_load`)
and written (`rwp_store`), and sealed again holding the new element, the leaf back in the family
beside the old element; out of range, the element is handed back. -/
theorem sliceReplaceM_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {A : VTy}
    (hΓ : Ctx.DeadP Γ) : SemJN (ℍ := ℍ) Δ Γ (.val replaceV) (.val (sliceReplaceMTy a A)) := by
  refine sem_constN hΓ rfl fun δ Θ n _ _ => ⟨rfl, ?_⟩
  intro Θ' _ hΘ' _ _ ls' c'' k _ v σ τ hcomp hv hcon
  rw [eq_of_compS_empty_left hcomp] at hcon ⊢
  obtain ⟨v₁, v₂, σ₁, σ₂, rfl, hc, ⟨ℓ, cn, rfl, hn, hs⟩, w₁, x, ρ₀, σx, rfl, hc₂,
    ⟨⟨i, rfl⟩, rfl⟩, hx⟩ := hv
  rw [eq_of_compS_empty_left hc₂] at hc
  have hΦ := LocTy.view_down hΘ'.1 c''
  have hQd : PostN.Down (fun k _ v ρ => vN (ℍ := ℍ)
      (.tensor (.sliceMut a A) (.sum A A)) δ Θ' k v ρ) :=
    fun k _ v ρ h => vN_down _ δ Θ' k v ρ h
  have hTd := opTableN_down OpTabN.empty_down
  refine cN_ret_of ?_
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
    set P : CPredL := fun Θ₀ j u r => vN (ℍ := ℍ) A δ Θ₀ j u r with hP
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
    have hwA : vN (ℍ := ℍ) A δ Θ' j₀ w₀ σ₀ := (vN_above A δ Θ' hσ₀).mp hw₀
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
    have hwx : famL b P Θ' m x ⟨σx, hσx⟩ := (vN_above A δ Θ' hσx).mpr (vN_le (by omega) hx)
    -- `rest = F ● σ₀`, `F = ρr ● σx`: `rest = σx ● R`, `R = ρr ● σ₀`
    obtain ⟨R, hR, hrestR⟩ := compS_reassoc (ResU.CompS.comm hF) hrest
    refine ⟨x, σx, hσx, hwx, R, rest, ResU.CompS.comm hp₃, hrestR, fun X' hX' => ?_⟩
    -- `X' = R ● leaf = (ρr ● leaf) ● σ₀`
    obtain ⟨L, hL, hX'L⟩ := compS_exch hR hX'
    have hleaf : vN (ℍ := ℍ) (.mut a A) δ Θ' m (Val.loc (ℓ + i.toNat))
        (ResU.single (ℓ + i.toNat) (CellU.mutOf b x σx hσx (famL b P Θ' m) hwx)) :=
      ⟨α₀, hα₀, b, hα₀b, ⟨ℓ + i.toNat, x, σx, hσx, m, hwx, le_rfl, rfl, hlΘ, rfl⟩, hunif⟩
    have hfam : vN (ℍ := ℍ) (.sliceMut a A) δ Θ' m (Val.arr ℓ cn) L :=
      vN_fam_mk hn (hback _ (fun _ _ h => vN_le (by omega) h) _ L (ResU.CompS.comm hL) hleaf)
    exact ⟨_, _, L, σ₀, rfl, hX'L, hfam,
      .inl ⟨w₀, rfl, vN_le (by omega) hwA⟩⟩
  · rw [he]
    refine erwp_det hΦ hTd hQd
      (fun μ => step1Only_plug (Head.case₂ μ Val.unit _ _) rfl .hole) ?_
    simp only [Kont.plug]
    rw [replace_out]
    exact erwp_val (v := Val.pair (Val.arr ℓ cn) (Val.inj₂ x))
      ⟨_, _, σ₁, σx, rfl, hc, vN_fam_mk hn hs, .inr ⟨x, rfl, hx⟩⟩

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel (LtLife substAll)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Kont Head eLoad eStore)

theorem sliceSwapM_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {A : VTy}
    (hΓ : Ctx.DeadP Γ) : SemJN (ℍ := ℍ) Δ Γ (.val BoCa.Fig16.LogRel.Core.swapV) (.val (sliceSwapMTy a A)) := by
  refine sem_constN hΓ rfl fun δ Θ n _ _ => ⟨rfl, ?_⟩
  intro Θ' _ hΘ' _ _ ls' c'' k _ v σ τ hcomp hv hcon
  rw [eq_of_compS_empty_left hcomp] at hcon ⊢
  obtain ⟨v₁, v₂, σ₁, σ₂, rfl, hc, ⟨ℓ, cn, rfl, hn, hs⟩, w₁, w₂, ρ₀, ρ₀', rfl, hc₂,
    ⟨⟨i, rfl⟩, rfl⟩, ⟨⟨j, rfl⟩, rfl⟩⟩ := hv
  rw [eq_of_compS_empty_left hc₂] at hc
  obtain rfl := ResU.CompS.functional hc (ResU.comp_empty_right σ₁)
  have hΦ := LocTy.view_down hΘ'.1 c''
  have hQd : PostN.Down (fun k _ v ρ => vN (ℍ := ℍ) (.sliceMut a A) δ Θ' k v ρ) :=
    fun k _ v ρ h => vN_down _ δ Θ' k v ρ h
  have hTd := opTableN_down OpTabN.empty_down
  refine cN_ret_of ?_
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
    exact erwp_val (v := Val.arr ℓ cn) (vN_fam_mk hn hs)
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
    exact erwp_val (v := Val.arr ℓ cn) (vN_fam_mk hn hs)
  rw [he']
  refine erwp_det hΦ hTd hQd
    (fun μ => step1Only_plug (Head.case₁ μ (Val.loc (ℓ + j.toNat)) _ _) rfl .hole) ?_
  show erwp _ _ _ _ _ (slSwapCells ℓ cn (ℓ + i.toNat) (ℓ + j.toNat)) _
  refine erwp_of_valid fun hv => ?_
  set P : CPredL := fun Θ₀ j u r => vN (ℍ := ℍ) A δ Θ₀ j u r with hP
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
    have hwA : vN (ℍ := ℍ) A δ Θ' j₀ w₀ σ₀ := (vN_above A δ Θ' hσ₀).mp hw₀
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
    have hwx : famL b P Θ' m w₀ ⟨σ₀, hσ₀⟩ := (vN_above A δ Θ' hσ₀).mpr (vN_le (by omega) hwA)
    refine ⟨w₀, σ₀, hσ₀, hwx, ρr, rest, ResU.CompS.comm hp₄, ResU.CompS.comm hrest,
      fun X' hX' => ?_⟩
    have hleaf : vN (ℍ := ℍ) (.mut a A) δ Θ' m (Val.loc (ℓ + i.toNat))
        (ResU.single (ℓ + i.toNat) (CellU.mutOf b w₀ σ₀ hσ₀ (famL b P Θ' m) hwx)) :=
      ⟨α₀, hα₀, b, hα₀b, ⟨ℓ + i.toNat, w₀, σ₀, hσ₀, m, hwx, le_rfl, rfl, hlΘ, rfl⟩, hunif⟩
    exact vN_fam_mk hn (hback _ (fun _ _ h => vN_le (by omega) h) _ X' (ResU.CompS.comm hX') hleaf)
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
    have hwAi : vN (ℍ := ℍ) A δ Θ' ji wi σi := (vN_above A δ Θ' hσi).mp hwi
    have hwAj : vN (ℍ := ℍ) A δ Θ' jj wj σj := (vN_above A δ Θ' hσj).mp hwj
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
      (vN_above A δ Θ' hσij).mpr (vN_le (by omega) hwAi)
    have hwj' : famL bi P Θ' m wj ⟨σj, hσji⟩ :=
      (vN_above A δ Θ' hσji).mpr (vN_le (by omega) hwAj)
    -- the cell at `j` sealed at `wi`: `N' = σi ● R`, `R = own_i(wj) ● S`, `S = ρr ● σj`
    obtain ⟨S, hS, hLS⟩ := compS_reassoc (ResU.CompS.comm hH) hL
    obtain ⟨R, hR, hN'R⟩ := compS_lcomm hLS hN'
    refine ⟨wi, σi, hσij, hwi', R, N', ResU.CompS.comm hp₄, hN'R, fun Y hY => ?_⟩
    -- the cell at `i` sealed at `wj`: `Y = own_i(wj) ● T`, `T = σj ● R'`, `R' = ρr ● cell_j`
    obtain ⟨T, hT, hYT⟩ := compS_reassoc hR hY
    obtain ⟨R', hR', hTR'⟩ := compS_reassoc (ResU.CompS.comm hS) hT
    refine ⟨wj, σj, hσji, hwj', R', T, hYT, hTR', fun Z hZ => ?_⟩
    have hleafi : vN (ℍ := ℍ) (.mut a A) δ Θ' m (Val.loc (ℓ + i.toNat))
        (ResU.single (ℓ + i.toNat) (CellU.mutOf bi wj σj hσji (famL bi P Θ' m) hwj')) :=
      ⟨αi, hαi, bi, hαbi, ⟨ℓ + i.toNat, wj, σj, hσji, m, hwj', le_rfl, rfl, hliΘ, rfl⟩, hunifi⟩
    have hleafj : vN (ℍ := ℍ) (.mut a A) δ Θ' m (Val.loc (ℓ + j.toNat))
        (ResU.single (ℓ + j.toNat) (CellU.mutOf bj wi σi hσij (famL bj P Θ' m) hwi')) :=
      ⟨αj, hαj, bj, hαbj, ⟨ℓ + j.toNat, wi, σi, hσij, m, hwi', le_rfl, rfl, hljΘ, rfl⟩, hunifj⟩
    exact vN_fam_mk hn (hback _ (fun _ _ h => vN_le (by omega) h) _ _ R' Z
      (ResU.CompS.comm hR') (ResU.CompS.comm hZ) hleafi hleafj)

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Head Kont hndE ubindE ccatchE cfinE)

namespace Goal791N
open BoCa.Fig16.LogRel (LtLife substAll)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- **The fill** (Core's `tabFill_wp`): with the cells `ℓ, …, ℓ + i − 1` filled and
`ℓ + i, …, ℓ + i + k − 1` holding `()`, the rest of `tabFill` runs to the array, at every index
below the `!`-function's; by induction on `k`. -/
theorem tabFill_wpN {A : VTy} {δ : LSub} {Θ : LocTy} (hΘ : Θ.OK) {M : Nat} (f : Val) (l : Loc)
    (N : UInt32) (hN31 : N.toNat < 2 ^ 31)
    (hf : vN (ℍ := ℍ) (.bang (.lolli (.int .w32) A)) δ Θ M f PMap.empty) :
    ∀ (k i m : Nat) (ls : List SRec) (ρd ρt ρ : WRes) (c : Loc → Option Life), m ≤ M →
      ConsistentX c ρ → i + k = N.toNat →
      sepRange (fun x => vN (ℍ := ℍ) (.ref A) δ Θ m (Val.loc x)) l i ρd →
      sepRange (fun m => ptoOwn m .unit) (l + i) k ρt → ResU.CompS ρd ρt ρ →
      erwp (ℍ := ℍ) (Θ.view c) (opTableN OpTabN.empty)
        (fun k _ v ρ => vN (ℍ := ℍ) (.array A) δ Θ k v ρ) m ls (tabFill f l N i k) ρ
  | 0, i, m, ls, ρd, ρt, ρ, c, _, _, hN, hd, ht, hc => by
      obtain ⟨rfl, -⟩ := ht
      rw [ResU.CompS.functional hc (ResU.comp_empty_right ρd)]
      refine erwp_val (v := Val.arr l N) (vN_fam_mk hN31 ?_)
      rw [← hN]; exact hd
  | k + 1, i, m, ls, ρd, ρt, ρ, c, hm, hcon, hN, hd, ⟨cl, ρt', hct, hcl, ht'⟩, hc => by
      have hΦ := LocTy.view_down hΘ.1 c
      show erwp (ℍ := ℍ) _ _ _ m ls
        ((Kont.seq (.appR (.app (.val (.prim .store)) (.val (.loc (l + i)))) .hole)
          (tabFill f l N (i + 1) k)).plug (.app (.val f) (.val (Val.i32 (UInt32.ofNat i))))) ρ
      -- `ρ = cell ● (ρd ● ρt')`
      obtain ⟨R, hR, hρ⟩ := compS_lcomm hct hc
      refine erwp_bind_frame hΦ (opTableN_local _) _
        (fun σ => ∃ σc σr, ResU.CompS σc σr σ ∧ ptoOwn (l + i) .unit σc ∧ ∃ σd σt,
          ResU.CompS σd σt σr ∧
          sepRange (fun x => vN (ℍ := ℍ) (.ref A) δ Θ m (Val.loc x)) l i σd ∧
          sepRange (fun m => ptoOwn m .unit) (l + i + 1) k σt)
        (compS_empty_left ρ) hcon
        (bang_app hΘ hm hf (consistentX_empty c) (k := m) ⟨⟨_, rfl⟩, rfl⟩ ls)
        ⟨cl, R, hρ, hcl, ρd, ρt', hR, hd, ht'⟩ ?_
      intro k' hk' ls' w σw σr σ hσ hw ⟨c', R', hR', hc', σd, σt, hdt, hd', ht''⟩ hcσ hvσ
      obtain rfl := hc'
      simp only [Kont.plug]
      -- `σ = cell ● (σw ● R')`
      obtain ⟨G, hG, hσG⟩ := compS_lcomm hR' hσ
      refine erwp_bindR hΦ (opTableN_local _) (.seq .hole (tabFill f l N (i + 1) k)) ?_
      refine rwp_store ls' (l + i) .unit w _ ⟨_, G, hσG, rfl, fun c₃ σ₃ hc₃ hcomp₃ => ?_⟩
      obtain rfl := hc₃
      simp only [Kont.plug]
      refine erwp_det hΦ (opTableN_down OpTabN.empty_down)
        (fun k _ v ρ h => vN_down _ δ Θ k v ρ h)
        (fun μ => step1Only_plug (Head.seq μ _) rfl .hole) ?_
      -- the new leaf `σw ● cell`, beside the filled cells and the rest of the placeholders
      obtain ⟨L, hL, hσ₃⟩ := compS_exch hG hcomp₃
      obtain ⟨Md, hMd, hσ₃'⟩ := compS_lcomm hdt hσ₃
      obtain ⟨D, hD, hσ₃''⟩ := compS_reassoc' hMd hσ₃'
      have hvG : ResU.Valid G := (ResU.Valid.split hσG hvσ).2
      have hcG : ConsistentX c G := consistentX_right hσG hcσ hvσ
      have hvR' : ResU.Valid R' := (ResU.Valid.split hG hvG).2
      have hcR' : ConsistentX c R' := consistentX_right hG hcG hvG
      have hcw : ConsistentX c σw := consistentX_left hG hcG hvG
      have hcL : ConsistentX c L :=
        consistentX_compS (ResU.CompS.comm hL) (consistentX_single_own c (l + i) w) hcw
      have hc₃ : ConsistentX c σ₃ := consistentX_compS hσ₃ hcL hcR'
      have hleaf : vN (ℍ := ℍ) (.ref A) δ Θ (k' - 1) (Val.loc (l + i)) L :=
        ⟨l + i, w, σw, rfl, ResU.CompS.comm hL, vN_le (by omega) hw⟩
      refine tabFill_wpN hΘ f l N hN31 hf k (i + 1) (k' - 1) ls' D σt σ₃ c (by omega) hc₃
        (by rw [← hN]; ring) (sepRange_append hD
          (sepRange_mono' (fun _ _ h => vN_le (by omega) h) hd')
          ⟨L, PMap.empty, ResU.comp_empty_right L, hleaf, ⟨rfl, trivial⟩⟩) ?_ hσ₃''
      rwa [show l + i + 1 = l + (i + 1) by ring] at ht''

/-- **`array_new` at `SemJN`** (Core's `arrNew_compatX`): the `tab` step (`erwp_tab`), then the
fill from no filled cell (`tabFill_wpN`). -/
theorem arrNew_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {A : VTy} (hΓ : Ctx.DeadP Γ) :
    SemJN (ℍ := ℍ) Δ Γ (.val (.prim .tab)) (.val (arrNewTy A)) := by
  refine sem_constN hΓ rfl fun δ Θ n _ _ => ⟨rfl, ?_⟩
  intro Θ' _ hΘ' _ _ ls' c'' k _ v σ τ hcomp hv hcon
  rw [eq_of_compS_empty_left hcomp] at hcon ⊢
  obtain ⟨v₁, f, σ₁, σ₂, rfl, hc, ⟨⟨cn, rfl⟩, rfl⟩, hf⟩ := hv
  obtain rfl : σ₂ = PMap.empty := hf.1
  cases eq_empty_of_compS_empty hc
  have hΦ := LocTy.view_down hΘ'.1 c''
  rcases k with _ | k
  · exact cN_ret_of erwp_zero
  refine cN_ret_of ?_
  refine erwp_tab hΦ (opTableN_local _) fun ℓ cells x hcells hx => ?_
  rw [eq_of_compS_empty_left hx]
  exact tabFill_wpN hΘ' f ℓ (arrLen cn) (arrLen_bound cn) hf (arrLen cn).toNat 0 k ls'
    PMap.empty cells cells c'' (Nat.le_succ k)
    (consistentX_sepRange_own c'' .unit _ ℓ hcells) (by simp) ⟨rfl, trivial⟩
    (by simpa using hcells) (compS_empty_left cells)

end Goal791N

end BoCa.Fig16.LogRel.Core.Chain.SI


end
