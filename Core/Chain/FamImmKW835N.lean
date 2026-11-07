import Core.Chain.FoldImmKW835N

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

/-!
# `slice_borrow` at the pure row, at the typed world  `[spec §42, §62]`

`slice_borrow` at the pure row at `SemJN` (`sliceBorrowI_compatN`): the callback stops nowhere, so
the chain's Imm Frame over the family (`erwp_I_frameListRN`) applies at `F A`'s empty table.
-/

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Kont performE raiseE opPayload)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

end BoCa.Fig16.LogRel.Core.Chain.SI

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel (LtLife substAll)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Kont Head ubindE)

/-- **An `imm` leaf at `α`** at the world `Θ`: `Imm`'s clause read at `α` (Core's `immLeaf`), one
`imm` cell longer-lived than `α` with its payload in the observable view, witnessed in the world's
records. -/
def immLeafN (A : VTy) (δ : LSub) (α : Life) (Θ : LocTy) (n : Nat) (m : Loc) : WProp := fun ρ =>
  immCell α (fun u σ => vO (ℍ := ℍ) A δ Θ n u σ) (Val.loc m) ρ ∧
    ∀ l s u σ h, ρ = ResU.single l (CellU.immOf s u σ h) → ImmWitW Θ.imm l s A δ

/-- An `imm` leaf at `α` is a value of `Imm 'x A` at `δ['x ↦ α]` (Core's `immLeaf_to_vP`). -/
theorem vN_immLeaf {x : LifeVar} {A : VTy} (hx : ¬ VFree x A) {δ : LSub} {α : Life} {Θ : LocTy}
    {n : Nat} {m : Loc} {ρ : WRes} (h : immLeafN (ℍ := ℍ) A δ α Θ n m ρ) :
    vN (ℍ := ℍ) (.imm (.var x) A) (δ.extend x α) Θ n (Val.loc m) ρ := by
  have hag : ∀ y, VFree y A → δ.find? y = (δ.extend x α).find? y := fun y hy =>
    (BoCa.Fig16.LogRel.find?_extend_ne δ α (fun e => by subst e; exact hx hy)).symm
  refine ⟨α, interp_ext_self δ x α, ?_, fun l s u σ hs e => ?_⟩
  · rw [vO_extend_of_not_free hx]; exact h.1
  · exact (immWitW_congr hag Θ.imm l s) ▸ h.2 l s u σ hs e

/-- **One Imm Frame per place, around one expression, across raises** (Core's
`wpG_I_frameList`, the frames of `sliceBorrowI_compatX` and `sliceBorrowIU_compatX`): the list
induction over `erwp_I_frameRR`, at an abortive table `Tb`.

Frame `j` lends its leaf `imm` at `αⱼ`, below the frame's rest, the payloads' stratum `β`, the
result's `β′` and the bound `γ` (Core's `aF ⊓ β′ ⊓ β`), its record `(pⱼ, αⱼ)` in the world of the
frames inside it; their run is read at the lender's view (`erwp_tieEntryR`). The inner frames'
bound is `@R ⊓ αⱼ ⊓ γ` as printed. The callback runs at the world holding every record, each lent
below the bound and on the callback's list, and receives every leaf at the innermost lifetime.
`Ψ` is the callback's postcondition: in the stratum `β′`, read at the world without a record at
a resource in the record's stratum, and not reading the list. The claim a `raise` carries is the
cells owned again (`claimL`, at the frames' index). -/
theorem erwp_I_frameListRN {A : VTy} {δ : LSub} {β β' : Life} (hadm : AdmWf A δ)
    (hunif : ∀ Θ j u r, vN (ℍ := ℍ) A δ Θ j u r → r.InStratum β)
    (Tb : OpTabN) (hab : ∀ m i en, Tb m i = some en → en.abort = true)
    (hTok : ∀ α, Tb.ILendOKR α)
    (Ψ : LocTy → PostN) (hΨs : ∀ Θ k ls v ρ, Ψ Θ k ls v ρ → ρ.InStratum β')
    (hΨl : ∀ (Θ : LocTy) (r : FrameRec) (α : Life) k ls v ρ,
      ρ.InStratum α → Ψ (Θ.addImm (r, α)) k ls v ρ → Ψ Θ k ls v ρ)
    (hΨls : ∀ Θ k ls₁ ls₂ v ρ, Ψ Θ k ls₁ v ρ → Ψ Θ k ls₂ v ρ) (e : Expr) (c : Loc → Option Life) :
    ∀ (I : List Loc) (Θ : LocTy) (n : Nat) (ls : List SRec) (ρo ρH ρ : WRes) (γ : Life),
      ConsistentX c ρH → ResU.CompS ρo ρH ρ →
      sepList (fun m => vN (ℍ := ℍ) (.ref A) δ Θ n (Val.loc m)) I ρo →
      (∀ α, α < γ → ρH.InStratum α ∧ ∀ (xs ls' : List SRec), (∀ x ∈ xs, x.2 < γ ∧ x ∈ ls') →
        (∀ y ∈ ls, y ∈ ls') → ∀ ρm ρ',
          sepList (immLeafN (ℍ := ℍ) A δ α (Θ.addImms xs) n) I ρm → ResU.CompS ρH ρm ρ' →
          ConsistentX c ρ' →
          erwp (ℍ := ℍ) ((Θ.addImms xs).view c) (opTableR Tb (fun _ => claimL (ℍ := ℍ) A δ Θ [] n))
            (Ψ (Θ.addImms xs)) n ls' e ρ') →
      erwp (ℍ := ℍ) (Θ.view c) (opTableR Tb (fun _ => claimL (ℍ := ℍ) A δ Θ I n))
        (fun k ls' v ρ' => ∃ ρ₁ ρ₂, ResU.CompS ρ₁ ρ₂ ρ' ∧
          sepList (fun m => vN (ℍ := ℍ) (.ref A) δ Θ k (Val.loc m)) I ρ₁ ∧ Ψ Θ k ls' v ρ₂)
        n ls e ρ
  | [], Θ, n, ls, ρo, ρH, ρ, γ, hcH, hcρ, ho, hH => by
      obtain ⟨rfl, -⟩ := ho
      rw [eq_of_compS_empty_left hcρ]
      have h := (hH (↓γ) (Life.down_sqsubset γ)).2 [] ls (fun _ h => absurd h List.not_mem_nil)
        (fun _ h => h) PMap.empty ρH ⟨rfl, trivial⟩ (ResU.comp_empty_right ρH) hcH
      exact erwp_mono (fun k ls' v σ h' =>
        ⟨PMap.empty, σ, compS_empty_left σ, ⟨rfl, trivial⟩, h'⟩) (opTableR_local _ _) n ls e ρH h
  | ℓ :: I, Θ, n, ls, ρo, ρH, ρ, γ, hcH, hcρ, ho, hH => by
      obtain ⟨ρ0, ρr, hc0, hleaf, hrest⟩ := ho
      obtain ⟨l, u, σ, hl, hcl, hu⟩ := hleaf
      obtain rfl : ℓ = l := loc_inj hl
      -- `ρ = ρ0 ● Fr`, `Fr = ρr ● ρH`
      obtain ⟨Fr, hFr, hρ⟩ := compS_reassoc hc0 hcρ
      refine erwp_of_valid fun hv => ?_
      have hvρ0 : ResU.Valid ρ0 := (ResU.Valid.split hρ hv).1
      have hvσ : ResU.Valid σ := (ResU.Valid.split hcl hvρ0).2
      -- the outer frame's lifetime: below the frame's rest, `β`, `β′` and the bound
      obtain ⟨βF, hβF⟩ := ResU.exists_stratum Fr
      set α₁ : Life := ↓(βF ⊓ β ⊓ β' ⊓ γ) with hα₁def
      have hα₁lt : α₁ < βF ⊓ β ⊓ β' ⊓ γ := Life.down_sqsubset _
      have hα₁F : α₁ ≤ βF := hα₁lt.le.trans (inf_le_left.trans (inf_le_left.trans inf_le_left))
      have hα₁β : α₁ ≤ β := hα₁lt.le.trans (inf_le_left.trans (inf_le_left.trans inf_le_right))
      have hα₁β' : α₁ ≤ β' := hα₁lt.le.trans (inf_le_left.trans inf_le_right)
      have hα₁γ : α₁ < γ := lt_of_lt_of_le hα₁lt inf_le_right
      have houtP : σ.InStratum α₁ := (hunif Θ n u σ hu).mono hα₁β
      have houtb : Fr.InStratum α₁ := hβF.mono hα₁F
      -- the record and its lineage
      set p : FrameRec := ⟨ℓ, u, σ, A, δ⟩ with hpdef
      obtain ⟨-, eR, -, heR, -, -⟩ := hvσ
      obtain ⟨ds, hds⟩ := lineage_list (r := p) (vN_vShape A δ Θ n u σ hu) hadm heR
      set Θ₁ := Θ.addImm (p, α₁) with hΘ₁
      set ls₁ := frameList p ds α₁ ls with hls₁
      set ρi : WRes := ResU.single ℓ (CellU.immOf (LSet.singleton α₁) u σ houtP) with hρi
      have hci : ConsistentX c ρi := consistentX_allImm (fun m ψ e => by
        obtain ⟨-, rfl⟩ := ResU.single_get_eq_some e
        exact CellU.kind_immOf _ _ _ _) c
      have hRs : ∀ k ρ', (fun _ : Nat => claimL (ℍ := ℍ) A δ Θ₁ I n) k ρ' → ρ'.InStratum α₁ :=
        fun k ρ' h =>
          sepList_closed (ResU.inStratum_empty α₁) (fun _ _ _ hc a b => inStratum_compS hc a b)
            (fun m τ hm => ownLeafN_inStratum hα₁β hunif hm) h
      -- the cells of `I` at the world without the record
      have hdrop : ∀ k ρ', ρ'.InStratum α₁ →
          sepList (fun m => vN (ℍ := ℍ) (.ref A) δ Θ₁ k (Val.loc m)) I ρ' →
          sepList (fun m => vN (ℍ := ℍ) (.ref A) δ Θ k (Val.loc m)) I ρ' := fun k ρ' hs h =>
        sepList_mono_down (R := fun τ => τ.InStratum α₁)
          (fun _ _ _ hc h => ⟨ResU.CompS.inStratum_left hc h,
            ResU.CompS.inStratum_left (ResU.CompS.comm hc) h⟩)
          (fun m τ hτ hm => vN_extR (.ref A) δ k _ τ (LocTy.extR_of_addImm Θ p hτ) hm) hs h
      have hcl' : ∀ k ρ', (claimI ℓ u σ k ⋆ (fun _ : Nat => claimL (ℍ := ℍ) A δ Θ₁ I n) k) ρ' →
          claimL (ℍ := ℍ) A δ Θ (ℓ :: I) n ρ' := by
        rintro k ρ' ⟨ρ₁, ρ₂, hc12, hcw, hr⟩
        exact ⟨ρ₁, ρ₂, hc12, ⟨ℓ, u, σ, rfl, hcw, hu⟩, hdrop n ρ₂ (hRs k ρ₂ hr) hr⟩
      set Q : PostN := fun k ls' v ρ' => ∃ ρ₁ ρ₂, ResU.CompS ρ₁ ρ₂ ρ' ∧
        sepList (fun m => vN (ℍ := ℍ) (.ref A) δ Θ k (Val.loc m)) (ℓ :: I) ρ₁ ∧
          Ψ Θ k ls' v ρ₂ with hQ
      have hIF := erwp_I_frameRR (Φ := Θ.view c) ℓ A δ hadm u
        (fun _ v ρ => vN (ℍ := ℍ) A δ Θ n v ρ) (fun _ ρ h => vN_vShape A δ Θ n u ρ h)
        (fun _ _ _ _ h => h) (hTok α₁) hRs (Q := Q)
        (fun k _ _ w ρ _ ⟨ρ₁, ρ₂, hc12, ho1, hψ⟩ => ⟨ρ₁, ρ₂, hc12, ho1, hΨls _ _ _ _ _ _ hψ⟩)
        n ls e σ ρ0 Fr ρ houtP houtb hu hcl hρ ds hds (fun BI hBI => ?_)
      · exact erwp_opTableR_le (OpTabN.Sub.le fun _ _ _ h => h) hcl' n ls e ρ hIF
      -- `BI = ρr ● R`, `R = ρH ● ρi`
      obtain ⟨R, hR, hBIR⟩ := compS_reassoc hFr hBI
      have hcR : ConsistentX c R := consistentX_compS hR hcH hci
      obtain ⟨βR, hβR⟩ := ResU.exists_stratum R
      have hrest₁ : sepList (fun m => vN (ℍ := ℍ) (.ref A) δ Θ₁ n (Val.loc m)) I ρr :=
        sepList_mono_down (R := fun τ => τ.InStratum α₁)
          (fun _ _ _ hc h => ⟨ResU.CompS.inStratum_left hc h,
            ResU.CompS.inStratum_left (ResU.CompS.comm hc) h⟩)
          (fun m τ hτ hm => vN_extR (.ref A) δ n _ τ (LocTy.extR_addImm Θ p hτ) hm)
          (ResU.CompS.inStratum_left hFr houtb) hrest
      -- the inner frames' run, read at the lender's view
      refine erwp_tieEntryR (Φ := Θ.view c) (Φ' := Θ₁.view c) rfl hab (fun y hy => by
        rcases List.mem_cons.mp hy with rfl | hy
        · exact .inr (List.mem_cons_self ..)
        · exact .inl hy) ?_
      refine erwp_mono_le n (fun k hk ls' v ρ' h => ?_)
        (fun j _ ls' t Ψ' Ψ'' ρ hΨ h => opTableR_local _ _ j ls' t Ψ' Ψ'' ρ hΨ h) n le_rfl _ _ BI
        (erwp_I_frameListRN hadm hunif Tb hab hTok Ψ hΨs hΨl hΨls e c I Θ₁ n ls₁ ρr R BI
          (βR ⊓ α₁ ⊓ γ) hcR hBIR hrest₁ (fun α₂ hα₂ => ⟨hβR.mono (le_of_lt (lt_of_lt_of_le hα₂
            (inf_le_left.trans inf_le_left))), ?_⟩))
      · -- the outer frame's postcondition from the inner ones'
        obtain ⟨ρ₁, ρ₂, hc12, ho1, hψ⟩ := h
        have hs1 : ρ₁.InStratum α₁ := sepList_closed (ResU.inStratum_empty α₁)
          (fun _ _ _ hc a b => inStratum_compS hc a b)
          (fun m τ hm => ownLeafN_inStratum hα₁β hunif hm) ho1
        have hs2 : ρ₂.InStratum α₁ := (hΨs _ _ _ _ _ hψ).mono hα₁β'
        refine ⟨fun Y X hY hX σ' Z hσ' hZ => ?_, inStratum_compS hc12 hs1 hs2⟩
        subst hY
        obtain ⟨Wc, hWc, hZ'⟩ :=
          (ResU.CompS.assoc ρ' (ResU.single ℓ (CellU.ownOf u)) σ' Z).mpr ⟨X, hX, hZ⟩
        obtain ⟨oc, hoc, hZ''⟩ := compS_exch hc12 hZ'
        exact ⟨oc, ρ₂, hZ'', ⟨Wc, ρ₁, ResU.CompS.comm hoc, ⟨ℓ, u, σ', rfl, hWc, vN_le hk hσ'⟩,
          hdrop k ρ₁ hs1 ho1⟩, hΨl Θ p α₁ k ls' v ρ₂ hs2 hψ⟩
      · -- the inner frames' callback: the outer leaf, at `α₂ ⊑ α₁`, heads the family
        intro xs ls' hxs hls' ρm₂ ρ' hm₂ hcomp hc'
        have hα₂γ : α₂ < γ := lt_of_lt_of_le hα₂ inf_le_right
        have hα₂α₁ : α₂ < α₁ := lt_of_lt_of_le hα₂ (inf_le_left.trans inf_le_right)
        have hγ₁α₁ : βR ⊓ α₁ ⊓ γ ≤ α₁ := inf_le_left.trans inf_le_right
        have hγ₁γ : βR ⊓ α₁ ⊓ γ ≤ γ := inf_le_right
        obtain ⟨X, hX, hρ'X⟩ := compS_reassoc hR hcomp
        rw [LocTy.addImm_addImms] at hm₂ ⊢
        have hlead : immLeafN (ℍ := ℍ) A δ α₂ (Θ.addImms (xs ++ [(p, α₁)])) n ℓ ρi := by
          refine ⟨⟨ℓ, LSet.singleton α₁, u, σ, houtP, rfl, rfl, hα₂α₁.le, ?_⟩,
            fun l₀ s₀ u₀ σ₀ h₀ e => ?_⟩
          · refine vO_extR A δ n u σ (LocTy.extR_addImms Θ _ fun x hx => ?_)
              (vN_vO A δ Θ n u σ hu)
            rcases List.mem_append.mp hx with hx | hx
            · exact houtP.mono ((hxs x hx).1.le.trans hγ₁α₁)
            · rw [List.mem_singleton.mp hx]; exact houtP
          · obtain ⟨rfl, e'⟩ := single_immOf_inj e
            obtain ⟨rfl, -⟩ := CellU.immOf_inj e'
            exact ⟨(p, α₁), List.mem_append_left _ (List.mem_append_right _
              (List.mem_singleton_self _)), le_refl _, p, DescR.refl _, A, δ, TyEq.refl _ _,
              Or.inl ⟨p, List.mem_singleton_self _, rfl, rfl, fun _ _ => rfl⟩⟩
        refine (hH α₂ hα₂γ).2 (xs ++ [(p, α₁)]) ls' (fun x hx => ?_)
          (fun y hy => hls' y ((addAt_frameList p ds α₁ ls).1 y hy)) X ρ'
          ⟨_, ρm₂, hX, hlead, hm₂⟩ hρ'X hc'
        rcases List.mem_append.mp hx with hx | hx
        · exact ⟨lt_of_lt_of_le (hxs x hx).1 hγ₁γ, (hxs x hx).2⟩
        · rw [List.mem_singleton.mp hx]
          exact ⟨hα₁γ, hls' _ (List.mem_cons_self ..)⟩

/-! ### `slice_borrow` at the pure row -/

/-- **`slice_borrow` is a value of its type** (Core's `sliceBorrowI_compatX`):
`withbor` at `Array A ⊸ (∀'x ⊏ @Δ. [Imm 'x A] ⊸ ['x] B) ⊸ Array A ⊗ B`. `sliceBorrowM_sem`'s
steps with the `n` Imm Frames around the callback (`erwp_I_frameListRN` at the family's range,
the pure row's table): the payloads' and the result's strata from the side conditions by 6.60 at
`↓@bδ` (`vN_outlivesLe`), the frames' lifetimes below the bound and the callback's stratum; the
callback at the world holding the records (`LocTy.extR_addImms` at its resource), the family
`[Imm 'x A]` at the innermost lifetime (`vN_immLeaf`), `withbor1_sem`'s steps inside. -/
theorem sliceBorrowI_sem {Δ : LifeCtx} {x : LifeVar} {A B : VTy} {δ : LSub} (hδ : Δ.Models δ)
    (hadm : AdmWf A δ) (hsideA : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A)
    (hsideB : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b B) (hA : ¬ VFree x A) (hB : ¬ VFree x B)
    (Θ₀ : LocTy) (n : Nat) :
    vN (ℍ := ℍ) (sliceBorrowITy x Δ.meetOfDom A B) δ Θ₀ n withborVal PMap.empty := by
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
  have hcf : ConsistentX c' ρf := consistentX_right hc' hcon hv''
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
  have hBδ : ∀ α, vN (ℍ := ℍ) B (δ.extend x α) = vN (ℍ := ℍ) B δ :=
    fun α => vN_extend_of_not_free hB δ α
  -- the frames' postcondition: the handle beside a result of `B`
  let Ψ : LocTy → PostN := fun Θ k _ v ρ => ∃ w, v = Val.pair (Val.arr l cn) w ∧
    vN (ℍ := ℍ) B δ Θ k w ρ
  have hI := erwp_I_frameListRN hadm hunif OpTabN.empty
    (fun _ _ _ h => by simp [OpTabN.empty] at h) empty_iLendOKR Ψ
    (fun Θ k _ v ρ ⟨w, _, hw⟩ => hBs Θ k w ρ hw)
    (fun Θ r α k _ v ρ hρ ⟨w, hvw, hw⟩ =>
      ⟨w, hvw, vN_extR B δ k w ρ (LocTy.extR_of_addImm Θ r hρ) hw⟩)
    (fun _ _ _ _ _ _ h => h)
    ((Kont.pairR (Val.arr l cn) (Kont.appL Kont.hole (Val.arr l cn))).plug
      (.app (.val f) (.val Val.unit))) c' (rangeLocs l cn.toNat) Θ' k' ls' ρu ρf ρ'' (m ⊓ βf) hcf hc'
    (by rw [← sepRange_eq_sepList]; exact hs')
    (fun α hα => ⟨hβf.mono (le_of_lt (lt_of_lt_of_le hα inf_le_right)), ?_⟩)
  · refine erwp_mono (fun k ls₁ v ρ' h => ?_) (fun j ls₁ t Ψ₁ Ψ₂ ρ _ h => ?_) k' ls' _ ρ'' hI
    · -- the returned leaves are the array again, beside the callback's result
      obtain ⟨ρ₁, ρ₂, hc12, ho, w, rfl, hw⟩ := h
      exact ⟨Val.arr l cn, w, ρ₁, ρ₂, rfl, hc12,
        ⟨l, cn, rfl, hn', by rw [sepRange_eq_sepList]; exact ho⟩, hw⟩
    · -- the pure row stops nowhere
      rcases h with ⟨K, m, i, v, en, h⟩ | ⟨K, m, i, v, en, h⟩
      · obtain ⟨⟨-, -, hTe, -⟩, -⟩ := pure_sep_iff.mp h; simp [OpTabN.empty] at hTe
      · obtain ⟨⟨-, -, hTe, -⟩, -⟩ := pure_sep_iff.mp h; simp [OpTabN.empty] at hTe
  -- the callback, at the world holding the records, from the leaves at `α`
  intro xs ls₂ hxs _ ρm ρ₃ hml hcomp hc''
  set W := Θ'.addImms xs with hW
  have hOKW : W.OK := LocTy.addImms_ok hΘ' xs
  have hEW : Θ'.ExtR W ρf := LocTy.extR_addImms Θ' xs fun x hx =>
    hβf.mono (le_of_lt (lt_of_lt_of_le (hxs x hx).1 inf_le_right))
  refine erwp_of_valid fun hv₃ => erwp_of_rwp ?_
  have hLt : LtLife δ Δ.meetOfDom α := ⟨m, hm, lt_of_lt_of_le hα inf_le_left⟩
  have hΦi : (W.view c').Down := LocTy.view_down hOKW.1 c'
  have hcm : ConsistentX c' ρm := consistentX_right hcomp hc'' hv₃
  have hfam : vN (ℍ := ℍ) (.arrayImm (.var x) A) (δ.extend x α) W k' (Val.arr l cn) ρm :=
    ⟨l, cn, rfl, hn', by
      rw [sepRange_eq_sepList]; exact sepList_mono' (fun _ _ h => vN_immLeaf hA h) hml⟩
  refine rwp_bind hΦi _ ?_
  have hcb := (hf W hEW hOKW c' hcf ls₂) α hLt
  have hfr' := rwp_frame (fun _ τ => τ = ρm) (fun _ _ _ _ h => h) hcomp (rwp_of_erwp_empty (erwp_of_cN_ret hcb)) rfl
  refine rwp_mono_le (fun j hj ls₃ g τ hg => ?_) (rwp_consistentXV hfr' hc'')
  obtain ⟨⟨τg, τm, hcτ, hgv, rfl⟩, hcτ', hvτ⟩ := hg
  have happ := hgv W (LocTy.extR_refl _ _) hOKW c' (consistentX_left hcτ hcτ' hvτ) ls₃
    c' j le_rfl (Val.arr l cn) _ τ hcτ (vN_le hj hfam) hcτ'
  show rwp (ℍ := ℍ) _ _ j ls₃ ((Kont.pairR (Val.arr l cn) Kont.hole).plug
    (.app (.val g) (.val (Val.arr l cn)))) τ
  refine rwp_bind hΦi _ ?_
  refine rwp_mono_le (fun j' hj' ls₄ w ρw hw => ?_) (rwp_of_erwp_empty (erwp_of_cN_ret happ))
  refine rwp_val (v := Val.pair (Val.arr l cn) w) ?_
  obtain ⟨β, hβ, hwB, -⟩ := hw
  exact ⟨w, rfl, by rw [← hBδ α]; exact hwB⟩

/-- **`slice_borrow` at `SemJN`** (Core's `sliceBorrowI_compatX`). -/
theorem sliceBorrowI_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {A B : VTy} (x : LifeVar)
    (hΓ : Ctx.DeadP Γ) (hsc : VScoped Δ A) (hsideA : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A)
    (hsideB : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b B) (hfree₁ : ¬ VFree x A)
    (hfree₂ : ¬ VFree x B) :
    SemJN (ℍ := ℍ) Δ Γ withbor (.val (sliceBorrowITy x Δ.meetOfDom A B)) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  obtain rfl := gN_deadP hΓ hg
  refine cN_ret_of ?_
  show erwp (ℍ := ℍ) (Θ.view c) (opTableN OpTabN.empty) _ n ls (substAll γ withbor) _
  rw [show substAll γ withbor = withbor from psub_closedAt _ γ (by decide) (Nat.zero_le 0)]
  exact erwp_val (v := withborVal)
    (sliceBorrowI_sem hδ (admWf_of_vScoped hsc hδ) hsideA hsideB hfree₁ hfree₂ Θ n)

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N


end
