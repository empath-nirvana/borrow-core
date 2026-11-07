import Core.Chain.ImmLendKW835N

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

/-!
# `withload` at the pure row, at the typed world  `[spec §62]`

`withload_rebT` (6.150 at the run's first entry) at `vN`, over any one-world table `T` with the
reborrow's premises (`hTab`, `hClo`); at the pure row `T` is the empty table, where both hold of
no entry. `withload_compatN` is `Borrow834N`'s proof with it.
-/

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel (LtLife substAll)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Kont Head eLoad eStore)


theorem vO_le {A : VTy} {δ : LSub} {Θ : LocTy} {k n : Nat} (hkn : k ≤ n) {v : Val} {ρ : WRes}
    (h : vO (ℍ := ℍ) A δ Θ n v ρ) : vO (ℍ := ℍ) A δ Θ k v ρ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkn
  clear hkn
  induction d with
  | zero => exact h
  | succ d ihd => exact ihd (vO_down A δ Θ _ v ρ (by rwa [← Nat.add_assoc] at h))


/-- **Step 8 at the run's first entry** (`withload_compatX`'s steps 6–11): the loaded cell
`ℓ ↦ imm(s, v, σ)`, its payload observable at `A`, its location witnessed in the world's `imm`
records, and the callback. At the run's first entry the tie puts the witness's record on the
run's list (`cohE_of_immWitW`); the cell is that record's own cell (`TI`'s `leInvW`) or one of
its chain views (`exIn`); the image re-taken at a `β` below the cell, the callback's stratum and
the bound is a value of `Imm̲ 'x A` (`relabel_vN`), and 6.150 across the callback's stops, raises
and layered cancel runs (`erwp_rebGen`) gives the run. The table's premises are `hTab` (the
table may be stopped at under the reborrow) and `hClo` (its cancel obligations are closed under
it). The callback's run at the image is the premise `hcb`: at a suspending row
`callback_at_image`, at an unwinding row `callback_at_imageU`, at the pure row its `F (U …)`
form. -/
theorem withload_rebT {x : LifeVar} {bnd : Lifetime.Life} {A B : VTy}
    {T : OpTabN} {δ : LSub} (hbnd : ∃ γ, bnd.interp δ = some γ) (hA : ¬ VFree x A)
    {Θ : LocTy} {c : Loc → Option Life}
    (hTab : ∀ β, LtLife δ bnd β → T.RebOKR β)
    (hClo : ∀ β, LtLife δ bnd β → ∀ {le : Loc} {s : LSet} {v : Val} {R : WRes}
      {hs : R.InStratum s.join} {χ : WRes} {Ok : List SRec → Prop},
      RebEntryG (ℍ := ℍ) (Θ.view c) β (ResU.single le (CellU.immOf s v R hs)) χ R Ok →
      ResU.Reb β R χ →
      (∀ (ls ls'' lsO : List SRec) (ψ Ks : WRes), Ok ls → (∀ y, y ∈ ls'' ↔ y ∈ ls) →
        ResU.CompS ψ (ResU.single le (CellU.immOf s v R hs)) Ks → extF ls'' lsO Ks → Ok lsO) →
      RebClosed β (ResU.single le (CellU.immOf s v R hs)) χ Ok
        T)
    {n : Nat} {ls : List SRec} {f v : Val} {l : Loc} {s : LSet} {σ : WRes}
    {h : σ.InStratum s.join} {ρf X : WRes}
    (hpay : vO (ℍ := ℍ) A δ Θ n v σ) (hwit : ImmWitW Θ.imm l s A δ)
    (hcb : ∀ β, LtLife δ bnd β → ∀ (u : Val) (χ Bχ : WRes),
      (∀ m (ψ : CellU Loc Val), χ.get m = some ψ → ψ.kind = Kind.imm) → u = v → ResU.Reb β σ χ →
      vN (ℍ := ℍ) (A.immReborrow (.var x)) (δ.extend x β) Θ n u χ → ResU.CompS ρf χ Bχ →
      erwp (ℍ := ℍ) (Θ.view c) (opTableN T)
        (RebPost β (fun k _ v ρ => vN (ℍ := ℍ) B δ Θ k v ρ)) n ls
        (.app (.app (.val f) (.val .unit)) (.val u)) Bχ)
    (hX : ResU.CompS (ResU.single l (CellU.immOf s v σ h)) ρf X) :
    erwp (ℍ := ℍ) (Θ.view c) (opTableN T)
      (fun k _ v ρ => vN (ℍ := ℍ) B δ Θ k v ρ) n ls
      (.app (.app (.val f) (.val .unit)) (.val v)) X := by
  rw [erwp_eq]
  intro ρF fρ ps μ hF hcF hT htg hI hl hfd j μ' e' hj hrun hfin
  -- the cell is a top-level piece of the run's typed world
  obtain ⟨Fr, -, hcell⟩ := compS_lcomm hX hcF
  have hTI := hT.inv
  obtain ⟨aW, haW⟩ := agW_of_valid hT.valid
  obtain ⟨s'', hs'', hle⟩ := cell_of_compS_single hcell
  obtain ⟨φ₁, eφ₁, kφ₁, rφ₁, wφ₁⟩ := AgW.get_imm haW hle (CellU.kind_immOf _ _ _ _)
  simp only [CellU.erase_immOf, CellU.wit_immOf] at rφ₁ wφ₁
  -- step 6: the tie puts the witness's record on the run's list
  have hI' : ImmTieL Θ.imm ls := hI
  obtain ⟨xr, hxr, hxrs, d, hd, hdmem, S₀, δ₀, he, hcoh⟩ := cohE_of_immWitW hT hI' hwit
  -- the source's payload is bounded by the run's tags
  have hLσ : LifeBoundW Θ.imm σ := lifeBoundW_of_entry (hash_valid_comp hF hcF) htg hI' hle
  have hR₀ : vShape d.T d.δ d.v d.R := (hTI.1.2.2.2.1 d hdmem).1
  -- step 9: the fresh `β`, below the cell, the callback's stratum and the bound
  obtain ⟨γb, hγb⟩ := hbnd
  obtain ⟨g, hg⟩ := ResU.exists_stratum ρf
  set β : Life := ↓(s.meet ⊓ g ⊓ γb) with hβdef
  have hβlt : β < s.meet ⊓ g ⊓ γb := Life.down_sqsubset _
  have hβs : β < s.meet := lt_of_lt_of_le hβlt (inf_le_left.trans inf_le_left)
  have hβx : β ≤ xr.2 := hβs.le.trans hxrs
  have hβg : β ≤ g := (lt_of_lt_of_le hβlt (inf_le_left.trans inf_le_right)).le
  have hLt : LtLife δ bnd β := ⟨γb, hγb, lt_of_lt_of_le hβlt inf_le_right⟩
  have hσβ : σ.InStratum β := h.mono (hβs.le.trans (LSet.meet_le_join s))
  have hbβ : ρf.InStratum β := hg.mono hβg
  have hT' := hTab β hLt
  rcases hcoh with ⟨rfl, rfl, hag⟩ | ⟨p, u₀, hch, hag⟩
  · -- the record's own cell: `v = d.v`, `σ = d.R`
    obtain ⟨φ, eφ, -, rφ, wφ⟩ := hTI.leInvW d hdmem aW haW
    rw [eφ₁] at eφ; cases Option.some.inj eφ
    have hv : v = d.v := rφ₁.symm.trans rφ
    have hσ : σ = d.R := wφ₁.symm.trans wφ
    subst hv hσ
    -- step 7: the template, from 6.132 at the record's shape
    set y := d.T.lifeBound with hydef
    have hy : ¬ VFree y d.T := fun hf' => lt_irrefl _ (lt_vLifeBound hf')
    obtain ⟨γ, hγ⟩ := six132_shape_fresh hy d.δ d.v d.R hR₀
    obtain ⟨⟨χ₀, hreb₀, hsh₀⟩, -⟩ := hγ (↓γ) (Life.down_sqsubset γ)
    have hSt : TmplSpec d (tmpl d) := tmpl_spec (tmpl_exists hT hdmem hcell hy hreb₀ hsh₀)
    have hheA : TyEq A δ d.T d.δ := he.trans (TyEq.of_agree d.T hag)
    -- step 8: the image re-taken at `β`, typed at `Imm̲ 'x A`
    have himg : vN (ℍ := ℍ) (A.immReborrow (.var x)) (δ.extend x β) Θ n d.v (canon d β) := by
      obtain ⟨β₁, x₁, hx₁, hreb₁, hden₁, -⟩ := hSt
      have hden₁' : vShape (A.immReborrow (.var x)) (δ.extend x β₁) d.v (tmpl d) := by
        rw [vShape_tyEq (tyEq_immReb hheA hA hx₁ β₁)]; exact hden₁
      exact relabel_vN A hA hA hden₁' hpay (CellMatch.of_le ⟨_, ResU.comp_empty_right _⟩)
        (fun m ψ e => reb_cell_match hreb₁ e) (reb_wit_stratum hσβ hreb₁)
        (lifeBoundOn_reb hreb₁ hLσ) (lifeBoundWit_reb hreb₁ hLσ)
        (fun m S u hpos hown => immWitW_root hxr hd he hag hA hβx hpos hown)
        (fun m S hpos => immWitW_rootMut hxr hd hR₀ he hag hA hβx hpos)
    have hshape : vShape (d.T.immReborrow (.var y)) (d.δ.extend y β) d.v (canon d β) := by
      rw [← vShape_tyEq (tyEq_immReb hheA hA hy β)]
      exact vN_vShape _ _ _ _ _ _ himg
    have hreb := canon_reb hSt hσβ
    have hE := rebEntryG_top (ℍ := ℍ) (Φ := Θ.view c) (hs := h) d y hy hSt hσβ hshape
      (fun z hz => hβs.le.trans (s.meet_least z hz))
    have hcan := hClo β hLt hE hreb okKept_top
    have hrun' := erwp_rebGen hE hreb okKept_top hT' hcan
      (Q := fun k _ v ρ => vN (ℍ := ℍ) B δ Θ k v ρ) n ls
      (.app (.app (.val f) (.val .unit)) (.val d.v)) ρf X hX hbβ hdmem
      (fun Bχ hBχ => hcb β hLt _ _ Bχ (reb_allImm hreb) rfl hreb himg hBχ)
    rw [erwp_eq] at hrun'
    exact hrun' ρF fρ ps μ hF hcF hT htg hI hl hfd j μ' e' hj hrun hfin
  · -- a chain view: the cell's value is the chain's (`ex(R)_○` lifts into `ag(W)`)
    obtain ⟨e₀, he₀, hlift⟩ := hTI.exIn hdmem aW haW
    obtain ⟨ζ, eζ, rζ, -⟩ := exR_cell he₀ hch.own (by simp)
    obtain ⟨ζ', eζ', rζ', -⟩ := hlift l ζ eζ
    rw [eφ₁] at eζ'; cases Option.some.inj eζ'
    simp only [CellU.erase_ownOf] at rζ
    have hv : v = u₀ := rφ₁.symm.trans (rζ'.trans rζ)
    subst hv
    -- the view's owned cells are the record's, and its witness is shaped (`DeepInv`)
    obtain ⟨-, hσden, hσown, -, -⟩ :=
      hTI.1.1 d hdmem p l S₀ v hch aW haW φ₁ eφ₁ (by rw [kφ₁]; simp)
    rw [wφ₁] at hσden hσown
    -- step 7: the view's template, from 6.132 at the view's shape
    set y := S₀.lifeBound with hydef
    have hy : ¬ VFree y S₀ := fun hf' => lt_irrefl _ (lt_vLifeBound hf')
    obtain ⟨γ, hγ⟩ := six132_shape_fresh hy d.δ v σ hσden
    obtain ⟨⟨χ₀, hreb₀, hsh₀⟩, -⟩ := hγ (↓γ) (Life.down_sqsubset γ)
    have hSt : TmplSpecD d S₀ v σ (tmplD d S₀ v σ) :=
      tmplD_spec (tmplD_exists hch hT hdmem hcell hy hreb₀ hsh₀)
    have hheA : TyEq A δ S₀ d.δ := he.trans (TyEq.of_agree S₀ hag)
    -- step 8: the view's image re-taken at `β`, typed at `Imm̲ 'x A`
    have himg : vN (ℍ := ℍ) (A.immReborrow (.var x)) (δ.extend x β) Θ n v
        (canonD d S₀ v σ β) := by
      obtain ⟨β₁, x₁, hx₁, hreb₁, hden₁, -⟩ := hSt
      have hden₁' : vShape (A.immReborrow (.var x)) (δ.extend x β₁) v (tmplD d S₀ v σ) := by
        rw [vShape_tyEq (tyEq_immReb hheA hA hx₁ β₁)]; exact hden₁
      exact relabel_vN A hA hA hden₁' hpay (CellMatch.of_le ⟨_, ResU.comp_empty_right _⟩)
        (fun m ψ e => reb_cell_match hreb₁ e) (reb_wit_stratum hσβ hreb₁)
        (lifeBoundOn_reb hreb₁ hLσ) (lifeBoundWit_reb hreb₁ hLσ)
        (fun m S u hpos hown => immWitW_child hxr hd hch he hag hA hβx hpos (hσown m u hown))
        (fun m S hpos => immWitW_childMut hxr hd hR₀ hch he hag hA hβx hpos)
    have hshape : vShape (S₀.immReborrow (.var y)) (d.δ.extend y β) v (canonD d S₀ v σ β) := by
      rw [← vShape_tyEq (tyEq_immReb hheA hA hy β)]
      exact vN_vShape _ _ _ _ _ _ himg
    have hreb := canonD_reb hSt hσβ
    have hβc : (CellU.immOf s v σ h).InStratum β := (CellU.inStratum_immOf β s v σ h).mpr hβs
    have hE := rebEntryG_deep (ℍ := ℍ) (Φ := Θ.view c) d hch y hy hSt hσβ hβc hshape
    have hcan := hClo β hLt hE hreb (okKept_deep hch)
    have hrun' := erwp_rebGen hE hreb (okKept_deep hch) hT' hcan
      (Q := fun k _ v ρ => vN (ℍ := ℍ) B δ Θ k v ρ) n ls
      (.app (.app (.val f) (.val .unit)) (.val v)) ρf X hX hbβ hdmem
      (fun Bχ hBχ => hcb β hLt _ _ Bχ (reb_allImm hreb) rfl hreb himg hBχ)
    rw [erwp_eq] at hrun'
    exact hrun' ρF fρ ps μ hF hcF hT htg hI hl hfd j μ' e' hj hrun hfin


/-- **`withload` at `SemJN`** (Core's `withload_compatX`):
`Imm @a A ⊸ (∀'x ⊏ @Δ. Imm̲ 'x A ⊸ ['x] B) ⊸ B` at the pure row. Core's steps: the `Imm`
argument at the callback's world (`vC_local`, here `vN_extR`); the load (`wpTS_load_I`, here
`rwp_load_cell` under `erwp_bindR`); 6.150 at the record the program's own `Imm` value
witnesses (`wpTS_reborrow`, here `withload_rebT` at the empty table), the callback run at the image
(`callback_at_imageP`). -/
theorem withload_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {A B : VTy}
    (x : LifeVar) (hΓ : Ctx.DeadP Γ) (hA : ¬ VFree x A) (hB : ¬ VFree x B) :
    SemJN (ℍ := ℍ) Δ Γ withload (.val (axWithloadTy a x Δ.meetOfDom A B)) := by
  intro δ γ Θ c n ls ρ hδ _ _ _ hg
  obtain rfl := gN_deadP hΓ hg
  refine cN_ret_of ?_
  show erwp (ℍ := ℍ) (Θ.view c) (opTableN OpTabN.empty) _ n ls (substAll γ withload) _
  rw [show substAll γ withload = withload from psub_closedAt _ γ (by decide) (Nat.zero_le 0)]
  refine erwp_val (v := withloadV) ?_
  intro Θ₁ _ hΘ₁ _ _ ls₁ c₂ k₁ _ v₁ τ₀ ρ₁ hcomp hv₁ _
  obtain rfl := eq_of_compS_empty_left hcomp
  obtain ⟨-, -, ⟨l, -, -, -, -, rfl, -, -, -⟩, -⟩ := id hv₁
  have hΦ₁ : (Θ₁.view c₂).Down := LocTy.view_down hΘ₁.1 c₂
  refine cN_ret_of ?_
  refine erwp_det hΦ₁ (opTableN_down OpTabN.empty_down) (fun k _ v ρ h => vN_down _ δ Θ₁ k v ρ h)
    (fun μ => step1Only_plug (Head.beta μ _ (Val.loc l)) rfl .hole) ?_
  have e₁ : Kont.hole.plug (Expr.subst 0 (Val.loc l)
      (Val.lam (.app (.app BoCa.v0 unit') (.app load' BoCa.v1))).1) = (withloadAt l).1 := by
    simp [Kont.plug, Expr.subst, Expr.shift, withloadAt, BoCa.v0, BoCa.v1, unit', load', Val.loc,
      Val.lam, Expr.val, Val.unit, Val.prim]
  rw [e₁]
  refine erwp_val (v := withloadAt l) ?_
  -- the callback, at the world the body's `U` reached; the source arrives there along `ExtR`
  intro Θ₂ hE₂ hΘ₂ _ _ ls₂ c k₂ hk₂ f ρf ρ'' hc' hf hcon
  have hΦ : (Θ₂.view c).Down := LocTy.view_down hΘ₂.1 c
  obtain ⟨α₀, hα₀, ⟨l', s, w, σ, hσs, hl', rfl, hα₀s, hpay⟩, hwit⟩ :=
    vN_le hk₂ (vN_extR _ δ k₁ _ _ hE₂ hv₁)
  obtain rfl : l = l' := by have := congrArg Subtype.val hl'; simpa [Val.loc] using this
  refine cN_ret_of ?_
  refine erwp_det hΦ (opTableN_down OpTabN.empty_down) (fun k _ v ρ h => vN_down _ δ Θ₂ k v ρ h)
    (fun μ => step1Only_plug (Head.beta μ _ f) rfl .hole) ?_
  have e₂ : Kont.hole.plug (Expr.subst 0 f
      (.app (.app BoCa.v0 unit') (.app load' (.val (.loc l))))) =
      (Kont.appR (.app (.val f) (.val .unit)) .hole).plug
        (.app (.val (.prim .load)) (.val (Val.loc l))) := by
    simp [Kont.plug, Expr.subst, BoCa.v0, unit', load', Val.loc, Expr.val, Val.prim, Val.unit]
  rw [e₂]
  refine erwp_of_valid fun hv'' => ?_
  have hcf : ConsistentX c ρf := consistentX_right hc' hcon hv''
  -- the load
  refine erwp_bindR hΦ (opTableN_local _) _ ?_
  refine rwp_load_cell ls₂ l s w σ hσs _ hc' ?_
  simp only [Kont.plug]
  -- 6.150 at the record, the callback at the image
  exact withload_rebT (T := OpTabN.empty) (Lifetime.Life.interp_defined_of_wf hδ
      (Lifetime.meetOfDomL_wf Δ.entries)) hA
    (fun _ _ => ⟨fun _ _ _ h => absurd h (by simp [OpTabN.empty]),
      fun _ _ _ h => absurd h (by simp [OpTabN.empty]),
      fun _ _ _ h => absurd h (by simp [OpTabN.empty])⟩)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h => absurd h (by simp [OpTabN.empty]))
    (vO_le (Nat.sub_le k₂ 1) hpay) (hwit l s w σ hσs rfl)
    (fun β hLt u χ Bχ hχ _ _ himg hBχ =>
      callback_at_imageP hB hΘ₂ hLt (vN_le (Nat.sub_le k₂ 1) hf) hcf hχ himg hBχ) hc'



end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
