import Core.Chain.FieldKW835N
import Core.Chain.WithloadKW835N

/-!
# `withload` at a suspending row, at the typed world  `[spec §62]`

Core's `withload_compatX` at a suspending row at `SemJN` (`withloadS_compat`), step for step, over
`Withload791N`'s witness facts: the load (`rwp_load_cell` under
`erwpK_bindR`); at the run's first entry the record the source witnesses, its template and the
image re-taken at a fresh `β` (`withload_reb`, `withload_rebT`'s steps at `erwpK`); 6.150 across
the callback's stops, raises and layered cancel runs at the row's table at the typed world
(`erwpK_rebGen_tab`); the callback at the image as a thunk of `cN` (`callback_at_image`).
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
open BoCa.BoLo (Heap Kont Head performE raiseE cancelVal opPayload)

/-- An entry's cancel obligation matters only where the entry is capturable. -/
theorem entNK_fin_congr {q : Qual} {B : VTy} {PA : Nat → Val → WRes → Prop}
    {PB : KW → Nat → Val → WRes → Prop} {f f' : Option (KW → Nat → List SRec → Expr → WProp)}
    {wk : Life → KW → WRes → Prop} (h : capB q B = true → f = f') :
    entNK q B PA PB f wk = entNK q B PA PB f' wk := by
  unfold entNK
  by_cases hc : capB q B = true
  · rw [h hc]
  · simp only [hc]
    congr 1

/-- A row's cancel obligation at the typed world reads `δ` only through its table. -/
theorem finN_of_tabN : ∀ (F : CTy) {δ₁ δ₂ : LSub},
    (∀ x, tabN (ℍ := ℍ) F δ₁ x = tabN (ℍ := ℍ) F δ₂ x) → finN (ℍ := ℍ) F δ₁ = finN (ℍ := ℍ) F δ₂
  | .eff _ _ _ _ _ _ _ _, _, _, h => by
      simp only [tabN] at h
      simp only [finN, h]
  | .ret _, _, _, _ => rfl
  | .arr _ _, _, _, _ => rfl
  | .amp _ _, _, _, _ => rfl
  | .top, _, _, _ => rfl
  | .all _ _ _, _, _, _ => rfl
  | .nu _, _, _, _ => rfl

/-- **A row whose layers do not mention `'x` has one table at the typed world at `δ` and
`δ['x ↦ α]`.** -/
theorem tabN_extend_suspendC {x : LifeVar} {bnd : Lifetime.Life} (α : Life) :
    ∀ (F : CTy), F.SuspendC x bnd → ∀ (δ : LSub) (y : KW),
      tabN (ℍ := ℍ) F (δ.extend x α) y = tabN (ℍ := ℍ) F δ y
  | .eff m i q A B fin rc C, hF, δ, y => by
      obtain ⟨⟨_, hA, hB, _, _, hfin⟩, hC⟩ := hF
      simp only [tabN]
      rw [vN_extend_of_not_free hA, vN_extend_of_not_free hB,
        tabN_extend_suspendC α C hC δ y,
        entNK_fin_congr (f := finN (ℍ := ℍ) fin (δ.extend x α)) (f' := finN (ℍ := ℍ) fin δ)
          (fun hcap => finN_of_tabN fin (tabN_extend_suspendC α fin (hfin hcap) δ))]
  | .ret _, _, _, _ => rfl
  | .arr _ _, _, _, _ => rfl
  | .amp _ _, _, _, _ => rfl
  | .top, _, _, _ => rfl
  | .all _ _ _, _, _, _ => rfl
  | .nu _, _, _, _ => rfl

/-- **The callback at the image, at `SemJN`**: the callback, at
`β ⊏ @bnd`, applied to the image `χ` of the loaded payload, typed at `Imm̲ 'x A`, runs at the
constant's table at the typed world, with `[β]𝒱⟦B⟧` as its post, from every world at `Θ`. -/
theorem callback_at_image {x : LifeVar} {bnd : Lifetime.Life} {A B : VTy} {S : Row}
    (hB : ¬ VFree x B) (hS : S.Suspend x bnd) {δ : LSub} {Θ : LocTy} (hΘ : Θ.OK)
    {c : Loc → Option Life} {n : Nat} {ls : List SRec} {f u : Val} {ρf χ Bχ : WRes} {β : Life}
    (hLt : LtLife δ bnd β)
    (hf : vN (ℍ := ℍ) (cbUTy x bnd (A.immReborrow (.var x)) B S) δ Θ n f ρf)
    (hcf : ConsistentX c ρf) (hχ : ∀ m (ψ : CellU Loc Val), χ.get m = some ψ → ψ.kind = Kind.imm)
    (himg : vN (ℍ := ℍ) (A.immReborrow (.var x)) (δ.extend x β) Θ n u χ)
    (hBχ : ResU.CompS ρf χ Bχ) (lo : Life) :
    erwpK (ℍ := ℍ) KW.PostK (fun z => z.Θ.view z.c)
      (fun z => opTableK z.lo (tabN (ℍ := ℍ) (CTy.effOf S B) δ z))
      (fun y => RebPost β (fun k _ v ρ => vN (ℍ := ℍ) B δ y.Θ k v ρ)) ⟨Θ, c, lo⟩ n ls
      (.app (.app (.val f) (.val .unit)) (.val u)) Bχ := by
  have h1 := (hf Θ (LocTy.extR_refl _ _) hΘ c hcf ls) β hLt
  have hcon : ConsistentX c Bχ := consistentX_compS hBχ hcf (consistentX_allImm hχ c)
  have h2 := h1 c n le_rfl u χ Bχ hBχ himg hcon
  rw [cN_effOf] at h2
  have h3 := h2 lo
  simp only [tabN_extend_suspendC β _ (suspendC_effOf hS _) δ,
    tabN_effOf_base S (.box (.var x) B) B δ] at h3
  refine erwpK_mono (fun _ _ h => h) (fun y k _ w ρ hb => ?_)
    (fun z k ls t Ψ Ψ' ρ hΨ h => opTableK_local z.lo (tabN (ℍ := ℍ) (CTy.effOf S B) δ z) k ls t Ψ
      Ψ' ρ hΨ h) n _ ls _ Bχ h3
  obtain ⟨α', hα', hbB, hst⟩ := hb
  rw [interp_ext_self] at hα'
  cases Option.some.inj hα'
  rw [vN_extend_of_not_free hB] at hbB
  exact ⟨hbB, hst⟩

/-- **Step 8 at the run's first entry, at the typed world** (`withload_rebT`'s
steps at `erwpK`): the loaded cell `ℓ ↦ imm(s, v, σ)`, its payload observable at `A`, its location
witnessed in the world's `imm` records, and the callback. At the run's first entry the tie puts
the witness's record on the run's list (`cohE_of_immWitW`); the cell is that record's own cell
(`TI`'s `leInvW`) or one of its chain views (`exIn`); the image re-taken at a `β` below the cell,
the callback's stratum and the bound is a value of `Imm̲ 'x A` (`relabel_vN`), and 6.150 across
the callback's stops, raises and layered cancel runs at the row's table at the typed world
(`erwpK_rebGen_tab`, its entry at every view: `rebEntryGV_top`, `rebEntryGV_deep`) gives the
run. -/
theorem withload_reb {x : LifeVar} {bnd : Lifetime.Life} {A B : VTy}
    {S : Row} {δ : LSub} (hbnd : ∃ γ, bnd.interp δ = some γ) (hA : ¬ VFree x A)
    (hS : S.Suspend x bnd) {y₀ : KW}
    {n : Nat} {ls : List SRec} {f v : Val} {l : Loc} {s : LSet} {σ : WRes}
    {h : σ.InStratum s.join} {ρf X : WRes}
    (hpay : vO (ℍ := ℍ) A δ y₀.Θ n v σ) (hwit : ImmWitW y₀.Θ.imm l s A δ)
    (hcb : ∀ β, LtLife δ bnd β → ∀ (u : Val) (χ Bχ : WRes),
      (∀ m (ψ : CellU Loc Val), χ.get m = some ψ → ψ.kind = Kind.imm) → u = v → ResU.Reb β σ χ →
      vN (ℍ := ℍ) (A.immReborrow (.var x)) (δ.extend x β) y₀.Θ n u χ → ResU.CompS ρf χ Bχ →
      erwpK (ℍ := ℍ) KW.PostK (fun z => z.Θ.view z.c)
        (fun z => opTableK z.lo (tabN (ℍ := ℍ) (CTy.effOf S B) δ z))
        (fun y => RebPost β (fun k _ v ρ => vN (ℍ := ℍ) B δ y.Θ k v ρ)) y₀ n ls
        (.app (.app (.val f) (.val .unit)) (.val u)) Bχ)
    (hX : ResU.CompS (ResU.single l (CellU.immOf s v σ h)) ρf X) :
    erwpK (ℍ := ℍ) KW.PostK (fun z => z.Θ.view z.c)
      (fun z => opTableK z.lo (tabN (ℍ := ℍ) (CTy.effOf S B) δ z))
      (fun y k _ v ρ => vN (ℍ := ℍ) B δ y.Θ k v ρ) y₀ n ls
      (.app (.app (.val f) (.val .unit)) (.val v)) X := by
  have hFS := suspendC_effOf hS B
  -- the reborrow at the row's table at the typed world
  have hRK : ∀ (β : Life), LtLife δ bnd β → ∀ {le : Loc} {s : LSet} {v : Val} {R : WRes}
      {hs : R.InStratum s.join} {χ : WRes} {Ok : List SRec → Prop},
      (∀ x : KW, RebEntryGP (ℍ := ℍ) (x.Θ.view x.c) β (ResU.single le (CellU.immOf s v R hs))
        χ R Ok (fun w Y => ResU.Valid w ∧ ResU.Valid Y)) →
      ResU.Reb β R χ →
      (∀ (ls ls'' lsO : List SRec) (ψ Ks : WRes), Ok ls → (∀ y, y ∈ ls'' ↔ y ∈ ls) →
        ResU.CompS ψ (ResU.single le (CellU.immOf s v R hs)) Ks → extF ls'' lsO Ks → Ok lsO) →
      RKFrame (ℍ := ℍ) KW.PostK (fun y => y.Θ.view y.c) (fun _ => True) β
        (ResU.single le (CellU.immOf s v R hs)) χ Ok
        (fun z => opTableK z.lo (tabN (ℍ := ℍ) (CTy.effOf S B) δ z))
        (fun z => opTableK z.lo (tabN (ℍ := ℍ) (CTy.effOf S B) δ z))
        (fun y => RebPost β (fun k _ v ρ => vN (ℍ := ℍ) B δ y.Θ k v ρ))
        (fun y k _ v ρ => vN (ℍ := ℍ) B δ y.Θ k v ρ) := by
    intro β hLt le s v R hs χ Ok hE hreb hOk
    have hfr := erwpK_rebGen_tab (ℍ := ℍ) valRelOK_vN (V := KW.PostK) hLt hE hreb hOk hFS
      (Q := fun y k _ v ρ => vN (ℍ := ℍ) B δ y.Θ k v ρ)
    simpa only [tabNK_vN] using hfr
  rw [erwpK_eq]
  intro ρF fρ ps μ hF hcF hT htg hI hl hfd j μ' e' hj hrun hfin
  -- the cell is a top-level piece of the run's typed world
  obtain ⟨Fr, -, hcell⟩ := compS_lcomm hX hcF
  have hTI := hT.inv
  obtain ⟨aW, haW⟩ := agW_of_valid hT.valid
  obtain ⟨s'', hs'', hle⟩ := cell_of_compS_single hcell
  obtain ⟨φ₁, eφ₁, kφ₁, rφ₁, wφ₁⟩ := AgW.get_imm haW hle (CellU.kind_immOf _ _ _ _)
  simp only [CellU.erase_immOf, CellU.wit_immOf] at rφ₁ wφ₁
  -- step 6: the tie puts the witness's record on the run's list
  have hI' : ImmTieL y₀.Θ.imm ls := hI
  obtain ⟨xr, hxr, hxrs, d, hd, hdmem, S₀, δ₀, he, hcoh⟩ := cohE_of_immWitW hT hI' hwit
  -- the source's payload is bounded by the run's tags
  have hLσ : LifeBoundW y₀.Θ.imm σ := lifeBoundW_of_entry (hash_valid_comp hF hcF) htg hI' hle
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
    have himg : vN (ℍ := ℍ) (A.immReborrow (.var x)) (δ.extend x β) y₀.Θ n d.v (canon d β) := by
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
    have hE := fun z : KW => rebEntryGV_top (ℍ := ℍ) (Φ := z.Θ.view z.c) (hs := h) d y hy hSt hσβ
      hshape (fun z hz => hβs.le.trans (s.meet_least z hz))
    have hrun' := hRK β hLt hE hreb okKept_top n y₀ trivial ls
      (.app (.app (.val f) (.val .unit)) (.val d.v)) ρf X hX hbβ hdmem
      (fun Bχ hBχ => hcb β hLt _ _ Bχ (reb_allImm hreb) rfl hreb himg hBχ)
    rw [erwpK_eq] at hrun'
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
    have himg : vN (ℍ := ℍ) (A.immReborrow (.var x)) (δ.extend x β) y₀.Θ n v
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
    have hE := fun z : KW => rebEntryGV_deep (ℍ := ℍ) (Φ := z.Θ.view z.c) d hch y hy hSt hσβ hβc
      hshape
    have hrun' := hRK β hLt hE hreb (okKept_deep hch) n y₀ trivial ls
      (.app (.app (.val f) (.val .unit)) (.val v)) ρf X hX hbβ hdmem
      (fun Bχ hBχ => hcb β hLt _ _ Bχ (reb_allImm hreb) rfl hreb himg hBχ)
    rw [erwpK_eq] at hrun'
    exact hrun' ρF fρ ps μ hF hcF hT htg hI hl hfd j μ' e' hj hrun hfin

/-- **`withload` at a suspending row is a value of `!` its type, at `SemJN`**: at
`Imm @a A ⊸ (∀'x ⊏ @bnd. Imm̲ 'x A ⊸ F_Σ(['x] B)) ⊸ F_Σ B` with `Σ` a `Row.Suspend x bnd` row.
Its steps at every floor: the load (`rwp_load_cell` under `erwpK_bindR`); at the
run's first entry the record, its template and the image (`withload_reb`); 6.150 at the row's table
at the typed world; the callback at the image as a thunk of `cN` (`callback_at_image`).

Premises those of the rule. -/
theorem withloadS_compat {a : Lifetime.Life} {x : LifeVar} {bnd : Lifetime.Life} {A B : VTy}
    {S : Row} (hbnd : LifeCtx.empty.Defines bnd) (hA : ¬ VFree x A) (hB : ¬ VFree x B)
    (hS : S.Suspend x bnd) (δ : LSub) (Θ₀ : LocTy) (n : Nat) :
    vN (ℍ := ℍ) (.bang (withloadUTy a x bnd A B S)) δ Θ₀ n withloadV PMap.empty := by
  refine ⟨rfl, fun Θ _ hΘ c₁ _ ls => ?_⟩
  intro c₂ k hk u ρv ρu hc hu _
  obtain rfl := eq_of_compS_empty_left hc
  intro c k' hk' f ρf ρ'' hc' hf hcon
  obtain ⟨α₀, hα₀, ⟨l, s, w, σ, hσs, rfl, rfl, hα₀s, hpay⟩, hwit⟩ :=
    vN_le hk' hu
  rw [cN_effOf]
  intro lo
  refine erwpK_of_valid fun hv'' => ?_
  have hcf : ConsistentX c ρf := consistentX_right hc' hcon hv''
  have hΦ : ((⟨Θ, c, lo⟩ : KW).Θ.view (⟨Θ, c, lo⟩ : KW).c).Down := LocTy.view_down hΘ.1 c
  have hTd : (opTableK lo (tabN (ℍ := ℍ) (CTy.effOf S B) δ ⟨Θ, c, lo⟩)).Down :=
    opTableK_downI (tabN_downI_OK _ δ ⟨Θ, c, lo⟩)
  have hQo : ∀ z : KW, PostN.Down (fun k _ v ρ => vN (ℍ := ℍ) B δ z.Θ k v ρ) :=
    fun z k _ v ρ h => vN_down _ δ z.Θ k v ρ h
  refine erwpK_det (Φ := fun z : KW => z.Θ.view z.c) (x := ⟨Θ, c, lo⟩) hΦ hTd hQo
    (fun μ => step1Only_plug (Head.beta μ _ (Val.loc l)) rfl (.appL .hole f)) ?_
  refine erwpK_det (Φ := fun z : KW => z.Θ.view z.c) (x := ⟨Θ, c, lo⟩) hΦ hTd hQo
    (fun μ => step1Only_plug (Head.beta μ _ f) rfl .hole) ?_
  have e₃ : Kont.hole.plug (Expr.subst 0 f (Expr.subst (0 + 1) (Val.shift 1 0 (Val.loc l))
        (.app (.app v0 unit') (.app load' v1)))) =
      (Kont.appR (.app (.val f) (.val .unit)) .hole).plug
        (.app (.val (.prim .load)) (.val (Val.loc l))) := by
    simp [Kont.plug, Expr.subst, Expr.shift, Val.shift, Val.loc, Expr.val, Val.prim, v0, v1,
      unit', load', Val.unit]
  rw [e₃]
  -- the load
  refine erwpK_bindR (Φ := fun z : KW => z.Θ.view z.c) (x := ⟨Θ, c, lo⟩)
    (fun z => opTableK_local _ _) hΦ _ ?_
  refine rwp_load_cell ls l s w σ hσs _ hc' ?_
  -- 6.150 at the record, the callback at the image
  simp only [Kont.plug]
  exact withload_reb (y₀ := ⟨Θ, c, lo⟩) (hbnd δ (models_empty_any _)) hA hS
    (vO_le (Nat.sub_le k' 1) hpay) (hwit l s w σ hσs rfl)
    (fun β hLt u χ Bχ hχ _ _ himg hBχ =>
      callback_at_image hB hS hΘ hLt (vN_le (Nat.sub_le k' 1) hf) hcf hχ himg hBχ lo) hc'

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
