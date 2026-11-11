import Core.Chain.TabKW835N
import Core.Chain.MechK835N4
import Core.Chain.HandleK835N

/-!
# The field reborrow's frame and the finaliser's raise at the typed tables  `[spec §19, §27, §62]`

`docs/new-core/scope-835-tables.md` §8. Two premises of the mechanical producers read off the
typed tables at `KW`:

* **the guarded twin with the frame** (`tabGK_canF`): the field reborrow
  `withborF` frames `ℓ ↦ own(loc ℓ₂)` outside the Mut Frame at the field (`erwpK_frameGR`); the
  guarded twin's cancel obligations with the frame beside the share are the twin's, by induction on
  how deep cancel rows nest, each step `erwpK_frame_cancelRunGR` at the cancel row's tables. The
  entries' order at the joint share gives it at the run's share (`KW.Owed.left`), the joint share
  being valid;
* **the abortive payload across a finaliser's stops** (`tabNK_raiseOwed`, the premise `hTk` of
  `erwpK_ubindRaiseF`): an entry's order at the joint share is `ExtR` there, so the payload, a
  value of `A` at a part of it, is one at the resumption world (`ValRelOK.extR`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa.Fig16.LogRel (LtLife)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Kont performE raiseE cancelVal opPayload hndE hndVal)

/-! ### The orders at a part of the share -/

/-- `KW.Owed` at a part of a valid share. -/
theorem KW.Owed.left {x y : KW} {f : Life} {ρ₁ ρ₂ ρ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ)
    (hv : ResU.Valid ρ) (h : x.Owed f y ρ) : x.Owed f y ρ₁ :=
  ⟨⟨h.1.1.left hc, h.1.2.1, h.1.2.2⟩, h.2.1, consistentX_left hc h.2.2.1 hv, h.2.2.2.1,
    h.2.2.2.2⟩

/-- `KW.OwedR` at a part of a valid share. -/
theorem KW.OwedR.left {x y : KW} {ρ₁ ρ₂ ρ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ)
    (hv : ResU.Valid ρ) (h : x.OwedR y ρ) : x.OwedR y ρ₁ :=
  ⟨h.1.left hc, h.2.1, consistentX_left hc h.2.2 hv⟩

/-! ### Lookups at another world and another claim -/

/-- **An entry of `tabNK` is a layer's, and `tabNK` at every world map and every world has the
layer's entry at the same key.** -/
theorem tab_lookupNNK : ∀ (F : CTy) {vr : VRel} {g : KW → KW} {δ : LSub} {x : KW}
    {m j : UInt32} {en : OpEntK KW},
    tabNK (ℍ := ℍ) vr g F δ x m j = some en → ∃ q A B fin, F.LayerOf q A B fin ∧
      en = entNK q B (fun k v ρ => vr A δ x.Θ k v ρ)
        (fun y k v ρ => vr B δ y.Θ k v ρ ∧ ConsistentX y.c ρ)
        (finNK (ℍ := ℍ) vr g fin δ) (fun f y ρ => (g x).Owed f (g y) ρ) ∧
      ∀ (g₂ : KW → KW) (x₂ : KW), tabNK (ℍ := ℍ) vr g₂ F δ x₂ m j =
        some (entNK q B (fun k v ρ => vr A δ x₂.Θ k v ρ)
          (fun y k v ρ => vr B δ y.Θ k v ρ ∧ ConsistentX y.c ρ)
          (finNK (ℍ := ℍ) vr g₂ fin δ) (fun f y ρ => (g₂ x₂).Owed f (g₂ y) ρ))
  | .eff m₀ i₀ q A B fin rc C, vr, g, δ, x, m, j, en, h => by
      simp only [tabNK] at h
      unfold extTabK at h
      split at h
      · rename_i hmj
        cases Option.some.inj h
        obtain ⟨rfl, rfl⟩ := hmj
        exact ⟨q, A, B, fin, .inl ⟨rfl, rfl, rfl, rfl⟩, rfl, fun g₂ x₂ => by
          simp only [tabNK, extTabK, and_self, if_true]⟩
      · rename_i hmj
        obtain ⟨q', A', B', fin', hL, he, hR⟩ := tab_lookupNNK C h
        exact ⟨q', A', B', fin', .inr hL, he, fun g₂ x₂ => by
          simp only [tabNK, extTabK, if_neg hmj]; exact hR g₂ x₂⟩
  | .ret _, _, _, _, _, _, _, _, h => by simp [tabNK, OpTabK.empty] at h
  | .arr _ _, _, _, _, _, _, _, _, h => by simp [tabNK, OpTabK.empty] at h
  | .amp _ _, _, _, _, _, _, _, _, h => by simp [tabNK, OpTabK.empty] at h
  | .top, _, _, _, _, _, _, _, h => by simp [tabNK, OpTabK.empty] at h
  | .all _ _ _, _, _, _, _, _, _, _, h => by simp [tabNK, OpTabK.empty] at h
  | .nuSys _ _ _, _, _, _, _, _, _, _, h => by simp [tabNK, OpTabK.empty] at h

/-- **An entry of `tabGK` is a layer's, and every `tabGK` at the same world has the layer's entry at
the same key, its cancel run at its own guard and claim.** -/
theorem tab_lookupGGK : ∀ (F : CTy) {R : Nat → WProp} {G : ShareG} {vr : VRel}
    {g : KW → KW} {δ : LSub} {x : KW} {m j : UInt32} {en : OpEntK KW},
    tabGK (ℍ := ℍ) R G vr g F δ x m j = some en → ∃ q A B fin, F.LayerOf q A B fin ∧
      en = entNK q B (fun k v ρ => vr A δ x.Θ k v ρ)
        (fun y k v ρ => vr B δ y.Θ k v ρ ∧ ConsistentX y.c ρ)
        (finGK (ℍ := ℍ) R G vr g fin δ) (fun f y ρ => (g x).Owed f (g y) ρ) ∧
      ∀ (R' : Nat → WProp) (G' : ShareG), tabGK (ℍ := ℍ) R' G' vr g F δ x m j =
        some (entNK q B (fun k v ρ => vr A δ x.Θ k v ρ)
          (fun y k v ρ => vr B δ y.Θ k v ρ ∧ ConsistentX y.c ρ)
          (finGK (ℍ := ℍ) R' G' vr g fin δ) (fun f y ρ => (g x).Owed f (g y) ρ))
  | .eff m₀ i₀ q A B fin rc C, R, G, vr, g, δ, x, m, j, en, h => by
      simp only [tabGK] at h
      unfold extTabK at h
      split at h
      · rename_i hmj
        cases Option.some.inj h
        obtain ⟨rfl, rfl⟩ := hmj
        exact ⟨q, A, B, fin, .inl ⟨rfl, rfl, rfl, rfl⟩, rfl, fun R' G' => by
          simp only [tabGK, extTabK, and_self, if_true]⟩
      · rename_i hmj
        obtain ⟨q', A', B', fin', hL, he, hR⟩ := tab_lookupGGK C h
        exact ⟨q', A', B', fin', .inr hL, he, fun R' G' => by
          simp only [tabGK, extTabK, if_neg hmj]; exact hR R' G'⟩
  | .ret _, _, _, _, _, _, _, _, _, _, h => by simp [tabGK, OpTabK.empty] at h
  | .arr _ _, _, _, _, _, _, _, _, _, _, h => by simp [tabGK, OpTabK.empty] at h
  | .amp _ _, _, _, _, _, _, _, _, _, _, h => by simp [tabGK, OpTabK.empty] at h
  | .top, _, _, _, _, _, _, _, _, _, h => by simp [tabGK, OpTabK.empty] at h
  | .all _ _ _, _, _, _, _, _, _, _, _, _, h => by simp [tabGK, OpTabK.empty] at h
  | .nuSys _ _ _, _, _, _, _, _, _, _, _, _, h => by simp [tabGK, OpTabK.empty] at h

/-- Two guarded twins at the same world agree but for the cancel obligations. -/
theorem tabGK_tabGK_twin (R : Nat → WProp) (G : ShareG) (R' : Nat → WProp) (G' : ShareG)
    (vr : VRel) (g : KW → KW) (F : CTy) (δ : LSub) (x : KW) :
    (tabGK (ℍ := ℍ) R G vr g F δ x).Twin (tabGK (ℍ := ℍ) R' G' vr g F δ x) := by
  intro m i en h
  obtain ⟨q, A, B, fin, -, rfl, hR⟩ := tab_lookupGGK F h
  exact ⟨_, hR R' G', rfl, rfl, rfl, rfl, rfl⟩

/-! ### The guarded twin with the frame -/

/-- **The guarded twin's cancel obligations with a frame beside the share, at the typed world**
(the premise `hcan` of `erwpK_frameGR`), by induction on how deep cancel rows
nest: at a capturable entry the cancel run at its cancel row's guarded table is framed
(`erwpK_frame_cancelRunGR`), its entries' order read at the run's share (`KW.Owed.left`), its own
nested cancel obligations by the induction. -/
theorem tabGK_canF {Δ : LifeCtx} {xv : LifeVar} {bnd : Lifetime.Life} {δ : LSub} (R : Nat → WProp)
    (G : ShareG)
    (Fr : WProp) :
    ∀ (d : Nat) (F : CTy), F.cdepth ≤ d → F.SuspendC Δ xv bnd → ∀ (vr : VRel) (x : KW)
      (m i : UInt32) (en en' : OpEntK KW), tabGK (ℍ := ℍ) R G vr id F δ x m i = some en →
      tabGK (ℍ := ℍ) (fun k => R k ⋆ Fr) (G.sep fun _ => Fr) vr id F δ x m i = some en' →
      en.abort = false → en.q ≠ .lin →
      ∀ f y k ls (K : Kont) (ρk ρ₂ ρk' : WRes), ResU.CompS ρk ρ₂ ρk' → ResU.Valid ρk' → Fr ρ₂ →
        en'.wk f y ρk' → cancelOKK en y k ls K ρk → cancelOKK en' y k ls K ρk' := by
  intro d
  induction d with
  | zero =>
      intro F hd hF vr x m i en en' h
      obtain ⟨q, A, B, fin, hL, -, -⟩ := tab_lookupGGK F h
      exact absurd (layer_cdepth F hL) (by omega)
  | succ d ih =>
  intro F hd hFs vr x m i en en' h h' ha hql f y k ls K ρk ρ₂ ρk' hc _ hFr _ hcn
  obtain ⟨q, A, B, fin, hL, rfl, hR⟩ := tab_lookupGGK F h
  rw [hR _ _] at h'
  cases Option.some.inj h'
  have hcap : capB q B = true := by
    simp only [entNK] at ha hql
    simp only [capB, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_eq_eq_not, Bool.not_true]
    refine ⟨hql, ?_⟩
    cases hB : B.isZero
    · rfl
    · simp [hB, hql] at ha
  have hfin := (layer_suspend F hFs hL).2.2.2.2.2 hcap
  have hfd : fin.cdepth ≤ d := by have := layer_cdepth F hL; omega
  intro P' hP'
  simp only [entNK, hcap, if_true] at hP' hcn
  by_cases htop : fin = .top
  · subst htop; simp [finGK] at hP'
  rw [finGK_eq _ _ _ _ htop] at hP'
  cases Option.some.inj hP'
  have hin := hcn _ (finGK_eq _ _ _ _ htop _)
  refine erwpK_frame_cancelRunGR (ℍ := ℍ) (V := KW.PostK)
    (Φ := fun z => (id z : KW).Θ.view (id z : KW).c) (fl := fun z => (id z : KW).lo)
    (T₁ := fun z => tabGK (ℍ := ℍ) R G vr id fin δ z)
    (T₂ := fun z => tabGK (ℍ := ℍ) (fun k => R k ⋆ Fr) (G.sep fun _ => Fr) vr id
      fin δ z)
    (fun z => tabGK_tabGK_twin _ _ _ _ _ _ fin δ z) (tabGK_afok hfin _ _ _ _ δ) Fr ?_
    (fun z => ih fin hfd hfin _ z) k y ls _ ρk ρ₂ ρk' hc hFr hin
  intro z m' i' e₁ e₂ h₁ h₂ _ f' y' σk σ₂ σk' hcσ hvσ _ hy'
  obtain ⟨_, _, _, _, _, rfl, hR₁⟩ := tab_lookupGGK fin h₁
  rw [hR₁] at h₂
  cases Option.some.inj h₂
  exact KW.Owed.left hcσ hvσ hy'

/-- **The frame at the guarded twin, at the typed tables** (`erwp_frameGR` at `KW`, the field
reborrow's frame of `ℓ ↦ own(loc ℓ₂)` outside the Mut Frame at the field). Every premise of
`erwpK_frameGR` is read off the tables: the twin (`tabGK_tabGK_twin`), the entries' shape
(`tabGK_afok`), the order at the run's share (`KW.Owed.left`) and the cancel transfer
(`tabGK_canF`). -/
theorem erwpK_frameGR_tab {V : KW → KW → Prop} {Φ : KW → LocFam} {Δ : LifeCtx} {xv : LifeVar}
    {bnd : Lifetime.Life} {F : CTy} (hF : F.SuspendC Δ xv bnd) (vr : VRel) (δ : LSub)
    (R : Nat → WProp) (G : ShareG) {Q : KW → PostN} (Fr : WProp) :
    ∀ n x ls e (ρ₁ ρ₂ ρ : WRes), ResU.CompS ρ₁ ρ₂ ρ → Fr ρ₂ →
      erwpK (ℍ := ℍ) V Φ (fun z => opTableGRK z.lo (tabGK (ℍ := ℍ) R G vr id F δ z) G R) Q
        x n ls e ρ₁ →
      erwpK (ℍ := ℍ) V Φ (fun z => opTableGRK z.lo
        (tabGK (ℍ := ℍ) (fun k => R k ⋆ Fr) (G.sep fun _ => Fr) vr id F δ z)
        (G.sep fun _ => Fr) (fun k => R k ⋆ Fr)) (fun y k ls' v => Q y k ls' v ⋆ Fr)
        x n ls e ρ := by
  refine erwpK_frameGR (ℍ := ℍ) (fl := fun z => z.lo)
    (fun z => tabGK_tabGK_twin _ _ _ _ _ _ F δ z) (tabGK_afok hF _ _ _ _ δ) Fr ?_
    (fun z => tabGK_canF R G Fr _ F le_rfl hF vr z)
  intro z m' i' e₁ e₂ h₁ h₂ _ f' y' σk σ₂ σk' hcσ hvσ _ hy'
  obtain ⟨_, _, _, _, _, rfl, hR₁⟩ := tab_lookupGGK F h₁
  rw [hR₁] at h₂
  cases Option.some.inj h₂
  exact KW.Owed.left hcσ hvσ hy'

/-! ### An entry's order at a row's table -/

/-- **An entry's order at a part of a valid share, at a row's table**. -/
theorem tabNK_wkLeft {vr : VRel} (F : CTy) (δ : LSub) :
    ∀ x m i en, tabNK (ℍ := ℍ) vr id F δ x m i = some en → ∀ f y (ρ₁ ρ₂ ρ : WRes),
      ResU.CompS ρ₁ ρ₂ ρ → ResU.Valid ρ → en.wk f y ρ → en.wk f y ρ₁ := by
  intro x m i en h f y ρ₁ ρ₂ ρ hc hv hy
  obtain ⟨_, _, _, _, _, rfl, -⟩ := tab_lookupNNK F h
  exact KW.Owed.left hc hv hy

/-- **Every world an entry of a row's table owes its continuation at has a valid location
typing**. -/
theorem tabNK_wkOK {vr : VRel} (F : CTy) (δ : LSub) :
    ∀ x m i en, tabNK (ℍ := ℍ) vr id F δ x m i = some en → ∀ f y ρ, en.wk f y ρ → y.Θ.OK := by
  intro x m i en h f y ρ hy
  obtain ⟨_, _, _, _, _, rfl, -⟩ := tab_lookupNNK F h
  exact hy.2.1

/-! ### The abortive payload across a finaliser's stops -/

/-- **An abortive entry's payload is one at every world a stop at the same table owes its
continuation at**, at a part of the stop's share (the premise `hTk` of `erwpK_ubindRaiseF` at the
typed tables): the stop's order is `ExtR` at its share, so at the part (`LocTy.ExtR.left`), along
which the value relation is kept (`ValRelOK.extR`). -/
theorem tabNK_raiseOwed {vr : VRel} (hv : ValRelOK vr) (F : CTy) (δ : LSub) :
    ∀ x m' i' en', tabNK (ℍ := ℍ) vr id F δ x m' i' = some en' → en'.abort = false →
      ∀ f y (ρa ρb ρ : WRes), ResU.CompS ρa ρb ρ → en'.wk f y ρ →
      ∀ m i en, tabNK (ℍ := ℍ) vr id F δ x m i = some en → en.abort = true →
      ∃ en'', tabNK (ℍ := ℍ) vr id F δ y m i = some en'' ∧ en''.abort = true ∧
        ∀ k ls v, en.PA k ls v ρa → en''.PA k ls v ρa := by
  intro x m' i' en' h' _ f y ρa ρb ρ hc hy m i en h ha
  obtain ⟨_, _, _, _, _, rfl, -⟩ := tab_lookupNNK F h'
  have hE : x.Θ.ExtR y.Θ ρa := hy.1.extR.left hc
  obtain ⟨q, A, B, fin, -, rfl, hR⟩ := tab_lookupNNK F h
  exact ⟨_, hR id y, ha, fun k ls v hp => hv.extR A δ k v ρa hE hp⟩

/-- **The finaliser's raise along the post order at the typed tables** (the premise `hTVr` of
`erwpK_ubindRaiseF`): a post's world is the run's own. -/
theorem tabNK_raisePost {vr : VRel} (F : CTy) (δ : LSub) :
    ∀ x y, KW.PostK x y → ∀ m i en, tabNK (ℍ := ℍ) vr id F δ x m i = some en → en.abort = true →
      ∃ en'', tabNK (ℍ := ℍ) vr id F δ y m i = some en'' ∧ en''.abort = true ∧
        ∀ k ls v ρ, en.PA k ls v ρ → en''.PA k ls v ρ := by
  rintro x y rfl m i en h ha
  exact ⟨en, h, ha, fun _ _ _ _ h => h⟩

end BoCa.Fig16.LogRel.Core.Chain.SI

end
