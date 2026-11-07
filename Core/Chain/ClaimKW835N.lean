import Core.Chain.ReindexK835N
import Core.Chain.FrameListKW835N
import Core.Chain.ThenKW835N

/-!
# The lend's claim at the typed world  `[spec §62]`

`docs/new-core/scope-835-tables.md` §10.11. `Cancel791N`'s claim machinery at `KW`:

* `tabRWK`/`finRWK`: the lender's twin with a claim read at a world: `tabRK`'s entries, every
  capturable one's cancel run at its cancel row's own table, its cancel's `raise` carrying the claim
  at the world it is raised at;
* `erwpK_claimXK`, `erwpK_cancelRun_claimXK`: the lender's run carries the view's consistency to its
  claim (`erwp_claimX`, `erwp_cancelRun_claimX`). At a world the run is read at the view of that
  world: a run from a resource consistent with the view returns consistent resources
  (`rwpG_consistentXV`); a stop's continuation is resumed from its share, consistent with the
  resumption world's view (`KW.Owed`), and an answer, consistent with it by the entry's answer; a
  cancellable stop's cancel run is one at its cancel row's table, by induction on how deep cancel
  rows nest;
* `tabRWK_ubindCan`: the finaliser frame over the lender's cancel runs (`erwp_ubind_cancelRunCR` at
  `KW`): a cancellable stop's cancel run at `tabRWK` under `ubind (N, D)` is one at `tabNK`, by
  `erwpK_ubind_cancelRunCRI` and induction on how deep cancel rows nest;
* `erwpK_ubindClaimRWK`: the finaliser frame around the lender's body (`erwp_ubindClaimRT` at
  `KW`), by `erwpK_ubindClaimRTI`.

Each is read at the worlds an invariant `Inv` holds at, which every world a stop at a floor no
higher than the run's own owes its continuation at keeps (`hInvW`).
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
open BoCa.BoLo (Heap Kont performE raiseE cancelVal opPayload ubindE)

/-! ### The lender's twin with a claim read at a world -/

/-- **The cancel run ending at a claim read at a world** (`cancelOblRK` at `g = id`, the claim
`R z` at the world `z` the cancel's `raise` is at). -/
def cancelOblRWK (T : KW → OpTabK KW) (R : KW → Nat → WProp) :
    KW → Nat → List SRec → Expr → WProp :=
  fun y k ls e => erwpK (ℍ := ℍ) KW.PostK (fun z => z.Θ.view z.c)
    (fun z => cancelTabRK z.lo (T z) (R z)) (fun _ _ _ _ _ => False) y k ls e

mutual
/-- **The lender's table with a claim read at a world** (`tabRK` at `g = id`): every capturable
entry's cancel run ends at the claim of the world its `raise` is at. -/
def tabRWK (R : KW → Nat → WProp) (vr : VRel) : CTy → LSub → KW → OpTabK KW
  | .eff m i q A B fin _ C, δ, x => extTabK m i
      (entNK q B (fun k v ρ => vr A δ x.Θ k v ρ)
        (fun y k v ρ => vr B δ y.Θ k v ρ ∧ ConsistentX y.c ρ)
        (finRWK R vr fin δ) (fun f y ρ => x.Owed f y ρ))
      (tabRWK R vr C δ x)
  | _, _, _ => OpTabK.empty
/-- The lender's cancel obligation with a claim read at a world (`finRK`). -/
def finRWK (R : KW → Nat → WProp) (vr : VRel) : CTy → LSub →
    Option (KW → Nat → List SRec → Expr → WProp)
  | .top, _ => none
  | .eff m i q A B fin _ C, δ => some (cancelOblRWK (ℍ := ℍ) (fun x => extTabK m i
      (entNK q B (fun k v ρ => vr A δ x.Θ k v ρ)
        (fun y k v ρ => vr B δ y.Θ k v ρ ∧ ConsistentX y.c ρ)
        (finRWK R vr fin δ) (fun f y ρ => x.Owed f y ρ))
      (tabRWK R vr C δ x)) R)
  | .ret _, _ => some (cancelOblRWK (ℍ := ℍ) (fun _ => OpTabK.empty) R)
  | .arr _ _, _ => some (cancelOblRWK (ℍ := ℍ) (fun _ => OpTabK.empty) R)
  | .amp _ _, _ => some (cancelOblRWK (ℍ := ℍ) (fun _ => OpTabK.empty) R)
  | .all _ _ _, _ => some (cancelOblRWK (ℍ := ℍ) (fun _ => OpTabK.empty) R)
  | .nu _, _ => some (cancelOblRWK (ℍ := ℍ) (fun _ => OpTabK.empty) R)
end

theorem finRWK_eq (R : KW → Nat → WProp) (vr : VRel) {F : CTy} (hF : F ≠ .top) (δ : LSub) :
    finRWK (ℍ := ℍ) R vr F δ =
      some (cancelOblRWK (ℍ := ℍ) (fun x => tabRWK (ℍ := ℍ) R vr F δ x) R) := by
  cases F <;> simp_all [finRWK, tabRWK]

/-- **An entry of `tabRK` at `g = id` is a layer's, and every `tabRWK` has the layer's entry at the
same key.** -/
theorem tab_lookupRK_RW : ∀ (F : CTy) {R : Nat → WProp} {vr : VRel} {δ : LSub} {x : KW}
    {m j : UInt32} {en : OpEntK KW},
    tabRK (ℍ := ℍ) R vr id F δ x m j = some en → ∃ q A B fin, F.LayerOf q A B fin ∧
      en = entNK q B (fun k v ρ => vr A δ x.Θ k v ρ)
        (fun y k v ρ => vr B δ y.Θ k v ρ ∧ ConsistentX y.c ρ)
        (finRK (ℍ := ℍ) R vr id fin δ) (fun f y ρ => x.Owed f y ρ) ∧
      ∀ RW : KW → Nat → WProp, tabRWK (ℍ := ℍ) RW vr F δ x m j =
        some (entNK q B (fun k v ρ => vr A δ x.Θ k v ρ)
          (fun y k v ρ => vr B δ y.Θ k v ρ ∧ ConsistentX y.c ρ)
          (finRWK (ℍ := ℍ) RW vr fin δ) (fun f y ρ => x.Owed f y ρ))
  | .eff m₀ i₀ q A B fin rc C, R, vr, δ, x, m, j, en, h => by
      simp only [tabRK] at h
      unfold extTabK at h
      split at h
      · rename_i hmj
        cases Option.some.inj h
        obtain ⟨rfl, rfl⟩ := hmj
        exact ⟨q, A, B, fin, .inl ⟨rfl, rfl, rfl, rfl⟩, rfl, fun RW => by
          simp only [tabRWK, extTabK, and_self, if_true]⟩
      · rename_i hmj
        obtain ⟨q', A', B', fin', hL, he, hR⟩ := tab_lookupRK_RW C h
        exact ⟨q', A', B', fin', .inr hL, he, fun RW => by
          simp only [tabRWK, extTabK, if_neg hmj]; exact hR RW⟩
  | .ret _, _, _, _, _, _, _, _, h => by simp [tabRK, OpTabK.empty] at h
  | .arr _ _, _, _, _, _, _, _, _, h => by simp [tabRK, OpTabK.empty] at h
  | .amp _ _, _, _, _, _, _, _, _, h => by simp [tabRK, OpTabK.empty] at h
  | .top, _, _, _, _, _, _, _, h => by simp [tabRK, OpTabK.empty] at h
  | .all _ _ _, _, _, _, _, _, _, _, h => by simp [tabRK, OpTabK.empty] at h
  | .nu _, _, _, _, _, _, _, _, h => by simp [tabRK, OpTabK.empty] at h

/-- **An entry of `tabRWK` is a layer's, and `tabNK` at `g = id` has the layer's entry at the same
key.** -/
theorem tab_lookupRWK : ∀ (F : CTy) {RW : KW → Nat → WProp} {vr : VRel} {δ : LSub} {x : KW}
    {m j : UInt32} {en : OpEntK KW},
    tabRWK (ℍ := ℍ) RW vr F δ x m j = some en → ∃ q A B fin, F.LayerOf q A B fin ∧
      en = entNK q B (fun k v ρ => vr A δ x.Θ k v ρ)
        (fun y k v ρ => vr B δ y.Θ k v ρ ∧ ConsistentX y.c ρ)
        (finRWK (ℍ := ℍ) RW vr fin δ) (fun f y ρ => x.Owed f y ρ) ∧
      tabNK (ℍ := ℍ) vr id F δ x m j =
        some (entNK q B (fun k v ρ => vr A δ x.Θ k v ρ)
          (fun y k v ρ => vr B δ y.Θ k v ρ ∧ ConsistentX y.c ρ)
          (finNK (ℍ := ℍ) vr id fin δ) (fun f y ρ => x.Owed f y ρ))
  | .eff m₀ i₀ q A B fin rc C, RW, vr, δ, x, m, j, en, h => by
      simp only [tabRWK] at h
      unfold extTabK at h
      split at h
      · rename_i hmj
        cases Option.some.inj h
        obtain ⟨rfl, rfl⟩ := hmj
        exact ⟨q, A, B, fin, .inl ⟨rfl, rfl, rfl, rfl⟩, rfl, by
          simp only [tabNK, extTabK, and_self, if_true]; rfl⟩
      · rename_i hmj
        obtain ⟨q', A', B', fin', hL, he, hN⟩ := tab_lookupRWK C h
        exact ⟨q', A', B', fin', .inr hL, he, by
          simp only [tabNK, extTabK, if_neg hmj]; exact hN⟩
  | .ret _, _, _, _, _, _, _, _, h => by simp [tabRWK, OpTabK.empty] at h
  | .arr _ _, _, _, _, _, _, _, _, h => by simp [tabRWK, OpTabK.empty] at h
  | .amp _ _, _, _, _, _, _, _, _, h => by simp [tabRWK, OpTabK.empty] at h
  | .top, _, _, _, _, _, _, _, h => by simp [tabRWK, OpTabK.empty] at h
  | .all _ _ _, _, _, _, _, _, _, _, h => by simp [tabRWK, OpTabK.empty] at h
  | .nu _, _, _, _, _, _, _, _, h => by simp [tabRWK, OpTabK.empty] at h

mutual
/-- **`tabRK` at `g = id` is `tabRWK` at a claim read alike at every world.** -/
theorem tabRK_id_eq (R : Nat → WProp) (vr : VRel) : ∀ (F : CTy) (δ : LSub) (x : KW),
    tabRK (ℍ := ℍ) R vr id F δ x = tabRWK (ℍ := ℍ) (fun _ => R) vr F δ x
  | .eff m i q A B fin _ C, δ, x => by
      simp only [tabRK, tabRWK]
      rw [finRK_id_eq R vr fin δ, tabRK_id_eq R vr C δ x]; rfl
  | .ret _, _, _ => by simp [tabRK, tabRWK]
  | .arr _ _, _, _ => by simp [tabRK, tabRWK]
  | .amp _ _, _, _ => by simp [tabRK, tabRWK]
  | .top, _, _ => by simp [tabRK, tabRWK]
  | .all _ _ _, _, _ => by simp [tabRK, tabRWK]
  | .nu _, _, _ => by simp [tabRK, tabRWK]
/-- `finRK` at `g = id` is `finRWK` at a claim read alike at every world. -/
theorem finRK_id_eq (R : Nat → WProp) (vr : VRel) : ∀ (F : CTy) (δ : LSub),
    finRK (ℍ := ℍ) R vr id F δ = finRWK (ℍ := ℍ) (fun _ => R) vr F δ
  | .eff m i q A B fin _ C, δ => by
      simp only [finRK, finRWK]
      have h2 : ∀ x, tabRK (ℍ := ℍ) R vr id C δ x = tabRWK (ℍ := ℍ) (fun _ => R) vr C δ x :=
        fun x => tabRK_id_eq R vr C δ x
      rw [finRK_id_eq R vr fin δ]; simp only [h2]; rfl
  | .ret _, _ => rfl
  | .arr _ _, _ => rfl
  | .amp _ _, _ => rfl
  | .top, _ => rfl
  | .all _ _ _, _ => rfl
  | .nu _, _ => rfl
end

/-- `tabRK` at `g = id` and `tabRWK` agree but for the cancel obligations. -/
theorem tabRK_tabRWK_twin (R : Nat → WProp) (RW : KW → Nat → WProp) (vr : VRel) (F : CTy)
    (δ : LSub) (x : KW) :
    (tabRK (ℍ := ℍ) R vr id F δ x).Twin (tabRWK (ℍ := ℍ) RW vr F δ x) := by
  intro m i en h
  obtain ⟨q, A, B, fin, -, rfl, hRW⟩ := tab_lookupRK_RW F h
  exact ⟨_, hRW RW, rfl, rfl, rfl, rfl, rfl⟩

/-- A capturable entry of the typed tables has a cancel obligation. -/
theorem entNK_capB {q : Qual} {B : VTy} {PA : Nat → Val → WRes → Prop}
    {PB : KW → Nat → Val → WRes → Prop} {fin : Option (KW → Nat → List SRec → Expr → WProp)}
    {wk : Life → KW → WRes → Prop} (ha : (entNK q B PA PB fin wk).abort = false)
    (hq : (entNK q B PA PB fin wk).q ≠ .lin) : capB q B = true := by
  simp only [entNK] at ha hq
  simp only [capB, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_eq_eq_not, Bool.not_true]
  refine ⟨hq, ?_⟩
  cases hB : B.isZero
  · rfl
  · simp [hB, hq] at ha

/-! ### The claim, consistent with the view of the world it is raised at -/

/-- **The claim, consistent with the view of a world.** The finaliser consumes the claim at the
world its `raise` is at, by `d`'s judgment, whose argument clause reads a view consistent with the
argument (`fin_claim₀`). -/
def claimXK (R : Nat → WProp) : KW → Nat → WProp :=
  fun z k ρ => R k ρ ∧ ConsistentX z.c ρ

/-- **A cancel run at the lender's twin carries the view's consistency to its claim, at the typed
world** (`erwp_cancelRun_claimX`). A run at a world, from a resource consistent with that world's
view, returns consistent resources (`rwpG_consistentXV`), so the claim a `raise` carries is
consistent with it; a stop's continuation is resumed at a world whose view is consistent with its
share (`KW.Owed`) and with the answer (the entry's answer); a cancellable stop's cancel run is one at
its cancel row's table, by the induction on how deep cancel rows nest. -/
theorem erwpK_cancelRun_claimXK {vr : VRel} {R : Nat → WProp} {δ : LSub} :
    ∀ (d : Nat) (F : CTy), F.cdepth ≤ d → ∀ n (y : KW) ls e ρ, ConsistentX y.c ρ →
      cancelOblRK (ℍ := ℍ) id (fun x => tabRK (ℍ := ℍ) R vr id F δ x) R y n ls e ρ →
      cancelOblRWK (ℍ := ℍ) (fun x => tabRWK (ℍ := ℍ) (claimXK R) vr F δ x) (claimXK R) y n ls e
        ρ := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ihd =>
  intro F hFd n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro y ls e ρ hc h
  unfold cancelOblRK at h
  unfold cancelOblRWK
  rw [erwpK_eq] at h ⊢
  refine rwpG_mono_le (fun k hk ls' t σ ht => ?_) (rwpG_consistentXV h hc)
  obtain ⟨ht, hcσ, hvσ⟩ := ht
  rcases ht with ⟨_, _, _, _, hf⟩ | ⟨K₁, m, i, v, en, hp⟩ | ⟨K', err, hp⟩
  · exact hf.elim
  · -- a stop: its continuation is resumed at a world consistent with its share and its answer
    obtain ⟨⟨hpt, hK₁, hT', ha⟩, ρa, ρk, hcak, hA, hu, f, hf, hcont⟩ := pure_sep_iff.mp hp
    obtain ⟨q, A, B, fin, hLy, rfl, hRW⟩ := tab_lookupRK_RW F hT'
    refine Or.inr (Or.inl ⟨K₁, m, i, v, _, pure_sep_mk ⟨hpt, hK₁, hRW (claimXK R), ha⟩
      ⟨ρa, ρk, hcak, hA, hu, f, hf, fun y' hy' ls'' he => ⟨fun k' hk' w τ₁ τ₂ hB hcτ => ?_,
        fun hql P hP => ?_⟩⟩⟩)
    · have hc' := (hcont y' hy' ls'' he).1 k' hk' w τ₁ τ₂ hB hcτ
      simp only [erwpCK, show k' < n by omega, if_true] at hc' ⊢
      have hy'' : y.Owed f y' ρk := hy'
      exact ih k' (by omega) y' _ _ _ (consistentX_compS hcτ hy''.2.2.1 hB.2) hc'
    · have hcap := entNK_capB ha hql
      have hy'' : y.Owed f y' ρk := hy'
      simp only [entNK, hcap, if_true] at hP
      by_cases htop : fin = .top
      · subst htop; simp [finRWK] at hP
      rw [finRWK_eq _ _ htop] at hP
      cases Option.some.inj hP
      have hin := (hcont y' hy' ls'' he).2 hql _
        (by simp only [entNK, hcap, if_true]; exact finRK_eq R vr id htop δ)
      have hfd := layer_cdepth F hLy
      exact ihd fin.cdepth (by omega) fin le_rfl k y' ls'' _ ρk hy''.2.2.1 hin
  · -- the cancel's `raise`: the claim is part of a consistent resource
    obtain ⟨hpure, y1, y2, hy, hy1, hR⟩ := pure_sep_iff.mp hp
    obtain ⟨τa, τb, hcab, herr, hnb⟩ := hy1
    exact Or.inr (Or.inr ⟨K', err, pure_sep_mk hpure ⟨y1, y2, hy,
      ⟨τa, τb, hcab, errOkK_twin (tabRK_tabRWK_twin R (claimXK R) vr F δ y) herr, hnb⟩, hR,
      consistentX_right hy hcσ hvσ⟩⟩)

/-- **A body at the lender's twin carries the view's consistency to its claim, at the typed
world** (`erwp_claimX`): as `erwpK_cancelRun_claimXK`, at a `raise` the claim beside the payload. -/
theorem erwpK_claimXK {vr : VRel} {R : Nat → WProp} {F : CTy} {δ : LSub} {Q : KW → PostN} :
    ∀ n (x : KW) ls e ρ, ConsistentX x.c ρ →
      erwpK (ℍ := ℍ) KW.PostK (fun z => z.Θ.view z.c)
        (fun z => opTableRK z.lo (tabRK (ℍ := ℍ) R vr id F δ z) R) Q x n ls e ρ →
      erwpK (ℍ := ℍ) KW.PostK (fun z => z.Θ.view z.c)
        (fun z => opTableRK z.lo (tabRWK (ℍ := ℍ) (claimXK R) vr F δ z) (claimXK R z)) Q x n ls e
        ρ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x ls e ρ hc h
  rw [erwpK_eq] at h ⊢
  refine rwpG_mono_le (fun k hk ls' t σ ht => ?_) (rwpG_consistentXV h hc)
  obtain ⟨ht, hcσ, hvσ⟩ := ht
  rcases ht with hv | ⟨K₁, m, i, v, en, hp⟩ | ⟨K₁, m, i, v, en, hp⟩
  · exact Or.inl hv
  · -- a stop: its continuation is resumed at a world consistent with its share and its answer
    obtain ⟨⟨hpt, hK₁, hT', ha⟩, ρa, ρk, hcak, hA, hu, f, hf, hcont⟩ := pure_sep_iff.mp hp
    obtain ⟨q, A, B, fin, hLy, rfl, hRW⟩ := tab_lookupRK_RW F hT'
    refine Or.inr (Or.inl ⟨K₁, m, i, v, _, pure_sep_mk ⟨hpt, hK₁, hRW (claimXK R), ha⟩
      ⟨ρa, ρk, hcak, hA, hu, f, hf, fun y' hy' ls'' he => ⟨fun k' hk' w τ₁ τ₂ hB hcτ => ?_,
        fun hql P hP => ?_⟩⟩⟩)
    · have hc' := (hcont y' hy' ls'' he).1 k' hk' w τ₁ τ₂ hB hcτ
      simp only [erwpCK, show k' < n by omega, if_true] at hc' ⊢
      have hy'' : x.Owed f y' ρk := hy'
      exact ih k' (by omega) y' _ _ _ (consistentX_compS hcτ hy''.2.2.1 hB.2) hc'
    · have hcap := entNK_capB ha hql
      have hy'' : x.Owed f y' ρk := hy'
      simp only [entNK, hcap, if_true] at hP
      by_cases htop : fin = .top
      · subst htop; simp [finRWK] at hP
      rw [finRWK_eq _ _ htop] at hP
      cases Option.some.inj hP
      have hin := (hcont y' hy' ls'' he).2 hql _
        (by simp only [entNK, hcap, if_true]; exact finRK_eq R vr id htop δ)
      exact erwpK_cancelRun_claimXK fin.cdepth fin le_rfl k y' ls'' _ ρk hy''.2.2.1 hin
  · -- a `raise`: the claim is part of a consistent resource
    obtain ⟨⟨hpt, hK₁, hT', hab⟩, σ₁, ρR, hcσR, hpa, hR⟩ := pure_sep_iff.mp hp
    obtain ⟨q, A, B, fin, -, rfl, hRW⟩ := tab_lookupRK_RW F hT'
    exact Or.inr (Or.inr ⟨K₁, m, i, v, _, pure_sep_mk ⟨hpt, hK₁, hRW (claimXK R), hab⟩
      ⟨σ₁, ρR, hcσR, hpa, hR, consistentX_right hcσR hcσ hvσ⟩⟩)

/-! ### The finaliser frame over the lender's cancel runs and around its body -/

/-- A value relation read lower. -/
theorem ValRelOK.le {vr : VRel} (hv : ValRelOK vr) {A : VTy} {δ : LSub} {Θ : LocTy} {k k' : Nat}
    (hk : k' ≤ k) {v : Val} {ρ : WRes} (h : vr A δ Θ k v ρ) : vr A δ Θ k' v ρ := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  clear hk
  induction j with
  | zero => exact h
  | succ j ih => exact ih (hv.down _ _ _ _ _ _ h)

/-- `tabRWK` and `tabNK` at `g = id` agree but for the cancel obligations, their orders included. -/
theorem tabRWK_tabNK_twin (RW : KW → Nat → WProp) (vr : VRel) (F : CTy) (δ : LSub) :
    ∀ (x : KW) m i en, tabRWK (ℍ := ℍ) RW vr F δ x m i = some en →
      ∃ en', tabNK (ℍ := ℍ) vr id F δ x m i = some en' ∧ en'.q = en.q ∧
        en'.abort = en.abort ∧ en'.PA = en.PA ∧ en'.PB = en.PB ∧ en'.wc = en.wc ∧
        en'.wk = en.wk := by
  intro x m i en h
  obtain ⟨q, A, B, fin, -, rfl, hN⟩ := tab_lookupRWK F h
  exact ⟨_, hN, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `tabNK`'s abortive payloads are read lower and at every list. -/
theorem tabNK_paLe {vr : VRel} (hv : ValRelOK vr) (F : CTy) (δ : LSub) :
    ∀ (x : KW) m i en, tabNK (ℍ := ℍ) vr id F δ x m i = some en → en.abort = true →
      ∀ k k' ls ls' v ρ, k' ≤ k → en.PA k ls v ρ → en.PA k' ls' v ρ := by
  intro x m i en h _ k k' ls ls' v ρ hk hPA
  obtain ⟨q, A, B, fin, -, rfl, -⟩ := tab_lookupNK F h
  exact hv.le hk hPA

/-- Every world an entry of `tabRWK` owes at, at a floor no higher than the run's, is one `Inv`
holds at, when `KW.Owed` keeps `Inv` at such floors. -/
theorem tabRWK_wkInv {RW : KW → Nat → WProp} {vr : VRel} {F : CTy} {δ : LSub} {Inv : KW → Prop}
    (hInvW : ∀ x : KW, Inv x → ∀ f, f ≤ x.lo → ∀ y ρ, x.Owed f y ρ → Inv y) :
    ∀ (x : KW), Inv x → ∀ m i en, tabRWK (ℍ := ℍ) RW vr F δ x m i = some en → en.abort = false →
      ∀ f, f ≤ x.lo → ∀ y ρ, en.wk f y ρ → Inv y := by
  intro x hx m i en h _ f hf y ρ hy
  obtain ⟨q, A, B, fin, -, rfl, -⟩ := tab_lookupRWK F h
  exact hInvW x hx f hf y ρ hy

/-- **The finaliser frame over the lender's cancel runs, at the typed world**
(`erwp_ubind_cancelRunCR` at `KW`, the premise `hcan` of `erwpK_ubindClaimRTI`): a cancellable
stop's cancel run at its cancel row's `tabRWK`, under `ubind (N, D)`, is one at its `tabNK`, at the
worlds `Inv` holds at. By `erwpK_ubind_cancelRunCRI` at the cancel row, its own cancellable stops by
the induction on how deep cancel rows nest. -/
theorem tabRWK_ubindCan {vr : VRel} (hv : ValRelOK vr) {RW : KW → Nat → WProp} {Inv : KW → Prop}
    (hΦ : ∀ x : KW, Inv x → (x.Θ.view x.c).Down)
    (hInvW : ∀ x : KW, Inv x → ∀ f, f ≤ x.lo → ∀ y ρ, x.Owed f y ρ → Inv y) {δ : LSub}
    (N D : Val)
    (hD : ∀ x : KW, Inv x → ∀ k ls ρ, RW x k ρ → rwp (ℍ := ℍ) (x.Θ.view x.c)
      (fun _ _ _ ρ' => ρ' = PMap.empty) k ls (.app (.val D) (.val .unit)) ρ) :
    ∀ (d : Nat) (F : CTy), F.cdepth ≤ d → ∀ (x : KW) m i en en',
      tabRWK (ℍ := ℍ) RW vr F δ x m i = some en → tabNK (ℍ := ℍ) vr id F δ x m i = some en' →
      en.q ≠ .lin → ∀ y, Inv y → ∀ k ls (K₁ : Kont) ρ, cancelOKK en y k ls K₁ ρ →
        cancelOKK en' y k ls ((ubK N D).comp K₁) ρ := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ihd =>
  intro F hFd x m i en en' h h' hql y hy k ls K₁ ρ hc P hP
  obtain ⟨q, A, B, fin, hLy, rfl, hN⟩ := tab_lookupRWK F h
  rw [hN] at h'
  cases Option.some.inj h'
  by_cases hcap : capB q B = true
  · simp only [entNK, hcap, if_true] at hP hc
    by_cases htop : fin = .top
    · subst htop; simp [finNK] at hP
    rw [finNK_eq _ _ htop] at hP
    cases Option.some.inj hP
    have hin := hc _ (finRWK_eq RW vr htop δ)
    have hfd := layer_cdepth F hLy
    show cancelOblK (ℍ := ℍ) id (fun x => tabNK (ℍ := ℍ) vr id fin δ x) y k ls
      (((ubK N D).comp K₁).dead.plug _) ρ
    rw [dead_comp, ubK_dead, Kont.plug_comp]
    exact erwpK_ubind_cancelRunCRI (ℍ := ℍ) (V := KW.PostK) (Φ := fun z : KW => z.Θ.view z.c)
      (Inv := Inv) (fl := fun z : KW => z.lo) (Ti := fun z => tabRWK (ℍ := ℍ) RW vr fin δ z)
      (To := fun z => tabNK (ℍ := ℍ) vr id fin δ z) (R := RW) hΦ
      (fun z _ => cancelTabK_downI (tabNK_downI hv id fin δ z)) (tabRWK_tabNK_twin RW vr fin δ)
      (tabNK_paLe hv fin δ) N D (tabRWK_wkInv hInvW)
      (fun z _ m' i' en₁ en₁' h₁ h₁' hq₁ y' hy' =>
        ihd fin.cdepth (by omega) fin le_rfl z m' i' en₁ en₁' h₁ h₁' hq₁ y' hy') hD k y hy ls _ ρ
      hin
  · simp [entNK, hcap] at hP

/-- **The finaliser frame around the lender's body, at the typed world** (`erwp_ubindClaimRT` at
`KW`): `erwpK_ubindClaimRTI` at `tabRWK`/`tabNK`, at the worlds `Inv` holds at, the lender's cancel
runs by `tabRWK_ubindCan`. -/
theorem erwpK_ubindClaimRWK {vr : VRel} (hv : ValRelOK vr) {RW : KW → Nat → WProp}
    {Inv : KW → Prop} (hΦ : ∀ x : KW, Inv x → (x.Θ.view x.c).Down)
    (hInvW : ∀ x : KW, Inv x → ∀ f, f ≤ x.lo → ∀ y ρ, x.Owed f y ρ → Inv y) {F : CTy} {δ : LSub}
    (hTr : ∀ (x : KW) m i en, tabNK (ℍ := ℍ) vr id F δ x m i = some en → en.abort = true → m ≠ 0)
    (N D : Val)
    (hD : ∀ x : KW, Inv x → ∀ k ls ρ, RW x k ρ → rwp (ℍ := ℍ) (x.Θ.view x.c)
      (fun _ _ v ρ' => v = Val.unit ∧ ρ' = PMap.empty) k ls (.app (.val D) (.val .unit)) ρ)
    {Qin Qout : KW → PostN} (hQout : ∀ y, (Qout y).Down)
    (hN : ∀ y : KW, Inv y → ∀ k ls (v : Val) ρ, Qin y k ls v ρ →
      erwpK (ℍ := ℍ) KW.PostK (fun z => z.Θ.view z.c)
        (fun z => opTableK z.lo (tabNK (ℍ := ℍ) vr id F δ z)) Qout y k ls
        (.app (.val N) (.val v)) ρ) :
    ∀ n (x : KW), Inv x → ∀ ls M ρ,
      erwpK (ℍ := ℍ) KW.PostK (fun z => z.Θ.view z.c)
        (fun z => opTableRK z.lo (tabRWK (ℍ := ℍ) RW vr F δ z) (RW z)) Qin x n ls M ρ →
      erwpK (ℍ := ℍ) KW.PostK (fun z => z.Θ.view z.c)
        (fun z => opTableK z.lo (tabNK (ℍ := ℍ) vr id F δ z)) Qout x n ls
        (ubindE (.pair N D) M) ρ :=
  erwpK_ubindClaimRTI (ℍ := ℍ) (V := KW.PostK) (fun _ _ _ h₁ h₂ => h₁.trans h₂)
    (Φ := fun z : KW => z.Θ.view z.c) (Inv := Inv) hΦ (fun _ _ h => by rw [h])
    (fun x y h hx => by rw [show y = x from h]; exact hx) (fl := fun z : KW => z.lo)
    (Ti := fun z => tabRWK (ℍ := ℍ) RW vr F δ z) (To := fun z => tabNK (ℍ := ℍ) vr id F δ z)
    (fun z _ => opTableK_downI (tabNK_downI hv id F δ z))
    (fun _ _ h => tabLe_postK (fun z : KW => opTableK z.lo (tabNK (ℍ := ℍ) vr id F δ z)) h)
    (tabRWK_tabNK_twin RW vr F δ) (tabNK_paLe hv F δ) hTr N D (tabRWK_wkInv hInvW)
    (fun z _ m i en en' h h' hq y hy => tabRWK_ubindCan hv hΦ hInvW N D
      (fun x hx k ls ρ hR => rwp_mono (fun _ _ _ _ h => h.2) (hD x hx k ls ρ hR)) F.cdepth F
      le_rfl z m i en en' h h' hq y hy) hD hQout hN

/-! ### A run at a lower floor -/

/-- **The world at the floor no higher than `a`**: the location typing and the view kept. -/
def KW.flr (a : Life) (x : KW) : KW := ⟨x.Θ, x.c, min x.lo a⟩

/-- `KW.Owed` at the lowered floors: the floor's order is kept by `min`. -/
theorem KW.Owed.flr {x y : KW} {f : Life} {ρ : WRes} (h : x.Owed f y ρ) (a : Life) :
    (x.flr a).Owed f (y.flr a) ρ :=
  ⟨h.1, h.2.1, h.2.2.1, min_le_min_right a h.2.2.2.1, h.2.2.2.2⟩

/-- A stop at a lower floor bound is a stop at a higher one. -/
theorem performStopK_floor_le {ι : Type} {lo lo' : Life} (hlo : lo ≤ lo') (T : OpTabK ι) (k : Nat)
    (ls : List SRec) (t : Expr) (Ψ : ContK ι) (ρ : WRes) (h : performStopK lo T k ls t Ψ ρ) :
    performStopK lo' T k ls t Ψ ρ := by
  obtain ⟨K, n, i, v, en, h⟩ := h
  obtain ⟨hp, ρa, ρk, hc, hA, hu, f, hf, hcont⟩ := pure_sep_iff.mp h
  exact ⟨K, n, i, v, en, pure_sep_mk hp ⟨ρa, ρk, hc, hA, hu, f, le_trans hf hlo, hcont⟩⟩

/-- `tabNK` at `g = id` at a world and at its lowered floor agree but for the order, whose
location typing and view are the same. -/
theorem tabNK_flr_twin {vr : VRel} (F : CTy) (δ : LSub) (a : Life) (y : KW) :
    (tabNK (ℍ := ℍ) vr id F δ (y.flr a)).Twin (tabNK (ℍ := ℍ) vr id F δ y) := by
  intro m i en h
  obtain ⟨q, A, B, fin, -, rfl, hR⟩ := tab_lookupNNK F h
  exact ⟨_, hR id y, rfl, rfl, rfl, rfl, rfl⟩

/-- **A stop at `tabNK` at the lowered floor's world is a stop at the world's own**
(`erwpK_comap`'s `hT` at `g = KW.flr a`): the payload and the answer are read at the same location
typing and view; a world the stop owes at is the lowered floor's image of one (`KW.Owed.flr`); a
cancel obligation moves by `erwpK_comap` again, by induction on how deep cancel rows nest. -/
theorem tabNK_flr_comap {vr : VRel} {δ : LSub} (a : Life) :
    ∀ (d : Nat) (F : CTy), F.cdepth ≤ d → ∀ (lo : Life) (y : KW) k ls t (Ψ Ψ' : ContK KW) ρ,
      (∀ y' k', k' < k → ∀ ls e ρ, Ψ (y'.flr a) k' ls e ρ → Ψ' y' k' ls e ρ) →
      performStopK lo (tabNK (ℍ := ℍ) vr id F δ (y.flr a)) k ls t Ψ ρ →
      performStopK lo (tabNK (ℍ := ℍ) vr id F δ y) k ls t Ψ' ρ := by
  intro d
  induction d with
  | zero =>
      intro F hd lo y k ls t Ψ Ψ' ρ _ h
      obtain ⟨K, n, i, v, en, h⟩ := h
      obtain ⟨⟨-, -, h₃, -⟩, -⟩ := pure_sep_iff.mp h
      obtain ⟨q, A, B, fin, hL, -, -⟩ := tab_lookupNNK F h₃
      exact absurd (layer_cdepth F hL) (by omega)
  | succ d ih =>
  intro F hd lo y k ls t Ψ Ψ' ρ hΨ h
  obtain ⟨K, n, i, v, en, h⟩ := h
  obtain ⟨⟨h₁, h₂, h₃, h₄⟩, ρa, ρk, hc, hA, hu, f, hf, hcont⟩ := pure_sep_iff.mp h
  obtain ⟨q, A, B, fin, hL, rfl, hR⟩ := tab_lookupNNK F h₃
  have hfd : fin.cdepth ≤ d := by have := layer_cdepth F hL; omega
  refine ⟨K, n, i, v, _, pure_sep_mk ⟨h₁, h₂, hR id y, h₄⟩
    ⟨ρa, ρk, hc, hA, hu, f, hf, fun y' hy' ls' he => ⟨fun k' hk' w σ₁ σ₂ hB hcσ => ?_,
      fun hq P hP => ?_⟩⟩⟩
  · have hy'' : y.Owed f y' ρk := hy'
    exact hΨ y' k' hk' _ _ _ ((hcont (y'.flr a) (hy''.flr a) ls' he).1 k' hk' w σ₁ σ₂ hB hcσ)
  · have hy'' : y.Owed f y' ρk := hy'
    simp only [entNK] at hP hq
    by_cases hcap : capB q B = true
    · rw [if_pos hcap] at hP
      by_cases htop : fin = .top
      · subst htop; simp [finNK] at hP
      rw [finNK_eq _ _ htop] at hP
      cases Option.some.inj hP
      have hs := (hcont (y'.flr a) (hy''.flr a) ls' he).2 hq _
        (by simp only [entNK, if_pos hcap]; exact finNK_eq _ _ htop _)
      refine erwpK_comap (ℍ := ℍ) (KW.flr a) (fun _ => True)
        (fun _ => rfl) (fun _ _ _ _ _ _ _ _ hq => hq.elim) ?_ k y' trivial ls' _ ρk hs
      intro z _ k₁ ls₁ t₁ Ψ₁ Ψ₁' ρ₁ hΨ₁ h₁
      rcases h₁ with h₁ | ⟨K₁, err, h₁⟩
      · exact Or.inl (performStopK_floor_le (min_le_left _ _) _ _ _ _ _ _
          (ih fin hfd _ z k₁ ls₁ t₁ Ψ₁ Ψ₁'
            ρ₁ (fun y'' k'' hk'' ls'' e'' ρ'' h => hΨ₁ y'' k'' hk'' trivial ls'' e'' ρ'' h) h₁))
      · obtain ⟨hK, hr⟩ := pure_sep_iff.mp h₁
        obtain ⟨τ₁, τ₂, hτ, he₁, hn⟩ := hr
        exact Or.inr ⟨K₁, err, pure_sep_mk hK
          ⟨τ₁, τ₂, hτ, errOkK_twin (tabNK_flr_twin fin δ a z) he₁, hn⟩⟩
    · rw [if_neg hcap] at hP; cases hP

/-- **A run at `tabNK` from the lowered floor's world is a run from the world** (`erwpK_comap` at
`g = KW.flr a`), its posts read alike at both. -/
theorem erwpK_flr {vr : VRel} {F : CTy} {δ : LSub} (a : Life) {Q : KW → PostN}
    (hQ : ∀ (x : KW) k ls v ρ, Q (x.flr a) k ls v ρ → Q x k ls v ρ) :
    ∀ n (x : KW) ls e ρ,
      erwpK (ℍ := ℍ) KW.PostK (fun z => z.Θ.view z.c)
        (fun z => opTableK z.lo (tabNK (ℍ := ℍ) vr id F δ z)) Q (x.flr a) n ls e ρ →
      erwpK (ℍ := ℍ) KW.PostK (fun z => z.Θ.view z.c)
        (fun z => opTableK z.lo (tabNK (ℍ := ℍ) vr id F δ z)) Q x n ls e ρ := by
  intro n x ls e ρ h
  refine erwpK_comap (ℍ := ℍ) (KW.flr a) (fun _ => True) (V' := KW.PostK)
    (Φ' := fun z => z.Θ.view z.c) (Tb' := fun z => opTableK z.lo (tabNK (ℍ := ℍ) vr id F δ z))
    (Q' := Q) (fun _ => rfl)
    (fun x _ y k ls v ρ hy hq => ⟨x, KW.postK_refl x, ?_⟩) ?_ n x trivial ls e ρ h
  · have hy' : y = x.flr a := hy
    subst hy'
    exact hQ x k ls v ρ hq
  · intro z _ k₁ ls₁ t₁ Ψ₁ Ψ₁' ρ₁ hΨ₁ h₁
    rcases h₁ with h₁ | ⟨K₁, m, j, w, en, h₁⟩
    · exact Or.inl (performStopK_floor_le (min_le_left _ _) _ _ _ _ _ _
        (tabNK_flr_comap a F.cdepth F le_rfl _ z k₁ ls₁ t₁ Ψ₁ Ψ₁' ρ₁
          (fun y'' k'' hk'' ls'' e'' ρ'' h => hΨ₁ y'' k'' hk'' trivial ls'' e'' ρ'' h) h₁))
    · obtain ⟨⟨hE, hK, hTe, ha⟩, hr⟩ := pure_sep_iff.mp h₁
      obtain ⟨en', h', -, hab, hPA, -⟩ := tabNK_flr_twin F δ a z m j en hTe
      obtain ⟨τ₁, τ₂, hτ, ⟨hPAτ, hnA⟩, hn⟩ := hr
      exact Or.inr ⟨K₁, m, j, w, en', pure_sep_mk ⟨hE, hK, h', hab ▸ ha⟩
        ⟨τ₁, τ₂, hτ, ⟨hPA ▸ hPAτ, hnA⟩, hn⟩⟩

end BoCa.Fig16.LogRel.Core.Chain.SI

end
