import ProbeD1.NxAllI

/-!
# ProbeD1 — `MonoHide` at `vRLM`, and statement 4's transports (`NEXT.md` item 4)

* **Hiding, where it is invisible.** `hideInvisible`: hiding names no entry's row holds leaves the
  stack as it is. So `[handle]`'s context transport is the identity where the handled name crosses
  no entry (`monoHideGMHandle0_noCross`), and so is `AllRMono`'s hiding half
  (`allRHideM0_noCross`). Both programs' handlers are of this kind: `reconB′`'s callback row is
  `{wait}`, and `retry` hides `exn`, which no lender of theirs crosses.
* **`AllRMono`'s record-order half** (`allRExtM0`): `monoExtM0` at each instance of the
  intersection.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace ProbeD1
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open GhostEnd (LEnt LStack LKind extS vwE vwS vis stratS ReLend TabAtS jdgCty)

/-! ### Hiding where it is invisible -/

/-- **`HideInvisible`**: an entry whose row holds none of the names keeps its row. -/
theorem hideInvisible : HideInvisible := by
  intro N σ h
  induction σ with
  | nil => rfl
  | cons e σ ih =>
      show { e with cross := fun n => e.cross n && !N n } :: hideS N σ = e :: σ
      rw [ih (fun e' he' => h e' (List.mem_cons_of_mem _ he'))]
      congr 1
      cases e with
      | mk l x T k cr =>
          simp only [LEnt.mk.injEq, true_and]
          funext n
          cases hn : N n with
          | false => simp
          | true =>
              have := h ⟨l, x, T, k, cr⟩ List.mem_cons_self n hn
              simp only at this
              simp [this]

/-- **`[handle]`'s context transport where the handled name crosses no entry**: the identity. -/
theorem monoHideGMHandle0_noCross {σ : LStack} {δ : LSub} {Γ : Ctx VTy} {γ : List Val}
    {αs : List Life} {ls : List SRec} {ρ : WRes} {n : UInt32}
    (hn : ∀ e ∈ σ, e.cross n = false) (hg : gRLM (ℍ := ℍ) .binder0 σ δ αs ls Γ γ ρ) :
    gRLM (ℍ := ℍ) .binder0 (hideS (· == n) σ) δ αs ls Γ γ ρ := by
  rw [hideInvisible (· == n) σ (fun e he m hm => by
    obtain rfl : m = n := by simpa using hm
    exact hn e he)]
  exact hg

/-- **`AllRMono`'s hiding half where the hidden names cross no entry**: the identity. -/
theorem allRHideM0_noCross {σ : LStack} {δ : LSub} {αs : List Life} {ls : List SRec}
    {ρv : Targets.RVar} {k : Targets.RowCon} {C : Targets.Inst.OCTy} {η : Targets.RowEnv}
    {v : Val} {r : WRes} {N : UInt32 → Bool} (hN : ∀ e ∈ σ, ∀ n, N n = true → e.cross n = false)
    (h : ovalWM (ℍ := ℍ) .binder0 σ δ αs ls (.thunk (.allR ρv k C)) η v r) :
    ovalWM (ℍ := ℍ) .binder0 (hideS N σ) δ αs ls (.thunk (.allR ρv k C)) η v r := by
  rw [hideInvisible N σ hN]
  exact h

/-! ### `AllRMono`'s record-order half -/

/-- **The intersection carried along the record order**, instance by instance (`monoExtM0`). -/
theorem ovalUM_ext {σ : LStack} {δ : LSub} {αs : List Life} {ls ls' : List SRec} {r : WRes}
    (hok : StackOK σ αs) (hob : OuterBelowTop αs) (hro : RecsOutside αs ls)
    (hro' : RecsOutside αs ls') (he : Ext ls ls' r) (hk : KeepsT ls ls' r) (ht : TabAtS σ αs r)
    (hpv : PlaceViewsL (extS δ σ αs) σ αs ls r) :
    ∀ (C : Targets.Inst.OCTy) (η : Targets.RowEnv) (v : Val),
      ovalUM (ℍ := ℍ) .binder0 σ δ αs ls C η v r → ovalUM (ℍ := ℍ) .binder0 σ δ αs ls' C η v r
  | .allR ρ _ C, η, v => fun h s hs ho =>
      ovalUM_ext hok hob hro hro' he hk ht hpv C (Function.update η ρ s) v (h s hs ho)
  | .ret _, _, v => fun h => monoExtM0 σ δ _ αs ls ls' v r hok hob hro hro' he hk ht hpv h
  | .arr _ _, _, v => fun h => monoExtM0 σ δ _ αs ls ls' v r hok hob hro hro' he hk ht hpv h
  | .amp _ _, _, v => fun h => monoExtM0 σ δ _ αs ls ls' v r hok hob hro hro' he hk ht hpv h
  | .top, _, v => fun h => monoExtM0 σ δ _ αs ls ls' v r hok hob hro hro' he hk ht hpv h
  | .all _ _ _, _, v => fun h => monoExtM0 σ δ _ αs ls ls' v r hok hob hro hro' he hk ht hpv h
  | .nu _, _, v => fun h => monoExtM0 σ δ _ αs ls ls' v r hok hob hro hro' he hk ht hpv h
  | .eff _ _ _ _ _ _, _, v => fun h =>
      monoExtM0 σ δ _ αs ls ls' v r hok hob hro hro' he hk ht hpv h
  | .effF _ _, _, v => fun h => monoExtM0 σ δ _ αs ls ls' v r hok hob hro hro' he hk ht hpv h

/-- **`AllRExtM0`**: `AllRMono`'s record-order half at `vRLM .binder0`. -/
theorem allRExtM0 : AllRExtM0 (ℍ := ℍ) :=
  fun _ _ _ _ _ ρv k C η v _ hok hob hro hro' he hk ht hpv h =>
    ovalUM_ext hok hob hro hro' he hk ht hpv (.allR ρv k C) η v h

/-! ### `AllRMono`'s thaw half at the empty resource -/

/-- **The views of a stack at the empty resource are off**, so they are at every reading, every
vector of lifetimes of the same length and every list. -/
theorem vwSW_empty_all {s s' : LSub} : ∀ {seen : List BoCa.Loc} {σ : LStack} {ds : List Bool}
    {αs αs' : List Life} {ls ls' : List SRec}, αs'.length = αs.length →
    vwSW s seen σ ds αs ls PMap.empty → vwSW s' seen σ ds αs' ls' PMap.empty
  | _, [], [], [], [], _, _, _, h => h
  | seen, e :: σ, d :: ds, α :: αs, α' :: αs', ls, ls', hl, ⟨a, r, hc, ha, hr⟩ => by
      have ha0 := eq_empty_of_compS_left hc
      have hr0 := eq_empty_of_compS_right hc
      subst ha0 hr0
      refine ⟨PMap.empty, PMap.empty, hc, ?_, vwSW_empty_all (by simpa using hl) hr⟩
      cases hvis : vis seen e d
      · exact vwEW_off s' e α' ls'
      · rw [hvis] at ha
        obtain ⟨ψ, hψ, -⟩ := vwE_single ha.1
        have := congrArg (fun r => PMap.get r e.l) hψ
        simp at this
  | _, [], [], [], _ :: _, _, _, hl, _ => by simp at hl
  | _, [], [], _ :: _, _, _, _, _, h => by simp only [vwSW] at h
  | _, [], _ :: _, _, _, _, _, _, h => by simp only [vwSW] at h
  | _, _ :: _, [], _, _, _, _, _, h => by simp only [vwSW] at h
  | _, _ :: _, _ :: _, [], _, _, _, _, h => by simp only [vwSW] at h
  | _, _ :: _, _ :: _, _ :: _, [], _, _, hl, _ => by simp at hl

/-- **`RelendJInter` at the empty resource**: nothing is retained or dropped, so one split serves
every member of the family, its flags off, and the views each member is handed are empty. -/
theorem relendJInter_empty {I : Type} {P : I → LSub → List Life → List SRec → WProp}
    {δ : LSub} {σ : LStack} {αs : List Life} {ls : List SRec} (hl : αs.length = σ.length)
    (h : ∀ i, RelendJ δ σ (P i) αs ls PMap.empty) :
    RelendJ δ σ (fun δ' αs' ls' ρ' => ∀ i, P i δ' αs' ls' ρ') αs ls PMap.empty := by
  refine ⟨σ.map (fun _ => false), PMap.empty, PMap.empty, ResU.comp_empty_right _,
    ⟨vwSW_false hl, placeViewsL_empty⟩, stratS_empty αs,
    fun ι hι ls' he hkt hks hro ρv τ hv hc i => ?_⟩
  have hv0 := vwSW_false_inv hv.1
  subst hv0
  have hτ : τ = PMap.empty := by
    have := ResU.CompS.functional hc (ResU.comp_empty_right PMap.empty)
    exact this
  subst hτ
  obtain ⟨ds, ρz, ρn, hc', hn, -, H⟩ := h i
  have hz0 := eq_empty_of_compS_left hc'
  have hn0 := eq_empty_of_compS_right hc'
  subst hz0 hn0
  exact H ι hι ls' he hkt hks hro PMap.empty PMap.empty
    ⟨vwSW_empty_all (by simp [Inst.life]) hn.1, placeViewsL_empty⟩ (ResU.comp_empty_right _)

/-- **The intersection thaws at the empty resource**, instance by instance (`relendMValue`), the
instances joined by `relendJInter_empty`. -/
theorem ovalUM_thaw_empty {σ : LStack} {δ : LSub} {αs : List Life} {ls : List SRec}
    (hok : StackOK σ αs) (hob : OuterBelowTop αs) (hro : RecsOutside αs ls) :
    ∀ (C : Targets.Inst.OCTy) (η : Targets.RowEnv) (v : Val),
      ovalUM (ℍ := ℍ) .binder0 σ δ αs ls C η v PMap.empty →
      RelendJ δ σ (fun δ' αs' ls' => ovalUM (ℍ := ℍ) .binder0 σ δ' αs' ls' C η v) αs ls
        PMap.empty
  | .allR ρ k C, η, v => fun h => by
      have hI := relendJInter_empty (I := {s : Row // k.cls.Admits s ∧ ∀ o ∈ s, k.adm o})
        (P := fun s δ' αs' ls' => ovalUM (ℍ := ℍ) .binder0 σ δ' αs' ls' C
          (Function.update η ρ s.1) v) (δ := δ) (ls := ls) hok.1
        (fun s => ovalUM_thaw_empty hok hob hro C _ v (h s.1 s.2.1 s.2.2))
      exact relendJ_mono (fun δ' αs' ls' ρ' hP s hs ho => hP ⟨s, hs, ho⟩) hI
  | .ret _, _, v => fun h => relendMValue _ δ σ αs ls v _ hok hob hro (tab_empty σ αs)
      placeViewsL_empty h
  | .arr _ _, _, v => fun h => relendMValue _ δ σ αs ls v _ hok hob hro (tab_empty σ αs)
      placeViewsL_empty h
  | .amp _ _, _, v => fun h => relendMValue _ δ σ αs ls v _ hok hob hro (tab_empty σ αs)
      placeViewsL_empty h
  | .top, _, v => fun h => relendMValue _ δ σ αs ls v _ hok hob hro (tab_empty σ αs)
      placeViewsL_empty h
  | .all _ _ _, _, v => fun h => relendMValue _ δ σ αs ls v _ hok hob hro (tab_empty σ αs)
      placeViewsL_empty h
  | .nu _, _, v => fun h => relendMValue _ δ σ αs ls v _ hok hob hro (tab_empty σ αs)
      placeViewsL_empty h
  | .eff _ _ _ _ _ _, _, v => fun h => relendMValue _ δ σ αs ls v _ hok hob hro (tab_empty σ αs)
      placeViewsL_empty h
  | .effF _ _, _, v => fun h => relendMValue _ δ σ αs ls v _ hok hob hro (tab_empty σ αs)
      placeViewsL_empty h

/-- **`AllRThawM0` at the empty resource**: the thaw half where the slot holds nothing, as
`retryR`'s `!U(∀ρ. …)` slot does. -/
def AllRThawM0Empty : Prop :=
  ∀ (σ : LStack) (δ : LSub) (αs : List Life) (ls : List SRec) (ρv : Targets.RVar)
    (k : Targets.RowCon) (C : Targets.Inst.OCTy) (η : Targets.RowEnv) (v : Val),
    StackOK σ αs → OuterBelowTop αs → RecsOutside αs ls →
    ovalWM (ℍ := ℍ) .binder0 σ δ αs ls (.thunk (.allR ρv k C)) η v PMap.empty →
    RelendJ δ σ
      (fun δ' αs' ls' => ovalWM (ℍ := ℍ) .binder0 σ δ' αs' ls' (.thunk (.allR ρv k C)) η v)
      αs ls PMap.empty

theorem allRThawM0Empty : AllRThawM0Empty (ℍ := ℍ) :=
  fun _ _ _ _ ρv k C η v hok hob hro h => ovalUM_thaw_empty hok hob hro (.allR ρv k C) η v h

end ProbeD1

end
