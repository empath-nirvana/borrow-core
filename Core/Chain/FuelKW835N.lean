import Core.Chain.HandleTKW835N
import Core.Chain.Fuel835N

/-!
# `div_fuel` at the typed world  `[spec §14]`

`Fuel835N`'s handler at `cN`: `fuel_totalN` at `erwpK` and `divFuel_compatN` at `SemJN`, each step
`fuel_totalN₀`'s, at the relation at `KW`.

* the handler's steps at `erwpK`: `κ`'s resumption under a frame (`erwpK_kappaC_resume_in`), a
  tick under a one-clause handler of `Div` (`erwpK_hnd_tick`), a tick answered *close* or *next*
  (`fuel_tick_zeroK`, `fuel_tick_succK`), each `Fuel835N`'s at a world;
* **`fuel_totalN`**: by induction on the index, the run started from a resource consistent with
  the view of a world whose location typing is `OK`. A tick is resumed at the stop's own world,
  which the tick's entry owes at every floor (`KW.owed_self`), the stop's share being consistent
  with that world's view (`rwpG_consistentXV`); an operation of `Σ` passes the handler with its
  frame, and the run goes on at each world the entry owes, consistent there (`KW.Owed`, the
  answer's reading); its cancel passes the plain frame (`entF_plain`).
* `divFuel_compatN`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Head Kont performE raiseE cancelVal opPayload hndE hndVal kappaC
  kappaCell kappaAt clauseAt freeE)

variable {ι : Type}

/-- **Resuming a `κ` that owns a cell, under a frame, at `erwpK`** (`erwp_kappaC_resume_in`). -/
theorem erwpK_kappaC_resume_in {V : ι → ι → Prop} {Φ : ι → LocFam} {Tb : ι → TableK ι}
    (hL : ∀ x, (Tb x).Local) {Q : ι → PostN} {x : ι} (hΦ : (Φ x).Down) (hTd : (Tb x).Down)
    (hQ : ∀ y, (Q y).Down) (K₀ : Kont) (hasCancel : Bool) (ℓ : Loc) (H : Val) (K : Kont)
    (w : Val) {k : Nat} {ls : List SRec} {ρ : WRes}
    (h : (ptoOwn ℓ Val.unit ⋆
      erwpK (ℍ := ℍ) V Φ Tb Q x (k - 1) ls (K₀.plug (hndE H (K.plug (.val w))))) ρ) :
    erwpK (ℍ := ℍ) V Φ Tb Q x k ls
      (K₀.plug (.app (.app (kappaC hasCancel ℓ H K) (.val (Val.inj₁ .unit))) (.val w))) ρ := by
  let K₁ : Kont := K₀.comp (.appL .hole w)
  have e₀ : ∀ y, K₀.plug (.app y (.val w)) = K₁.plug y := fun y => by
    simp only [K₁, Kont.plug_comp]; rfl
  rw [e₀]
  refine erwpK_det hΦ hTd hQ (fun μ => step1Only_plug (Head.beta μ _ _) rfl K₁) ?_
  refine erwpK_det hΦ hTd hQ (fun μ => step1Only_plug (Head.case₁ μ Val.unit _ _) rfl K₁) ?_
  refine erwpK_det hΦ hTd hQ (fun μ => step1Only_plug (Head.seq μ _) rfl K₁) ?_
  have e₁ : ∀ y, K₁.plug (.seq (freeE (.val (Val.loc ℓ))) y) =
      (K₁.comp (.seq .hole y)).plug (freeE (.val (Val.loc ℓ))) := fun y => by
    rw [Kont.plug_comp, Kont.plug_comp, Kont.plug_comp]; rfl
  show erwpK (ℍ := ℍ) V Φ Tb Q x k ls (K₁.plug (.seq (freeE (.val (Val.loc ℓ))) _)) ρ
  rw [e₁]
  refine erwpK_free hL hΦ _ ℓ Val.unit ?_
  obtain ⟨ρ₁, ρ₂, hc, hp, hq⟩ := h
  refine ⟨ρ₁, ρ₂, hc, hp, ?_⟩
  rw [Kont.plug_comp]
  refine erwpK_det hΦ hTd hQ (fun μ => step1Only_plug (Head.seq μ _) rfl K₁) ?_
  rw [← e₀]
  refine erwpK_det hΦ hTd hQ (fun μ => step1Only_plug (Head.beta μ _ w) rfl K₀) ?_
  rw [show (0 + 1 : Nat) = 1 from rfl, show (0 + 1 + 1 : Nat) = 2 from rfl, kappa_resume_subst]
  exact hq

/-- **A tick under a handler of `Div` with one clause `c`, at `erwpK`** (`erwp_hnd_tick`). -/
theorem erwpK_hnd_tick {V : ι → ι → Prop} {Φ : ι → LocFam} {Tb : ι → TableK ι}
    (hL : ∀ x, (Tb x).Local) {Q : ι → PostN} {x : ι} (hΦ : (Φ x).Down) (hTd : (Tb x).Down)
    (hQ : ∀ y, (Q y).Down) (hr c : Val) (K₀ K₁ : Kont) (hK₁ : K₁.HasHnd divEff = false)
    {n : Nat} {ls : List SRec} {ρ : WRes}
    (h : ∀ ℓ : Loc, (ptoOwn ℓ Val.unit ─⋆ erwpK (ℍ := ℍ) V Φ Tb Q x (n - 1) ls
      (K₀.plug (.app (.val c)
        (.val (Val.pair .unit (kapV ℓ (hndVal divEff (qualsVal [.lin]) hr (c.pair .unit)) K₁))))))
      ρ) :
    erwpK (ℍ := ℍ) V Φ Tb Q x n ls
      (K₀.plug (hndE (hndVal divEff (qualsVal [.lin]) hr (c.pair .unit)) (K₁.plug tickE))) ρ := by
  refine erwpK_det hΦ hTd hQ (fun μ => step1Only_plug (Head.hop μ divEff 0 (qualsVal [.lin]) hr
    (Val.pair c .unit) c .unit K₁ (clauseAt_one c) hK₁) rfl K₀) ?_
  rw [kappaAt_lin]
  have e : K₀.plug (.app (.val c) (.pair (.val .unit)
      (kappaCell false (hndVal divEff (qualsVal [Qual.lin]) hr (c.pair Val.unit)) K₁))) =
      (K₀.comp (.appR (.val c) (.pairR .unit .hole))).plug
        (kappaCell false (hndVal divEff (qualsVal [Qual.lin]) hr (c.pair Val.unit)) K₁) := by
    rw [Kont.plug_comp]; rfl
  rw [e]
  refine erwpK_kappaCellV hL hΦ hTd hQ false _ K₁ _ (fun ℓ σ₁ σ₂ hp hc _ => ?_)
  rw [Kont.plug_comp]
  exact h ℓ σ₁ σ₂ hp hc

/-- **A tick under `div_fuel` with the budget spent, at `erwpK`** (`fuel_tick_zeroN`). -/
theorem fuel_tick_zeroK {V : ι → ι → Prop} {Φ : ι → LocFam} {Tb : ι → TableK ι}
    (hL : ∀ x, (Tb x).Local) {Q : ι → PostN} {x : ι} (hΦ : (Φ x).Down) (hTd : (Tb x).Down)
    (hQ : ∀ y, (Q y).Down) {K : Kont} (hK : FuelFrame 0 K) (K₁ : Kont)
    (hK₁ : K₁.HasHnd divEff = false) {n : Nat} {ls : List SRec} {ρ : WRes}
    (h : erwpK (ℍ := ℍ) V Φ Tb Q x (n - 1 - 1) ls
      (spentK.plug (hndE fuelH (K₁.plug (.val closeV)))) ρ) :
    erwpK (ℍ := ℍ) V Φ Tb Q x n ls (K.plug (hndE fuelH (K₁.plug tickE))) ρ := by
  refine erwpK_hnd_tick hL hΦ hTd hQ fuelR fuelC K K₁ hK₁ (fun ℓ σ₁ σ₂ hp hc => ?_)
  refine erwpK_pureSteps hΦ hTd hQ (fuel_clause hK _) ?_
  simp only [fixSelf]
  refine erwpK_pureSteps hΦ hTd hQ (PureSteps.head (fun μ => Head.case₁ μ .unit _ _) rfl) ?_
  have e : Expr.subst 0 Val.unit (.app (.val spentV) (.app (.app
      (.val ((kapV ℓ fuelH K₁).shift 1 0)) (.val (Val.inj₁ .unit))) (.val closeV))) =
      spentK.plug (.app (.app (kappaC false ℓ fuelH K₁) (.val (Val.inj₁ .unit))) (.val closeV)) := by
    simp [spentK, spentV, closeV, kapV_eq, Kont.plug]
    simp only [Expr.subst, substZero_shiftOne]
    rfl
  show erwpK (ℍ := ℍ) V Φ Tb Q x (n - 1) ls (Expr.subst 0 Val.unit (.app (.val spentV) (.app (.app
    (.val ((kapV ℓ fuelH K₁).shift 1 0)) (.val (Val.inj₁ .unit))) (.val closeV)))) σ₂
  rw [e]
  exact erwpK_kappaC_resume_in hL hΦ hTd hQ spentK false ℓ fuelH K₁ closeV
    ⟨σ₁, ρ, ResU.CompS.comm hc, hp, h⟩

/-- **A tick under `div_fuel` with budget left, at `erwpK`** (`fuel_tick_succN`). -/
theorem fuel_tick_succK {V : ι → ι → Prop} {Φ : ι → LocFam} {Tb : ι → TableK ι}
    (hL : ∀ x, (Tb x).Local) {Q : ι → PostN} {x : ι} (hΦ : (Φ x).Down) (hTd : (Tb x).Down)
    (hQ : ∀ y, (Q y).Down) {k : UInt32} (hk : k ≠ 0) {K : Kont} (hK : FuelFrame k K)
    (K₁ : Kont) (hK₁ : K₁.HasHnd divEff = false) {n : Nat} {ls : List SRec} {ρ : WRes}
    (h : erwpK (ℍ := ℍ) V Φ Tb Q x (n - 1 - 1) ls
      ((nextK (fixF k)).plug (hndE fuelH (K₁.plug (.val nextV)))) ρ) :
    erwpK (ℍ := ℍ) V Φ Tb Q x n ls (K.plug (hndE fuelH (K₁.plug tickE))) ρ := by
  refine erwpK_hnd_tick hL hΦ hTd hQ fuelR fuelC K K₁ hK₁ (fun ℓ σ₁ σ₂ hp hc => ?_)
  refine erwpK_pureSteps hΦ hTd hQ (fuel_clause hK _) ?_
  rw [show fixSelf fuelStep k = Val.inj₂ (fixF k) from fixSelf_succ hk]
  refine erwpK_pureSteps hΦ hTd hQ
    (PureSteps.head (fun μ => Head.case₂ μ (fixF k) _ _) rfl) ?_
  have e : Expr.subst 0 (fixF k) (.app (.val (.lam (.app (.var 1) (.var 0))))
      (.app (.app (.val ((kapV ℓ fuelH K₁).shift 1 0)) (.val (Val.inj₁ .unit))) (.val nextV))) =
      (nextK (fixF k)).plug
        (.app (.app (kappaC false ℓ fuelH K₁) (.val (Val.inj₁ .unit))) (.val nextV)) := by
    have hc := fixF_closed k
    have hv : Val.shift 1 0 (fixF k) = fixF k := Subtype.ext (closed_shift hc 1 0)
    simp [nextK, nextV, kapV_eq, Kont.plug]
    simp only [Expr.subst, substZero_shiftOne, hv]
    simp
  show erwpK (ℍ := ℍ) V Φ Tb Q x (n - 1) ls (Expr.subst 0 (fixF k) (.app (.val (.lam (.app (.var 1)
      (.var 0)))) (.app (.app (.val ((kapV ℓ fuelH K₁).shift 1 0)) (.val (Val.inj₁ .unit)))
        (.val nextV)))) σ₂
  rw [e]
  exact erwpK_kappaC_resume_in hL hΦ hTd hQ (nextK (fixF k)) false ℓ fuelH K₁ nextV
    ⟨σ₁, ρ, ResU.CompS.comm hc, hp, h⟩

end BoCa.Fig16.LogRel.Core.Chain.SI

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel (substAll)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Head Kont performE raiseE cancelVal opPayload hndE hndVal)

/-- The table of `tick, Σ` at the typed world: the tick's entry over the table of `Σ`
(`tabN_tick`). -/
theorem tabN_tickK (S : Row) (A : VTy) (δ : LSub) (x : KW) :
    tabN (ℍ := ℍ) (CTy.effOf (tickSig :: S) A) δ x = extTabK divEff 0
      (entNK .lin nextTy (fun k v ρ => vN (ℍ := ℍ) .unit δ x.Θ k v ρ)
        (fun y k v ρ => vN (ℍ := ℍ) nextTy δ y.Θ k v ρ ∧ ConsistentX y.c ρ)
        (finN (ℍ := ℍ) (.ret .unit) δ) (fun f y ρ => x.Owed f y ρ))
      (tabN (ℍ := ℍ) (CTy.effOf S A) δ x) := rfl

/-- **`div_fuel` is total, at the typed world** (`fuel_totalN₀`): under a frame at any budget, a
computation at the row `tick, Σ`, from a resource consistent with the view of a world whose
location typing is `OK`, is, handled, at `Σ`. By induction on the index: a tick is resumed at the
stop's own world, *next* (the frame at one less) or *close* (the frame `spent`), below the tick's
index; an operation of `Σ` passes the handler with its frame, the run going on at each world the
entry owes. -/
theorem fuel_totalN {S : Row} (hS : ∀ o ∈ S, o.n ≠ divEff) {A : VTy} {δ : LSub} :
    ∀ (n : Nat) (x : KW), x.Θ.OK → ∀ (k : UInt32) (K : Kont), FuelFrame k K →
      ∀ (ls : List SRec) (e : Expr) (ρ : WRes),
      erwpK (ℍ := ℍ) KW.PostK (fun z => z.Θ.view z.c)
        (fun z => opTableK z.lo (tabN (ℍ := ℍ) (CTy.effOf (tickSig :: S) A) δ z))
        (fun z k _ v ρ => vN (ℍ := ℍ) A δ z.Θ k v ρ) x n ls e ρ → ConsistentX x.c ρ →
      erwpK (ℍ := ℍ) KW.PostK (fun z => z.Θ.view z.c)
        (fun z => opTableK z.lo (tabN (ℍ := ℍ) (CTy.effOf S A) δ z))
        (fun z k _ v ρ => vN (ℍ := ℍ) A δ z.Θ k v ρ) x n ls (K.plug (hndE fuelH e)) ρ := by
  have hLin : ∀ z : KW,
      (opTableK z.lo (tabN (ℍ := ℍ) (CTy.effOf (tickSig :: S) A) δ z)).Local :=
    fun z => opTableK_local _ _
  have hLout : ∀ z : KW, (opTableK z.lo (tabN (ℍ := ℍ) (CTy.effOf S A) δ z)).Local :=
    fun z => opTableK_local _ _
  have hQ : ∀ z : KW, PostN.Down (fun k (_ : List SRec) v ρ => vN (ℍ := ℍ) A δ z.Θ k v ρ) :=
    fun z k _ v ρ h => vN_down A δ z.Θ k v ρ h
  have hsame : ∀ (z : KW) m i, ¬ (m = divEff ∧ i = 0) →
      tabN (ℍ := ℍ) (CTy.effOf (tickSig :: S) A) δ z m i =
        tabN (ℍ := ℍ) (CTy.effOf S A) δ z m i := by
    intro z m i h
    rw [tabN_tickK]
    simp only [extTabK, h, if_false]
  have hnone : ∀ (z : KW) i, tabN (ℍ := ℍ) (CTy.effOf S A) δ z divEff i = none := by
    intro z i
    rw [tabN_eq, tabF_effOf_find]
    cases hf : Row.find S divEff i with
    | none => rfl
    | some o => exact absurd (Row.find_mem hf).2.1 (hS o (Row.find_mem hf).1)
  have hdead : ∀ (K K₁ : Kont), K.dead = K →
      ((K.comp (hndK fuelH)).comp K₁).dead = (K.comp K₁).dead := by
    intro K K₁ hd
    rw [dead_comp, dead_comp, dead_comp, hd,
      show fuelH = hndVal divEff (qualsVal [.lin]) fuelR (Val.pair fuelC .unit) from rfl,
      dead_hndK, Kont.comp_hole]
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x hx k K hK ls e ρ h hc
  have hΦ : (x.Θ.view x.c).Down := LocTy.view_down hx.1 x.c
  have hDout : (opTableK x.lo (tabN (ℍ := ℍ) (CTy.effOf S A) δ x)).Down :=
    opTableK_downI (tabN_downI_OK _ δ x)
  have e₁ : ∀ y, K.plug (hndE fuelH y) = (K.comp (hndK fuelH)).plug y := fun y => by
    rw [Kont.plug_comp]; rfl
  rw [erwpK_eq] at h
  rw [e₁, erwpK_eq]
  refine rwpG_bind hΦ (K.comp (hndK fuelH)) ?_
  refine rwpG_mono_le (fun k' hk ls' t σ ⟨ht, hcσ, hvσ⟩ => ?_) (rwpG_consistentXV h hc)
  rcases ht with ⟨v, rfl, y, hy, hv⟩ | ⟨K₁, m, i, v, en, hp⟩ | ⟨K₁, m, i, v, en, hp⟩
  · -- `[ret]`
    have hy' : y = x := hy
    subst hy'
    rw [← e₁]
    exact erwpK_unfold_at (V := KW.PostK) (Φ := fun z : KW => z.Θ.view z.c) hLout hk
      (erwpK_pureSteps (Φ := fun z : KW => z.Θ.view z.c) hΦ hDout hQ (fuel_ret hK v)
      (erwpK_val (KW.postK_refl y) hv))
  · obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρk, hcak, hA, hu, f, hf, hcont⟩ := pure_sep_iff.mp hp
    by_cases hmi : m = divEff ∧ i = 0
    · -- a tick, resumed at the stop's own world: *close* once the budget is spent, *next*
      -- otherwise
      obtain ⟨rfl, rfl⟩ := hmi
      rw [tabN_tickK] at hT
      simp only [extTabK, and_self, if_true, Option.some.injEq] at hT
      subst hT
      obtain ⟨rfl, rfl⟩ : v = Val.unit ∧ ρa = PMap.empty := hA
      obtain rfl := eq_of_compS_empty_left hcak
      rw [← e₁]
      refine erwpK_unfold_at (V := KW.PostK) (Φ := fun z : KW => z.Θ.view z.c) (x := x) hLout hk ?_
      show erwpK (ℍ := ℍ) _ _ _ _ x k' ls' (K.plug (hndE fuelH (K₁.plug tickE))) σ
      rcases Nat.lt_or_ge k' 1 with hk1 | hk1
      · obtain rfl : k' = 0 := by omega
        exact erwpK_zero
      have hres : ∀ w, vN (ℍ := ℍ) nextTy δ x.Θ (k' - 1 - 1) w PMap.empty →
          erwpK (ℍ := ℍ) KW.PostK (fun z => z.Θ.view z.c)
            (fun z => opTableK z.lo (tabN (ℍ := ℍ) (CTy.effOf (tickSig :: S) A) δ z))
            (fun z k _ v ρ => vN (ℍ := ℍ) A δ z.Θ k v ρ) x (k' - 1 - 1) ls' (K₁.plug (.val w))
            σ := by
        intro w hw
        have h₁ := (hcont x (KW.owed_self hx f hcσ) ls' (extF_refl ls' σ)).1 (k' - 1 - 1)
          (by omega) w PMap.empty σ ⟨hw, consistentX_empty _⟩ (ResU.comp_empty_right σ)
        simp only [erwpCK, show k' - 1 - 1 < n by omega, if_true] at h₁
        exact h₁
      by_cases hk0 : k = 0
      · subst hk0
        exact fuel_tick_zeroK hLout hΦ hDout hQ hK K₁ (by simpa using hK₁)
          (ih (k' - 1 - 1) (by omega) x hx 0 spentK spentK_frame ls' _ σ
            (hres closeV (Or.inr ⟨Val.unit, rfl, rfl, rfl⟩)) hcσ)
      · exact fuel_tick_succK hLout hΦ hDout hQ hk0 hK K₁ (by simpa using hK₁)
          (ih (k' - 1 - 1) (by omega) x hx (k - 1) _ (nextK_frame k) ls' _ σ
            (hres nextV (Or.inl ⟨Val.unit, rfl, rfl, rfl⟩)) hcσ)
    · -- an operation of `Σ` passes the handler with its frame
      have hT' := (hsame x m i hmi) ▸ hT
      have hm : m ≠ divEff := by rintro rfl; rw [hnone] at hT'; cases hT'
      have hck := consistentX_right hcak hcσ hvσ
      have hKo : ((K.comp (hndK fuelH)).comp K₁).HasHnd m = false := by
        rw [hasHnd_comp, hasHnd_comp, hK.1,
          show fuelH = hndVal divEff (qualsVal [.lin]) fuelR (Val.pair fuelC .unit) from rfl,
          hndK_hasHnd, hK₁]
        simpa using Ne.symm hm
      have ht' : (K.comp (hndK fuelH)).plug (K₁.plug (performE (.val (opPayload m i v)))) =
          ((K.comp (hndK fuelH)).comp K₁).plug (opE false (opPayload m i v)) := by
        simp only [Kont.plug_comp]; rfl
      rw [ht']
      refine rwpG_here (final_opPlug (payloadName_opPayload m i v) hKo) (Or.inr (Or.inl
        ⟨(K.comp (hndK fuelH)).comp K₁, m, i, v, en, pure_sep_mk ⟨rfl, hKo, hT', ha⟩
          ⟨ρa, ρk, hcak, hA, hu, f, hf, fun y hy ls'' he =>
            ⟨fun k'' hk'' w τ₁ τ₂ hB hcτ => ?_, fun hq' => ?_⟩⟩⟩))
      · have hyO : x.Owed f y ρk := tabN_wkC δ _ x m i en hT f y ρk hy
        have h₁ := (hcont y hy ls'' he).1 k'' hk'' w τ₁ τ₂ hB hcτ
        simp only [erwpCK, show k'' < n by omega, if_true] at h₁ ⊢
        rw [Kont.plug_comp, ← e₁]
        obtain ⟨o, -, rfl⟩ := tabF_rowOf_find (tabF_of_tabN hT)
        exact ih k'' (by omega) y hyO.2.1 k K hK ls'' _ τ₂ h₁
          (consistentX_compS hcτ hyO.2.2.1 hB.2)
      · intro P hP
        have hyO : x.Owed f y ρk := tabN_wkC δ _ x m i en hT f y ρk hy
        show P y k' ls'' (((K.comp (hndK fuelH)).comp K₁).dead.plug _) ρk
        rw [hdead K K₁ hK.2.2.1]
        obtain ⟨o, -, rfl⟩ := tabF_rowOf_find (tabF_of_tabN hT')
        exact entF_plain (rdN_ok δ) K hK.1 (hK.2.1 0) noOwn_empty o hyO.2.1.1
          ((hcont y hy ls'' he).2 hq') (ResU.comp_empty_right ρk) P hP
  · obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρn, hcan, ⟨hPA, hnA⟩, hnn⟩ := pure_sep_iff.mp hp
    by_cases hmi : m = divEff ∧ i = 0
    · -- the tick is not abortive
      obtain ⟨rfl, rfl⟩ := hmi
      rw [tabN_tickK] at hT
      simp only [extTabK, and_self, if_true, Option.some.injEq] at hT
      subst hT
      simp [entNK, VTy.isZero] at ha
    · -- an abortive operation of `Σ` passes the handler
      have hT' := (hsame x m i hmi) ▸ hT
      have hm : m ≠ divEff := by rintro rfl; rw [hnone] at hT'; cases hT'
      have hKo : ((K.comp (hndK fuelH)).comp K₁).Catches m = false := by
        rw [catches_comp, catches_comp, hK.2.1,
          show fuelH = hndVal divEff (qualsVal [.lin]) fuelR (Val.pair fuelC .unit) from rfl,
          hndK_catches, hK₁]
        simpa using Ne.symm hm
      have ht' : (K.comp (hndK fuelH)).plug (K₁.plug (raiseE (.val (opPayload m i v)))) =
          ((K.comp (hndK fuelH)).comp K₁).plug (opE true (opPayload m i v)) := by
        simp only [Kont.plug_comp]; rfl
      rw [ht']
      exact rwpG_here (final_opPlug (payloadName_opPayload m i v) hKo) (Or.inr (Or.inr
        ⟨(K.comp (hndK fuelH)).comp K₁, m, i, v, en, pure_sep_mk ⟨rfl, hKo, hT', ha⟩
          ⟨ρa, ρn, hcan, ⟨hPA, hnA⟩, hnn⟩⟩))

/-- **`div_fuel` at `SemJN`** (`divFuel_compatN₀`): total at the rest of the row. The callback is
forced at the function's own world and view, applied at `()`; `div_fuel (t, k)` steps to the
handler under the budget's frame (`divFuel_steps`), and `fuel_totalN` takes it to the row `Σ` at
every floor. -/
theorem divFuel_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {S : Row} {A : VTy}
    (hS : ∀ o ∈ S, o.n ≠ divEff) (hΓ : Ctx.DeadP Γ) :
    SemJN (ℍ := ℍ) Δ Γ (.val divFuelV) (.val (divFuelTy S A)) := by
  intro δ γ Θ c n ls ρ _ _ _ _ hg
  obtain rfl := gN_deadP hΓ hg
  rw [show substAll γ (.val divFuelV) = .val divFuelV from substAll_closed divFuelV_closed γ]
  refine cN_ret_of (erwp_val (v := divFuelV) ⟨rfl, ?_⟩)
  intro Θ' _ hΘ' _ _ ls' c'' k hk v σ τ hcomp hv hcon
  obtain rfl := eq_of_compS_empty_left hcomp
  obtain ⟨t, vk, σ₁, σ₂, rfl, hc, ht, ⟨⟨kk, rfl⟩, rfl⟩⟩ := hv
  obtain rfl := ResU.CompS.functional hc (ResU.comp_empty_right σ₁)
  have ht' := ht Θ' (LocTy.extR_refl Θ' _) hΘ' c'' hcon ls' c'' k le_rfl Val.unit PMap.empty _
    (ResU.comp_empty_right _) ⟨rfl, rfl⟩ hcon
  have hin := (cN_effOf (tickSig :: S) A δ Θ' c'' k ls' _ _).mp ht'
  refine (cN_effOf S A δ Θ' c'' k ls' _ _).mpr fun lo => ?_
  refine erwpK_pureSteps (Φ := fun z : KW => z.Θ.view z.c) (x := (⟨Θ', c'', lo⟩ : KW))
    (LocTy.view_down hΘ'.1 c'') (opTableK_downI (tabN_downI_OK _ δ _))
    (fun z k _ v ρ h => vN_down A δ z.Θ k v ρ h) (divFuel_steps t kk) ?_
  exact fuel_totalN hS k ⟨Θ', c'', lo⟩ hΘ' kk (fuelK kk) (fuelK_frame kk) ls' _ _ (hin lo) hcon

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
