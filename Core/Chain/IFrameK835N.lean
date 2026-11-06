import Core.Chain.SI.IFrameK
import Core.Chain.MFrameK835N
import Core.Chain.FamImm836N

/-!
# The `imm` lend frames at `erwpK`  `[spec §19, §27, §62]`

`docs/new-core/scope-835-iframes.md`. Each Imm Frame across stops, restated at `erwpK` over any
world index (`erwpK_I_frame*`), as an instance of `erwpK_I_frameGen` (`SI/IFrameK.lean`); and its
`erwp` statement, word for word, proved again from the restated frame at one world
(`erwp_I_frame*_of_K`).

At a world index the borrowed run and the lender stop at different tables (`Ti`, `To`): the
borrowed run's entries owe at the lend's world, the lender's at its own, and `OpTabK.IFoldTwin`
relates them across the fold (`ifoldTwin_owed` at `KW`). At one world both are the lifted table and
`IFoldTwin` holds of a twin (`ifoldTwin_lift`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Head Kont performE raiseE cancelVal opPayload)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

variable {ι : Type}

/-! ### The frame's shape -/

/-- **An Imm Frame at `erwpK`**: `ℓ ↦ v ⋆ P̂(ls)(v) ⋆ ρ_b` lent `imm` at `A` to a computation in
`erwpK` from `ρ_b ● ρᵢ` at `frameList p ds A ls`, at the tables `TbI` and the post `QI`, at a world
where `Inv` holds: the computation is in `erwpK` at the tables `TbO` and the post `Q`. -/
def IKFrame (V : ι → ι → Prop) (Φ : ι → LocFam) (Inv : ι → Prop) (l : Loc) (Ty : VTy)
    (δ : LSub) (v : Val) (P : List SRec → Val → WProp) (A : Life) (ρP ρlP : WRes)
    (houtP : ρP.InStratum A) (ds : List FrameRec) (TbI TbO : ι → TableK ι) (QI Q : ι → PostN) :
    Prop :=
  ∀ n (x : ι), Inv x → ∀ ls e (ρb ρ : WRes), ρb.InStratum A → P ls v ρP → ResU.CompS ρlP ρb ρ →
    (∀ BI, ResU.CompS ρb (ResU.single l (CellU.immOf (LSet.singleton A) v ρP houtP)) BI →
      erwpK (ℍ := ℍ) V Φ TbI QI x n (frameList ⟨l, v, ρP, Ty, δ⟩ ds A ls) e BI) →
    erwpK (ℍ := ℍ) V Φ TbO Q x n ls e ρ

/-- A frame at one outer table is a frame at every table allowing its stops. -/
theorem IKFrame.conv {V : ι → ι → Prop} {Φ : ι → LocFam} {Inv : ι → Prop} {l : Loc} {Ty : VTy}
    {δ : LSub} {v : Val} {P : List SRec → Val → WProp} {A : Life} {ρP ρlP : WRes}
    {houtP : ρP.InStratum A} {ds : List FrameRec} {TbI TbO TbO' : ι → TableK ι}
    {QI Q : ι → PostN}
    (h : IKFrame (ℍ := ℍ) V Φ Inv l Ty δ v P A ρP ρlP houtP ds TbI TbO QI Q)
    (hL : ∀ x, (TbO x).Local) (hc : ∀ x k ls t Ψ ρ, TbO x k ls t Ψ ρ → TbO' x k ls t Ψ ρ) :
    IKFrame (ℍ := ℍ) V Φ Inv l Ty δ v P A ρP ρlP houtP ds TbI TbO' QI Q := by
  intro n x hx ls e ρb ρ houtb hPv hcρ hA
  exact erwpK_mono (fun _ _ h => h) (fun _ _ _ _ _ h => h)
    (fun x k ls t Ψ Ψ' ρ hΨ hT => hc x k ls t Ψ' ρ (hL x k ls t Ψ Ψ' ρ hΨ hT)) n x ls e ρ
    (h n x hx ls e ρb ρ houtb hPv hcρ hA)

/-- A frame for one borrowed post is a frame for every post inside it. -/
theorem IKFrame.postIn {V : ι → ι → Prop} {Φ : ι → LocFam} {Inv : ι → Prop} {l : Loc} {Ty : VTy}
    {δ : LSub} {v : Val} {P : List SRec → Val → WProp} {A : Life} {ρP ρlP : WRes}
    {houtP : ρP.InStratum A} {ds : List FrameRec} {TbI TbO : ι → TableK ι}
    {QI QI' Q : ι → PostN}
    (h : IKFrame (ℍ := ℍ) V Φ Inv l Ty δ v P A ρP ρlP houtP ds TbI TbO QI Q)
    (hL : ∀ x, (TbI x).Local) (hQ : ∀ y k ls v ρ, QI' y k ls v ρ → QI y k ls v ρ) :
    IKFrame (ℍ := ℍ) V Φ Inv l Ty δ v P A ρP ρlP houtP ds TbI TbO QI' Q := by
  intro n x hx ls e ρb ρ houtb hPv hcρ hA
  exact h n x hx ls e ρb ρ houtb hPv hcρ fun BI hBI =>
    erwpK_mono (fun _ _ h => h) hQ (fun x k ls t Ψ Ψ' ρ hΨ h => hL x k ls t Ψ Ψ' ρ hΨ h) n x _
      e BI (hA BI hBI)

theorem liftTabK_ext {Q : PostN} (hQ : ∀ k ls₁ ls₂ w ρ, Ext ls₁ ls₂ ρ → Q k ls₁ w ρ → Q k ls₂ w ρ) :
    ∀ (_ : Unit) k ls₁ ls₂ w ρ, Ext ls₁ ls₂ ρ → (fun _ : Unit => Q) () k ls₁ w ρ →
      (fun _ : Unit => Q) () k ls₂ w ρ :=
  fun _ => hQ

/-! ### `erwp_I_frame` -/

/-- **Imm Frame at `erwpK` across Kripke stops** (`erwp_I_frame`): a table of must-resume stops
and no raise. -/
theorem erwpK_I_frame {V : ι → ι → Prop} {Φ : ι → LocFam} {Inv : ι → Prop} (l : Loc) (Ty : VTy)
    (δ : LSub) (hadm : AdmWf Ty δ) (v : Val) (P : List SRec → Val → WProp)
    (hPshape : ∀ ls ρ, P ls v ρ → vShape Ty δ v ρ)
    (hPloc : ∀ ls₁ ls₂ ρ, extF ls₁ ls₂ ρ → P ls₁ v ρ → P ls₂ v ρ)
    {A : Life} {ρP ρlP : WRes} (houtP : ρP.InStratum A)
    (hclP : ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP)
    {ds : List FrameRec} (hds : ∀ d, d ∈ ds ↔ Desc ⟨l, v, ρP, Ty, δ⟩ d)
    {flI flO : ι → Life} {Ti To : ι → OpTabK ι} (hT : ∀ x, (Ti x).ILendOKCR A)
    (hab : ∀ x m i en, Ti x m i = some en → en.abort = false)
    (hlin : ∀ x m i en, Ti x m i = some en → en.abort = false → en.q = .lin)
    (hTT : ∀ x, Inv x → (Ti x).IFoldTwin Inv (flI x) (flO x) (To x) l A v ρP ρlP houtP)
    {Q : ι → PostN} (hQ : ∀ y k ls₁ ls₂ w ρ, Ext ls₁ ls₂ ρ → Q y k ls₁ w ρ → Q y k ls₂ w ρ) :
    IKFrame (ℍ := ℍ) V Φ Inv l Ty δ v P A ρP ρlP houtP ds (fun y => opTableK (flI y) (Ti y))
      (fun y => opTableK (flO y) (To y)) (fun y => IFPost l v P A (Q y)) Q :=
  IKFrame.conv (TbO := fun y k ls t Ψ => BoLo.or
      (performStopGK (flO y) (To y) (fun _ _ _ => True) k ls t Ψ) (raiseStopK (To y) k ls t Ψ))
    (erwpK_I_frameGen (RI := fun y => raiseStopK (Ti y)) (RO := fun y => raiseStopK (To y))
      (G := fun _ _ _ _ => True) l Ty δ hadm v P hPshape hPloc houtP hclP hds hT hTT
      (icanK_of_lin hlin) (by intros; trivial) (fun x _ => iraiseFold_absurd (hab x) _) hQ)
    (fun x => or_local (performStopGK_local _ _ _) (raiseStopK_free _)) unguard

/-- `erwp_I_frame` from `erwpK_I_frame`. -/
theorem erwp_I_frame_of_K {Φ : LocFam} (l : Loc) (T : VTy) (δ : LSub) (hadm : AdmWf T δ) (v : Val)
    (P : List SRec → Val → WProp) (hPshape : ∀ ls ρ, P ls v ρ → vShape T δ v ρ)
    (hPloc : ∀ ls₁ ls₂ ρ, extF ls₁ ls₂ ρ → P ls₁ v ρ → P ls₂ v ρ)
    {A : Life} {Tb : OpTabN} (hT : Tb.ILendOK A) {Q : PostN}
    (hQ : ∀ k ls₁ ls₂ w ρ, Ext ls₁ ls₂ ρ → Q k ls₁ w ρ → Q k ls₂ w ρ) :
    ∀ n ls e (ρP ρlP ρb ρ : WRes) (houtP : ρP.InStratum A), ρb.InStratum A →
      P ls v ρP → ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP → ResU.CompS ρlP ρb ρ →
      ∀ ds, (∀ d, d ∈ ds ↔ Desc ⟨l, v, ρP, T, δ⟩ d) →
      (∀ BI, ResU.CompS ρb (ResU.single l (CellU.immOf (LSet.singleton A) v ρP houtP)) BI →
        erwp (ℍ := ℍ) Φ (opTableN Tb) (IFPost l v P A Q) n (frameList ⟨l, v, ρP, T, δ⟩ ds A ls)
          e BI) →
      erwp (ℍ := ℍ) Φ (opTableN Tb) Q n ls e ρ := by
  intro n ls e ρP ρlP ρb ρ houtP houtb hPv hclP hcρ ds hds hA
  rw [erwp_opTableN_eq_erwpK A]
  refine erwpK_I_frame (V := fun _ _ => True) (Φ := fun _ => Φ) (Inv := fun _ => True)
    (flI := fun _ => A) (flO := fun _ => A) (Ti := fun _ => liftTabK Tb)
    (To := fun _ => liftTabK Tb) (Q := fun _ => Q) l T δ hadm v P hPshape hPloc houtP hclP hds
    (fun _ => hT.toR.liftK) (liftTabK_abort fun m i en h => (hT.entry m i en h).1)
    (liftTabK_lin fun m i en h _ => (hT.entry m i en h).2.1)
    (fun _ _ => ifoldTwin_lift (OpTabN.twin_refl Tb) A l A v ρP ρlP houtP) (liftTabK_ext hQ)
    n () trivial ls e ρb ρ houtb hPv hcρ fun BI hBI => ?_
  have h := hA BI hBI
  rw [erwp_opTableN_eq_erwpK A] at h
  exact h

/-! ### The other variants -/

/-- **Imm Frame at `erwpK` across Kripke stops**, raises carrying the claim (`erwp_I_frameR`). -/
theorem erwpK_I_frameR {V : ι → ι → Prop} {Φ : ι → LocFam} {Inv : ι → Prop} (l : Loc) (Ty : VTy)
    (δ : LSub) (hadm : AdmWf Ty δ) (v : Val) (P : List SRec → Val → WProp)
    (hPshape : ∀ ls ρ, P ls v ρ → vShape Ty δ v ρ)
    (hPloc : ∀ ls₁ ls₂ ρ, extF ls₁ ls₂ ρ → P ls₁ v ρ → P ls₂ v ρ)
    {A : Life} {ρP ρlP : WRes} (houtP : ρP.InStratum A)
    (hclP : ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP)
    {ds : List FrameRec} (hds : ∀ d, d ∈ ds ↔ Desc ⟨l, v, ρP, Ty, δ⟩ d)
    {flI flO : ι → Life} {Ti To : ι → OpTabK ι} (hT : ∀ x, (Ti x).ILendOKCR A)
    (hlin : ∀ x m i en, Ti x m i = some en → en.abort = false → en.q = .lin)
    (hTT : ∀ x, Inv x → (Ti x).IFoldTwin Inv (flI x) (flO x) (To x) l A v ρP ρlP houtP)
    {Q : ι → PostN} (hQ : ∀ y k ls₁ ls₂ w ρ, Ext ls₁ ls₂ ρ → Q y k ls₁ w ρ → Q y k ls₂ w ρ) :
    IKFrame (ℍ := ℍ) V Φ Inv l Ty δ v P A ρP ρlP houtP ds (fun y => opTableK (flI y) (Ti y))
      (fun y => opTableRK (flO y) (To y) (claimI l v ρP)) (fun y => IFPost l v P A (Q y)) Q :=
  IKFrame.conv (TbO := fun y k ls t Ψ => BoLo.or
      (performStopGK (flO y) (To y) (fun _ _ _ => True) k ls t Ψ)
      (raiseStopRK (To y) (claimI l v ρP) k ls t Ψ))
    (erwpK_I_frameGen (RI := fun y => raiseStopK (Ti y))
      (RO := fun y => raiseStopRK (To y) (claimI l v ρP))
      (G := fun _ _ _ _ => True) l Ty δ hadm v P hPshape hPloc houtP hclP hds hT hTT
      (icanK_of_lin hlin) (by intros; trivial)
      (fun x hx => iraiseFold_claim hclP (hTT x hx).twin (hT x)) hQ)
    (fun _ => or_local (performStopGK_local _ _ _) (raiseStopRK_free _ _)) unguard

/-- `erwp_I_frameR` from `erwpK_I_frameR`. -/
theorem erwp_I_frameR_of_K {Φ : LocFam} (l : Loc) (T : VTy) (δ : LSub) (hadm : AdmWf T δ)
    (v : Val) (P : List SRec → Val → WProp) (hPshape : ∀ ls ρ, P ls v ρ → vShape T δ v ρ)
    (hPloc : ∀ ls₁ ls₂ ρ, extF ls₁ ls₂ ρ → P ls₁ v ρ → P ls₂ v ρ)
    {A : Life} {Tb : OpTabN} (hT : Tb.ILendOKR A) {Q : PostN}
    (hQ : ∀ k ls₁ ls₂ w ρ, Ext ls₁ ls₂ ρ → Q k ls₁ w ρ → Q k ls₂ w ρ) :
    ∀ n ls e (ρP ρlP ρb ρ : WRes) (houtP : ρP.InStratum A), ρb.InStratum A →
      P ls v ρP → ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP → ResU.CompS ρlP ρb ρ →
      ∀ ds, (∀ d, d ∈ ds ↔ Desc ⟨l, v, ρP, T, δ⟩ d) →
      (∀ BI, ResU.CompS ρb (ResU.single l (CellU.immOf (LSet.singleton A) v ρP houtP)) BI →
        erwp (ℍ := ℍ) Φ (opTableN Tb) (IFPost l v P A Q) n (frameList ⟨l, v, ρP, T, δ⟩ ds A ls)
          e BI) →
      erwp (ℍ := ℍ) Φ (opTableR Tb (claimI l v ρP)) Q n ls e ρ := by
  intro n ls e ρP ρlP ρb ρ houtP houtb hPv hclP hcρ ds hds hA
  rw [erwp_eq_erwpK_of (opTableRK_lift A Tb (claimI l v ρP)) Φ Q]
  refine erwpK_I_frameR (V := fun _ _ => True) (Φ := fun _ => Φ) (Inv := fun _ => True)
    (flI := fun _ => A) (flO := fun _ => A) (Ti := fun _ => liftTabK Tb)
    (To := fun _ => liftTabK Tb) (Q := fun _ => Q) l T δ hadm v P hPshape hPloc houtP hclP hds
    (fun _ => hT.liftK) (liftTabK_lin fun m i en h ha => (hT.entry m i en h ha).1)
    (fun _ _ => ifoldTwin_lift (OpTabN.twin_refl Tb) A l A v ρP ρlP houtP) (liftTabK_ext hQ)
    n () trivial ls e ρb ρ houtb hPv hcρ fun BI hBI => ?_
  have h := hA BI hBI
  rw [erwp_opTableN_eq_erwpK A] at h
  exact h

/-- **Imm Frame at `erwpK` across Kripke stops**, the inner raises already carrying a claim `R`
(`erwp_I_frameRR`). -/
theorem erwpK_I_frameRR {V : ι → ι → Prop} {Φ : ι → LocFam} {Inv : ι → Prop} (l : Loc)
    (Ty : VTy) (δ : LSub) (hadm : AdmWf Ty δ) (v : Val) (P : List SRec → Val → WProp)
    (hPshape : ∀ ls ρ, P ls v ρ → vShape Ty δ v ρ)
    (hPloc : ∀ ls₁ ls₂ ρ, extF ls₁ ls₂ ρ → P ls₁ v ρ → P ls₂ v ρ)
    {A : Life} {ρP ρlP : WRes} (houtP : ρP.InStratum A)
    (hclP : ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP)
    {ds : List FrameRec} (hds : ∀ d, d ∈ ds ↔ Desc ⟨l, v, ρP, Ty, δ⟩ d)
    {flI flO : ι → Life} {Ti To : ι → OpTabK ι} (hT : ∀ x, (Ti x).ILendOKCR A)
    (hlin : ∀ x m i en, Ti x m i = some en → en.abort = false → en.q = .lin)
    (hTT : ∀ x, Inv x → (Ti x).IFoldTwin Inv (flI x) (flO x) (To x) l A v ρP ρlP houtP)
    {R : Nat → WProp} (hR : ∀ k ρ, R k ρ → ρ.InStratum A)
    {Q : ι → PostN} (hQ : ∀ y k ls₁ ls₂ w ρ, Ext ls₁ ls₂ ρ → Q y k ls₁ w ρ → Q y k ls₂ w ρ) :
    IKFrame (ℍ := ℍ) V Φ Inv l Ty δ v P A ρP ρlP houtP ds (fun y => opTableRK (flI y) (Ti y) R)
      (fun y => opTableRK (flO y) (To y) (fun k => claimI l v ρP k ⋆ R k))
      (fun y => IFPost l v P A (Q y)) Q :=
  IKFrame.conv (TbO := fun y k ls t Ψ => BoLo.or
      (performStopGK (flO y) (To y) (fun _ _ _ => True) k ls t Ψ)
      (raiseStopRK (To y) (fun k => claimI l v ρP k ⋆ R k) k ls t Ψ))
    (erwpK_I_frameGen (RI := fun y => raiseStopRK (Ti y) R)
      (RO := fun y => raiseStopRK (To y) (fun k => claimI l v ρP k ⋆ R k))
      (G := fun _ _ _ _ => True) l Ty δ hadm v P hPshape hPloc houtP hclP hds hT hTT
      (icanK_of_lin hlin) (by intros; trivial)
      (fun x hx => iraiseFold_claimR hclP (hTT x hx).twin (hT x) hR) hQ)
    (fun _ => or_local (performStopGK_local _ _ _) (raiseStopRK_free _ _)) unguard

/-- `erwp_I_frameRR` from `erwpK_I_frameRR`. -/
theorem erwp_I_frameRR_of_K {Φ : LocFam} (l : Loc) (T : VTy) (δ : LSub) (hadm : AdmWf T δ)
    (v : Val) (P : List SRec → Val → WProp) (hPshape : ∀ ls ρ, P ls v ρ → vShape T δ v ρ)
    (hPloc : ∀ ls₁ ls₂ ρ, extF ls₁ ls₂ ρ → P ls₁ v ρ → P ls₂ v ρ)
    {A : Life} {Tb : OpTabN} (hT : Tb.ILendOKR A) {R : Nat → WProp}
    (hR : ∀ k ρ, R k ρ → ρ.InStratum A) {Q : PostN}
    (hQ : ∀ k ls₁ ls₂ w ρ, Ext ls₁ ls₂ ρ → Q k ls₁ w ρ → Q k ls₂ w ρ) :
    ∀ n ls e (ρP ρlP ρb ρ : WRes) (houtP : ρP.InStratum A), ρb.InStratum A →
      P ls v ρP → ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP → ResU.CompS ρlP ρb ρ →
      ∀ ds, (∀ d, d ∈ ds ↔ Desc ⟨l, v, ρP, T, δ⟩ d) →
      (∀ BI, ResU.CompS ρb (ResU.single l (CellU.immOf (LSet.singleton A) v ρP houtP)) BI →
        erwp (ℍ := ℍ) Φ (opTableR Tb R) (IFPost l v P A Q) n
          (frameList ⟨l, v, ρP, T, δ⟩ ds A ls) e BI) →
      erwp (ℍ := ℍ) Φ (opTableR Tb (fun k => claimI l v ρP k ⋆ R k)) Q n ls e ρ := by
  intro n ls e ρP ρlP ρb ρ houtP houtb hPv hclP hcρ ds hds hA
  rw [erwp_eq_erwpK_of (opTableRK_lift A Tb (fun k => claimI l v ρP k ⋆ R k)) Φ Q]
  refine erwpK_I_frameRR (V := fun _ _ => True) (Φ := fun _ => Φ) (Inv := fun _ => True)
    (flI := fun _ => A) (flO := fun _ => A) (Ti := fun _ => liftTabK Tb)
    (To := fun _ => liftTabK Tb) (Q := fun _ => Q) l T δ hadm v P hPshape hPloc houtP hclP hds
    (fun _ => hT.liftK) (liftTabK_lin fun m i en h ha => (hT.entry m i en h ha).1)
    (fun _ _ => ifoldTwin_lift (OpTabN.twin_refl Tb) A l A v ρP ρlP houtP) hR (liftTabK_ext hQ)
    n () trivial ls e ρb ρ houtb hPv hcρ fun BI hBI => ?_
  have h := hA BI hBI
  rw [erwp_eq_erwpK_of (opTableRK_lift A Tb R) Φ _] at h
  exact h

/-- **Imm Frame at `erwpK` across Kripke stops**, cancellable stops at the twin table
(`erwp_I_frameT`). -/
theorem erwpK_I_frameT {V : ι → ι → Prop} {Φ : ι → LocFam} {Inv : ι → Prop} (l : Loc) (Ty : VTy)
    (δ : LSub) (hadm : AdmWf Ty δ) (v : Val) (P : List SRec → Val → WProp)
    (hPshape : ∀ ls ρ, P ls v ρ → vShape Ty δ v ρ)
    (hPloc : ∀ ls₁ ls₂ ρ, extF ls₁ ls₂ ρ → P ls₁ v ρ → P ls₂ v ρ)
    {A : Life} {ρP ρlP : WRes} (houtP : ρP.InStratum A)
    (hclP : ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP)
    {ds : List FrameRec} (hds : ∀ d, d ∈ ds ↔ Desc ⟨l, v, ρP, Ty, δ⟩ d)
    {flI flO : ι → Life} {Ti To : ι → OpTabK ι} (hT : ∀ x, (Ti x).ILendOKCR A)
    (hab : ∀ x m i en, Ti x m i = some en → en.abort = false)
    (hcan : ICanK Inv Ti To l Ty δ A v ρP ρlP houtP ds)
    (hTT : ∀ x, Inv x → (Ti x).IFoldTwin Inv (flI x) (flO x) (To x) l A v ρP ρlP houtP)
    {Q : ι → PostN} (hQ : ∀ y k ls₁ ls₂ w ρ, Ext ls₁ ls₂ ρ → Q y k ls₁ w ρ → Q y k ls₂ w ρ) :
    IKFrame (ℍ := ℍ) V Φ Inv l Ty δ v P A ρP ρlP houtP ds (fun y => opTableK (flI y) (Ti y))
      (fun y => opTableK (flO y) (To y)) (fun y => IFPost l v P A (Q y)) Q :=
  IKFrame.conv (TbO := fun y k ls t Ψ => BoLo.or
      (performStopGK (flO y) (To y) (fun _ _ _ => True) k ls t Ψ) (raiseStopK (To y) k ls t Ψ))
    (erwpK_I_frameGen (RI := fun y => raiseStopK (Ti y)) (RO := fun y => raiseStopK (To y))
      (G := fun _ _ _ _ => True) l Ty δ hadm v P hPshape hPloc houtP hclP hds hT hTT hcan
      (by intros; trivial) (fun x _ => iraiseFold_absurd (hab x) _) hQ)
    (fun x => or_local (performStopGK_local _ _ _) (raiseStopK_free _)) unguard

/-- `erwp_I_frameT` from `erwpK_I_frameT`. -/
theorem erwp_I_frameT_of_K {Φ : LocFam} (l : Loc) (Ty : VTy) (δ : LSub) (hadm : AdmWf Ty δ)
    (v : Val) (P : List SRec → Val → WProp) (hPshape : ∀ ls ρ, P ls v ρ → vShape Ty δ v ρ)
    (hPloc : ∀ ls₁ ls₂ ρ, extF ls₁ ls₂ ρ → P ls₁ v ρ → P ls₂ v ρ)
    {A : Life} {T T' : OpTabN} (hT : T.ILendOKC A) (hTT' : T.Twin T') {ρP ρlP : WRes}
    (houtP : ρP.InStratum A) (hclP : ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP)
    {ds : List FrameRec} (hds : ∀ d, d ∈ ds ↔ Desc ⟨l, v, ρP, Ty, δ⟩ d)
    (hcan : ICan T T' l Ty δ A v ρP ρlP houtP ds) {Q : PostN}
    (hQ : ∀ k ls₁ ls₂ w ρ, Ext ls₁ ls₂ ρ → Q k ls₁ w ρ → Q k ls₂ w ρ) :
    ∀ n ls e (ρb ρ : WRes), ρb.InStratum A → P ls v ρP → ResU.CompS ρlP ρb ρ →
      (∀ BI, ResU.CompS ρb (ResU.single l (CellU.immOf (LSet.singleton A) v ρP houtP)) BI →
        erwp (ℍ := ℍ) Φ (opTableN T) (IFPost l v P A Q) n (frameList ⟨l, v, ρP, Ty, δ⟩ ds A ls)
          e BI) →
      erwp (ℍ := ℍ) Φ (opTableN T') Q n ls e ρ := by
  intro n ls e ρb ρ houtb hPv hcρ hA
  rw [erwp_opTableN_eq_erwpK A]
  refine erwpK_I_frameT (V := fun _ _ => True) (Φ := fun _ => Φ) (Inv := fun _ => True)
    (flI := fun _ => A) (flO := fun _ => A) (Ti := fun _ => liftTabK T)
    (To := fun _ => liftTabK T') (Q := fun _ => Q) l Ty δ hadm v P hPshape hPloc houtP hclP hds
    (fun _ => hT.liftK) (liftTabK_abort fun m i en h => (hT.entry m i en h).1) (icanK_lift hcan)
    (fun _ _ => ifoldTwin_lift hTT' A l A v ρP ρlP houtP) (liftTabK_ext hQ)
    n () trivial ls e ρb ρ houtb hPv hcρ fun BI hBI => ?_
  have h := hA BI hBI
  rw [erwp_opTableN_eq_erwpK A] at h
  exact h

/-- **Imm Frame at `erwpK` across Kripke stops**, the stops guarded by the fold
(`erwp_I_frameF`). -/
theorem erwpK_I_frameF {V : ι → ι → Prop} {Φ : ι → LocFam} {Inv : ι → Prop} (l : Loc) (Ty : VTy)
    (δ : LSub) (hadm : AdmWf Ty δ) (v : Val) (P : List SRec → Val → WProp)
    (hPshape : ∀ ls ρ, P ls v ρ → vShape Ty δ v ρ)
    (hPloc : ∀ ls₁ ls₂ ρ, extF ls₁ ls₂ ρ → P ls₁ v ρ → P ls₂ v ρ)
    {A : Life} {ρP ρlP : WRes} (houtP : ρP.InStratum A)
    (hclP : ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP)
    {ds : List FrameRec} (hds : ∀ d, d ∈ ds ↔ Desc ⟨l, v, ρP, Ty, δ⟩ d)
    {flI flO : ι → Life} {Ti To : ι → OpTabK ι} (hT : ∀ x, (Ti x).ILendOKCR A)
    (hab : ∀ x m i en, Ti x m i = some en → en.abort = false)
    (hlin : ∀ x m i en, Ti x m i = some en → en.abort = false → en.q = .lin)
    (hTT : ∀ x, Inv x → (Ti x).IFoldTwin Inv (flI x) (flO x) (To x) l A v ρP ρlP houtP)
    {Q : ι → PostN} (hQ : ∀ y k ls₁ ls₂ w ρ, Ext ls₁ ls₂ ρ → Q y k ls₁ w ρ → Q y k ls₂ w ρ) :
    IKFrame (ℍ := ℍ) V Φ Inv l Ty δ v P A ρP ρlP houtP ds (fun y => opTableK (flI y) (Ti y))
      (fun y => opTableGK (flO y) (To y) (ImmFold ρlP)) (fun y => IFPost l v P A (Q y)) Q :=
  IKFrame.conv (TbO := fun y k ls t Ψ => BoLo.or
      (performStopGK (flO y) (To y) (ImmFold ρlP) k ls t Ψ)
      ((fun _ _ _ _ _ _ => False : ι → TableK ι) y k ls t Ψ))
    (erwpK_I_frameGen (RI := fun y => raiseStopK (Ti y))
      (RO := (fun _ _ _ _ _ _ => False : ι → TableK ι))
      (G := fun _ => ImmFold ρlP) l Ty δ hadm v P hPshape hPloc houtP hclP hds hT hTT
      (icanK_of_lin hlin) (fun _ _ _ _ Xi _ hkL => ⟨Xi.del l, ResU.CompS.comm hkL⟩)
      (fun x _ => iraiseFold_absurd (hab x) _) hQ)
    (fun _ => or_local (performStopGK_local _ _ _) (fun _ _ _ _ _ _ h => h)) noRaise

/-- `erwp_I_frameF` from `erwpK_I_frameF`. -/
theorem erwp_I_frameF_of_K {Φ : LocFam} (l : Loc) (T : VTy) (δ : LSub) (hadm : AdmWf T δ)
    (v : Val) (P : List SRec → Val → WProp) (hPshape : ∀ ls ρ, P ls v ρ → vShape T δ v ρ)
    (hPloc : ∀ ls₁ ls₂ ρ, extF ls₁ ls₂ ρ → P ls₁ v ρ → P ls₂ v ρ)
    {A : Life} {Tb : OpTabN} (hT : Tb.ILendOK A) {Q : PostN}
    (hQ : ∀ k ls₁ ls₂ w ρ, Ext ls₁ ls₂ ρ → Q k ls₁ w ρ → Q k ls₂ w ρ) :
    ∀ n ls e (ρP ρlP ρb ρ : WRes) (houtP : ρP.InStratum A), ρb.InStratum A →
      P ls v ρP → ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP → ResU.CompS ρlP ρb ρ →
      ∀ ds, (∀ d, d ∈ ds ↔ Desc ⟨l, v, ρP, T, δ⟩ d) →
      (∀ BI, ResU.CompS ρb (ResU.single l (CellU.immOf (LSet.singleton A) v ρP houtP)) BI →
        erwp (ℍ := ℍ) Φ (opTableN Tb) (IFPost l v P A Q) n (frameList ⟨l, v, ρP, T, δ⟩ ds A ls)
          e BI) →
      erwp (ℍ := ℍ) Φ (opTableG Tb (ImmFold ρlP)) Q n ls e ρ := by
  intro n ls e ρP ρlP ρb ρ houtP houtb hPv hclP hcρ ds hds hA
  rw [erwp_eq_erwpK_of (opTableGK_lift A Tb (ImmFold ρlP)) Φ Q]
  refine erwpK_I_frameF (V := fun _ _ => True) (Φ := fun _ => Φ) (Inv := fun _ => True)
    (flI := fun _ => A) (flO := fun _ => A) (Ti := fun _ => liftTabK Tb)
    (To := fun _ => liftTabK Tb) (Q := fun _ => Q) l T δ hadm v P hPshape hPloc houtP hclP hds
    (fun _ => hT.toR.liftK) (liftTabK_abort fun m i en h => (hT.entry m i en h).1)
    (liftTabK_lin fun m i en h _ => (hT.entry m i en h).2.1)
    (fun _ _ => ifoldTwin_lift (OpTabN.twin_refl Tb) A l A v ρP ρlP houtP) (liftTabK_ext hQ)
    n () trivial ls e ρb ρ houtb hPv hcρ fun BI hBI => ?_
  have h := hA BI hBI
  rw [erwp_opTableN_eq_erwpK A] at h
  exact h

/-- **Imm Frame at `erwpK` across Kripke stops**, over a cancel run (`erwp_I_frame_cancelRun`). -/
theorem erwpK_I_frame_cancelRun {V : ι → ι → Prop} {Φ : ι → LocFam} {Inv : ι → Prop} (l : Loc)
    (Ty : VTy) (δ : LSub) (hadm : AdmWf Ty δ) (v : Val)
    {A : Life} {ρP ρlP : WRes} (houtP : ρP.InStratum A)
    (hclP : ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP)
    {ds : List FrameRec} (hds : ∀ d, d ∈ ds ↔ Desc ⟨l, v, ρP, Ty, δ⟩ d)
    {flI flO : ι → Life} {Ti To : ι → OpTabK ι} (hT : ∀ x, (Ti x).ILendOKCR A)
    (hab : ∀ x m i en, Ti x m i = some en → en.abort = false)
    (hlin : ∀ x m i en, Ti x m i = some en → en.abort = false → en.q = .lin)
    (hTT : ∀ x, Inv x → (Ti x).IFoldTwin Inv (flI x) (flO x) (To x) l A v ρP ρlP houtP) :
    IKFrame (ℍ := ℍ) V Φ Inv l Ty δ v (fun _ _ ρ => vShape Ty δ v ρ) A ρP ρlP houtP ds
      (fun y => cancelTabK (flI y) (Ti y)) (fun y => cancelTabRK (flO y) (To y) (claimI l v ρP))
      (fun _ _ _ _ _ => False) (fun _ _ _ _ _ => False) :=
  IKFrame.postIn (IKFrame.conv (TbO := fun y k ls t Ψ => BoLo.or
      (performStopGK (flO y) (To y) (fun _ _ _ => True) k ls t Ψ)
      (cancelRaiseRK (To y) (claimI l v ρP) k ls t Ψ))
    (erwpK_I_frameGen (RI := fun y => cancelRaiseK (Ti y))
      (RO := fun y => cancelRaiseRK (To y) (claimI l v ρP))
      (G := fun _ _ _ _ => True) (Q := fun _ _ _ _ _ => False) l Ty δ hadm v
      (fun _ _ ρ => vShape Ty δ v ρ) (fun _ _ h => h) (fun _ _ _ _ h => h) houtP hclP hds hT hTT
      (icanK_of_lin hlin) (by intros; trivial) (fun x _ => icancelFold_claim hclP (hab x))
      (fun _ _ _ _ _ _ _ h => h))
    (fun _ => or_local (performStopGK_local _ _ _) (cancelRaiseRK_free _ _)) unguard)
    (fun _ => or_local (performStopK_local _ _) (cancelRaiseK_free _)) (fun _ _ _ _ _ h => h.elim)

/-- `erwp_I_frame_cancelRun` from `erwpK_I_frame_cancelRun`. -/
theorem erwp_I_frame_cancelRun_of_K {Φ : LocFam} (l : Loc) (T : VTy) (δ : LSub)
    (hadm : AdmWf T δ) (v : Val) {A : Life} {Tb : OpTabN} (hT : Tb.ILendOK A) :
    ∀ n ls e (ρP ρlP ρb ρ : WRes) (houtP : ρP.InStratum A), ρb.InStratum A →
      vShape T δ v ρP → ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP →
      ResU.CompS ρlP ρb ρ → ∀ ds,
      (∀ d, d ∈ ds ↔ Desc ⟨l, v, ρP, T, δ⟩ d) →
      (∀ BI, ResU.CompS ρb (ResU.single l (CellU.immOf (LSet.singleton A) v ρP houtP)) BI →
        erwp (ℍ := ℍ) Φ (cancelTabN Tb) (fun _ _ _ _ => False) n
          (frameList ⟨l, v, ρP, T, δ⟩ ds A ls) e BI) →
      erwp (ℍ := ℍ) Φ (cancelTabR Tb (claimI l v ρP)) (fun _ _ _ _ => False) n ls e ρ := by
  intro n ls e ρP ρlP ρb ρ houtP houtb hshape hclP hcρ ds hds hA
  rw [erwp_eq_erwpK_of (cancelTabRK_lift A Tb (claimI l v ρP)) Φ _]
  refine erwpK_I_frame_cancelRun (V := fun _ _ => True) (Φ := fun _ => Φ) (Inv := fun _ => True)
    (flI := fun _ => A) (flO := fun _ => A) (Ti := fun _ => liftTabK Tb)
    (To := fun _ => liftTabK Tb) l T δ hadm v houtP hclP hds
    (fun _ => hT.toR.liftK) (liftTabK_abort fun m i en h => (hT.entry m i en h).1)
    (liftTabK_lin fun m i en h _ => (hT.entry m i en h).2.1)
    (fun _ _ => ifoldTwin_lift (OpTabN.twin_refl Tb) A l A v ρP ρlP houtP)
    n () trivial ls e ρb ρ houtb hshape hcρ fun BI hBI => ?_
  have h := hA BI hBI
  rw [erwp_eq_erwpK_of (cancelTabK_lift A Tb) _ _] at h
  exact h

/-! ### At the typed world -/

/-- **The Imm Frame at the typed world** (`erwpK_I_frameT` at `KW`). The borrowed run's entries
owe along `KW.Owed` at the lend's world (`KW.lendImm`) at the floor bound `A`; the lender's, along
`KW.Owed` at its own world at its floor; the frame's invariant is `FoldInv A`. `IFoldTwin` is
`ifoldTwin_owed`. -/
theorem erwpK_I_frameT_KW {V : KW → KW → Prop} {Φ : KW → LocFam} (l : Loc) (Ty : VTy)
    (δ : LSub) (hadm : AdmWf Ty δ) (v : Val) (P : List SRec → Val → WProp)
    (hPshape : ∀ ls ρ, P ls v ρ → vShape Ty δ v ρ)
    (hPloc : ∀ ls₁ ls₂ ρ, extF ls₁ ls₂ ρ → P ls₁ v ρ → P ls₂ v ρ)
    {A : Life} {ρP ρlP : WRes} (houtP : ρP.InStratum A)
    (hclP : ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP)
    {ds : List FrameRec} (hds : ∀ d, d ∈ ds ↔ Desc ⟨l, v, ρP, Ty, δ⟩ d)
    {Ti To : KW → OpTabK KW} (hT : ∀ x, (Ti x).ILendOKCR A)
    (hab : ∀ x m i en, Ti x m i = some en → en.abort = false)
    (hcan : ICanK (fun y => y.Θ.FoldInv A) Ti To l Ty δ A v ρP ρlP houtP ds)
    (hTw : ∀ x, x.Θ.FoldInv A → ∀ m i en, Ti x m i = some en → ∃ en', To x m i = some en' ∧
      en'.q = en.q ∧ en'.abort = en.abort ∧ en'.PA = en.PA ∧ en'.PB = en.PB ∧ en'.wc = en.wc ∧
      (en.abort = false →
        (∀ f z ρ, (x.lendImm ⟨l, v, ρP, Ty, δ⟩ A).Owed f (z.lendImm ⟨l, v, ρP, Ty, δ⟩ A) ρ →
          en.wk f z ρ) ∧
        (∀ f z ρ, en'.wk f z ρ → x.Owed f z ρ)))
    {Q : KW → PostN} (hQ : ∀ y k ls₁ ls₂ w ρ, Ext ls₁ ls₂ ρ → Q y k ls₁ w ρ → Q y k ls₂ w ρ) :
    IKFrame (ℍ := ℍ) V Φ (fun y => y.Θ.FoldInv A) l Ty δ v P A ρP ρlP houtP ds
      (fun y => opTableK A (Ti y)) (fun y => opTableK y.lo (To y))
      (fun y => IFPost l v P A (Q y)) Q :=
  erwpK_I_frameT (flI := fun _ => A) (flO := fun y => y.lo) l Ty δ hadm v P hPshape hPloc houtP
    hclP hds hT hab hcan (fun x hx => ifoldTwin_owed hx (hTw x hx)) hQ

end BoCa.Fig16.LogRel.Core.Chain.SI

end
