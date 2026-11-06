import Core.Chain.SI.MFrameK
import Core.Chain.FamCancel836N
import Core.Chain.SI.AntiCancelN

/-!
# The `mut` lend frames at `erwpK`  `[spec §19, §27, §62]`

`docs/new-core/scope-835-mframes.md`. Each Mut Frame across stops, restated at `erwpK` over any
world index (`erwpK_M_frame*`), as an instance of `erwpK_M_frameGen` (`SI/MFrameK.lean`); and its
`erwp` statement, word for word, proved again from the restated frame at one world
(`erwp_M_frame*_of_K`).

At a world index the borrowed run and the lender stop at different tables (`Ti`, `To`): the
borrowed run's entries owe at the lend's world, the lender's at its own, and `OpTabK.FoldTwin`
relates them across the fold (`foldTwin_owed` at `KW`). At one world both are the lifted table
and `FoldTwin` holds of a twin (`foldTwin_lift`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Head Kont performE raiseE cancelVal opPayload)

variable {ι : Type}

/-! ### The frame's shape -/

/-- **A Mut Frame at `erwpK`**: a lend at `ℓ`, `A`, `F` of `ℓ ↦ v ⋆ ρ_P` beside `ρ_b`, to a
computation in `erwpK` at `Φ[ℓ ↦ (A, F)]` at the tables `TbI` and the post `QI`, at a world where
`Inv` holds: the computation is in `erwpK` at `Φ` at the tables `TbO` and the post `Q`. -/
def KFrame (V : ι → ι → Prop) (Φ : ι → LocFam) (Inv : ι → Prop) (l : Loc) (A : Life)
    (F : Nat → Val → SPropS Loc Val A) (TbI TbO : ι → TableK ι) (QI Q : ι → PostN) : Prop :=
  ∀ n j, n ≤ j → ∀ (x : ι), Inv x → ∀ ls e (v : Val) (ρP ρlP ρb ρ : WRes)
    (houtP : ρP.InStratum A), ρb.InStratum (↓A) → ∀ (P : Val → SPropS Loc Val A),
    (∀ u r, SPropS.toU (P u) r → SPropS.toU (F j u) r) → ∀ (hwit : P v ⟨ρP, houtP⟩),
    ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP → ResU.CompS ρlP ρb ρ →
    (∀ BM, ResU.CompS ρb (ResU.single l (CellU.mutOf A v ρP houtP P hwit)) BM →
      erwpK (ℍ := ℍ) V (fun y => (Φ y).set l A F) TbI QI x n ls e BM) →
    erwpK (ℍ := ℍ) V Φ TbO Q x n ls e ρ

/-- A frame at one outer table is a frame at every table allowing its stops. -/
theorem KFrame.conv {V : ι → ι → Prop} {Φ : ι → LocFam} {Inv : ι → Prop} {l : Loc} {A : Life}
    {F : Nat → Val → SPropS Loc Val A} {TbI TbO TbO' : ι → TableK ι} {QI Q : ι → PostN}
    (h : KFrame (ℍ := ℍ) V Φ Inv l A F TbI TbO QI Q) (hL : ∀ x, (TbO x).Local)
    (hc : ∀ x k ls t Ψ ρ, TbO x k ls t Ψ ρ → TbO' x k ls t Ψ ρ) :
    KFrame (ℍ := ℍ) V Φ Inv l A F TbI TbO' QI Q := by
  intro n j hjn x hx ls e v ρP ρlP ρb ρ houtP houtb P hPF hwit hclP hcρ hA
  exact erwpK_mono (fun _ _ h => h) (fun _ _ _ _ _ h => h)
    (fun x k ls t Ψ Ψ' ρ hΨ hT => hc x k ls t Ψ' ρ (hL x k ls t Ψ Ψ' ρ hΨ hT)) n x ls e ρ
    (h n j hjn x hx ls e v ρP ρlP ρb ρ houtP houtb P hPF hwit hclP hcρ hA)

/-- A frame for one borrowed post is a frame for every post inside it. -/
theorem KFrame.postIn {V : ι → ι → Prop} {Φ : ι → LocFam} {Inv : ι → Prop} {l : Loc} {A : Life}
    {F : Nat → Val → SPropS Loc Val A} {TbI TbO : ι → TableK ι} {QI QI' Q : ι → PostN}
    (h : KFrame (ℍ := ℍ) V Φ Inv l A F TbI TbO QI Q) (hL : ∀ x, (TbI x).Local)
    (hQ : ∀ y k ls v ρ, QI' y k ls v ρ → QI y k ls v ρ) :
    KFrame (ℍ := ℍ) V Φ Inv l A F TbI TbO QI' Q := by
  intro n j hjn x hx ls e v ρP ρlP ρb ρ houtP houtb P hPF hwit hclP hcρ hA
  exact h n j hjn x hx ls e v ρP ρlP ρb ρ houtP houtb P hPF hwit hclP hcρ fun BM hBM =>
    erwpK_mono (fun _ _ h => h) hQ (fun x k ls t Ψ Ψ' ρ hΨ h => hL x k ls t Ψ Ψ' ρ hΨ h) n x ls
      e BM (hA BM hBM)

/-- The lender's stop with no guard. -/
theorem unguard {fl : ι → Life} {T : ι → OpTabK ι} {RO : ι → TableK ι} (x : ι) (k : Nat)
    (ls : List SRec) (t : Expr) (Ψ : ContK ι) (ρ : WRes)
    (h : BoLo.or (performStopGK (fl x) (T x) (fun _ _ _ => True) k ls t Ψ) (RO x k ls t Ψ) ρ) :
    BoLo.or (performStopK (fl x) (T x) k ls t Ψ) (RO x k ls t Ψ) ρ :=
  h.imp_left (performStopGK_true_iff _ _ _ _ _ _ _).mp

/-- The lender's guarded stop with no raise. -/
theorem noRaise {fl : ι → Life} {T : ι → OpTabK ι} {G : ι → ShareG} (x : ι) (k : Nat)
    (ls : List SRec) (t : Expr) (Ψ : ContK ι) (ρ : WRes)
    (h : BoLo.or (performStopGK (fl x) (T x) (G x) k ls t Ψ)
      ((fun _ _ _ _ _ _ => False : ι → TableK ι) x k ls t Ψ) ρ) :
    performStopGK (fl x) (T x) (G x) k ls t Ψ ρ :=
  h.elim id False.elim

/-- **The cancel obligations across the fold**: a cancellable stop's, the borrowed run's at the
borrowed share, is the lender's at the lender's share, at every resumption world. -/
def CanFold (Inv : ι → Prop) (Ti To : ι → OpTabK ι) (l : Loc) (A : Life)
    (F : Nat → Val → SPropS Loc Val A) : Prop :=
  ∀ x, Inv x → ∀ m i en en', Ti x m i = some en → To x m i = some en' →
    en.abort = false → en.q ≠ .lin →
    ∀ y k ls (K : Kont) (ρk ρp Z ρkL W'' : WRes) (v'' : Val) (χ : WRes)
      (hχ : χ.InStratum A) (P'' : Val → SPropS Loc Val A) (hw'' : P'' v'' ⟨χ, hχ⟩),
      NoOwn ρp → ResU.CompS ρk ρp Z →
      ResU.CompS (Z.del l) (ResU.single l (CellU.mutOf A v'' χ hχ P'' hw'')) Z →
      (Z.del l).InStratum (↓A) →
      (∀ u r, SPropS.toU (P'' u) r → SPropS.toU (F k u) r) →
      ResU.CompS χ (ResU.single l (CellU.ownOf v'')) W'' → ResU.CompS (Z.del l) W'' ρkL →
      cancelOKK en y k ls K ρk → cancelOKK en' y k ls K ρkL

/-- A table of must-resume stops has no cancel obligation to carry. -/
theorem canFold_of_lin {Inv : ι → Prop} {Ti To : ι → OpTabK ι} {l : Loc} {A : Life}
    {F : Nat → Val → SPropS Loc Val A}
    (hlin : ∀ x m i en, Ti x m i = some en → en.abort = false → en.q = .lin) :
    CanFold Inv Ti To l A F := by
  intro x _ m i en _ hT _ ha hq
  exact absurd (hlin x m i en hT ha) hq

/-- `erwp_M_frameCR`'s `hcan` at one world. -/
theorem canFold_lift {T T' : OpTabN} {l : Loc} {A : Life} {F : Nat → Val → SPropS Loc Val A}
    (hcan : ∀ m i en en', T m i = some en → T' m i = some en' → en.abort = false →
      en.q ≠ .lin →
      ∀ k ls (K : Kont) (ρk ρp Z ρkL W'' : WRes) (v'' : Val) (χ : WRes) (hχ : χ.InStratum A)
        (P'' : Val → SPropS Loc Val A) (hw'' : P'' v'' ⟨χ, hχ⟩),
        NoOwn ρp → ResU.CompS ρk ρp Z →
        ResU.CompS (Z.del l) (ResU.single l (CellU.mutOf A v'' χ hχ P'' hw'')) Z →
        (Z.del l).InStratum (↓A) →
        (∀ u r, SPropS.toU (P'' u) r → SPropS.toU (F k u) r) →
        ResU.CompS χ (ResU.single l (CellU.ownOf v'')) W'' → ResU.CompS (Z.del l) W'' ρkL →
        cancelOKN en k ls K ρk → cancelOKN en' k ls K ρkL) :
    CanFold (fun _ : Unit => True) (fun _ => liftTabK T) (fun _ => liftTabK T') l A F := by
  intro _ _ m i en en' hT hT' ha hq _ k ls K ρk ρp Z ρkL W'' v'' χ hχ P'' hw'' hno hZ hZd hdZd
    hPk hW'' hkL
  obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some hT
  obtain ⟨en₀', h₀', rfl⟩ := liftTabK_some hT'
  exact cancelOKK_lift_conv (hcan m i en₀ en₀' h₀ h₀' ha hq k ls K ρk ρp Z ρkL W'' v'' χ hχ P''
    hw'' hno hZ hZd hdZd hPk hW'' hkL)

theorem OpTabN.twin_refl (T : OpTabN) : T.Twin T :=
  fun _ _ en h => ⟨en, h, rfl, rfl, rfl, rfl, rfl⟩

theorem OpTabN.LendOK.toCR {T : OpTabN} {A : Life} (h : T.LendOK A) : T.LendOKCR A :=
  ⟨fun m i en hT _ => ⟨by rw [(h.entry m i en hT).2.1]; decide, (h.entry m i en hT).2.2⟩,
    h.pa, h.pb⟩

theorem OpTabN.LendOKR.toCR {T : OpTabN} {A : Life} (h : T.LendOKR A) : T.LendOKCR A :=
  ⟨fun m i en hT ha => ⟨by rw [(h.entry m i en hT ha).1]; decide, (h.entry m i en hT ha).2⟩,
    h.pa, h.pb⟩

theorem OpTabN.LendOKC.toCR {T : OpTabN} {A : Life} (h : T.LendOKC A) : T.LendOKCR A :=
  ⟨fun m i en hT _ => (h.entry m i en hT).2, h.pa, h.pb⟩

theorem liftTabK_abort {T : OpTabN} (h : ∀ m i en, T m i = some en → en.abort = false) :
    ∀ (_ : Unit) m i en, liftTabK T m i = some en → en.abort = false := by
  intro _ m i en hT
  obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some hT
  exact h m i en₀ h₀

theorem liftTabK_lin {T : OpTabN}
    (h : ∀ m i en, T m i = some en → en.abort = false → en.q = .lin) :
    ∀ (_ : Unit) m i en, liftTabK T m i = some en → en.abort = false → en.q = .lin := by
  intro _ m i en hT
  obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some hT
  exact h m i en₀ h₀

theorem liftTabK_pa {T : OpTabN} {A : Life}
    (h : ∀ m i en, T m i = some en → ∀ k ls v (ρ : WRes), en.PA k ls v ρ → ρ.InStratum A) :
    ∀ m i en, liftTabK T m i = some en → ∀ k ls v (ρ : WRes), en.PA k ls v ρ →
      ρ.InStratum A := by
  intro m i en hT
  obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some hT
  exact h m i en₀ h₀

theorem OpTabN.Twin.lift {T T' : OpTabN} (h : T.Twin T') : (liftTabK T).Twin (liftTabK T') :=
  (foldTwin_lift h (↓0) 0 (↓0)).twin

/-- Every raise table here reads no continuation. -/
theorem raiseStopK_free (T : OpTabK ι) : ∀ k ls t (Ψ Ψ' : ContK ι) ρ,
    raiseStopK T k ls t Ψ ρ → raiseStopK T k ls t Ψ' ρ := fun _ _ _ _ _ _ h => h

theorem raiseStopRK_free (T : OpTabK ι) (R : Nat → WProp) : ∀ k ls t (Ψ Ψ' : ContK ι) ρ,
    raiseStopRK T R k ls t Ψ ρ → raiseStopRK T R k ls t Ψ' ρ := fun _ _ _ _ _ _ h => h

theorem cancelRaiseRK_free (T : OpTabK ι) (R : Nat → WProp) : ∀ k ls t (Ψ Ψ' : ContK ι) ρ,
    cancelRaiseRK T R k ls t Ψ ρ → cancelRaiseRK T R k ls t Ψ' ρ := fun _ _ _ _ _ _ h => h

theorem cancelRaiseK_free (T : OpTabK ι) : ∀ k ls t (Ψ Ψ' : ContK ι) ρ,
    cancelRaiseK T k ls t Ψ ρ → cancelRaiseK T k ls t Ψ' ρ := fun _ _ _ _ _ _ h => h

theorem performStopK_local (lo : Life) (T : OpTabK ι) : (performStopK lo T).Local := by
  intro k ls t Ψ Ψ' ρ hΨ h
  exact ((performStopGK_true_iff lo T k ls t Ψ' ρ).mp (performStopGK_local lo T _ k ls t Ψ Ψ' ρ hΨ
    ((performStopGK_true_iff lo T k ls t Ψ ρ).mpr h)))

/-! ### `erwp_M_frame` -/

/-- **Mut Frame at `erwpK` across Kripke stops** (`erwp_M_frame`): a table of must-resume stops
and no raise. -/
theorem erwpK_M_frame {V : ι → ι → Prop} {Φ : ι → LocFam} {Inv : ι → Prop} {l : Loc} {A : Life}
    {F : Nat → Val → SPropS Loc Val A} (hF : DownFam A F) {flI flO : ι → Life}
    {Ti To : ι → OpTabK ι} (hT : ∀ x, (Ti x).LendOKCR A)
    (hab : ∀ x m i en, Ti x m i = some en → en.abort = false)
    (hlin : ∀ x m i en, Ti x m i = some en → en.abort = false → en.q = .lin)
    (hTT : ∀ x, Inv x → (Ti x).FoldTwin Inv (flI x) (flO x) (To x) l A) {Q : ι → PostN} :
    KFrame (ℍ := ℍ) V Φ Inv l A F (fun y => opTableK (flI y) (Ti y))
      (fun y => opTableK (flO y) (To y)) (fun y => MFPost l A F (Q y)) Q :=
  KFrame.conv (TbO := fun y k ls t Ψ => BoLo.or
      (performStopGK (flO y) (To y) (fun _ _ _ => True) k ls t Ψ) (raiseStopK (To y) k ls t Ψ))
    (erwpK_M_frameGen (RI := fun y => raiseStopK (Ti y)) (RO := fun y => raiseStopK (To y)) hF hT
      hTT (canFold_of_lin hlin) (by intros; trivial)
      (fun x _ => raiseFold_absurd (hab x) _))
    (fun x => or_local (performStopGK_local _ _ _) (raiseStopK_free _)) unguard

/-- `erwp_M_frame` from `erwpK_M_frame`. -/
theorem erwp_M_frame_of_K {Φ : LocFam} {l : Loc} {A : Life} {F : Nat → Val → SPropS Loc Val A}
    (hF : DownFam A F) {T : OpTabN} (hT : T.LendOK A) {Q : PostN} :
    ∀ n j, n ≤ j → ∀ ls e (v : Val) (ρP ρlP ρb ρ : WRes) (houtP : ρP.InStratum A),
      ρb.InStratum (↓A) → ∀ (P : Val → SPropS Loc Val A),
      (∀ u r, SPropS.toU (P u) r → SPropS.toU (F j u) r) → ∀ (hwit : P v ⟨ρP, houtP⟩),
      ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP → ResU.CompS ρlP ρb ρ →
      (∀ BM, ResU.CompS ρb (ResU.single l (CellU.mutOf A v ρP houtP P hwit)) BM →
        erwp (ℍ := ℍ) (Φ.set l A F) (opTableN T) (MFPost l A F Q) n ls e BM) →
      erwp (ℍ := ℍ) Φ (opTableN T) Q n ls e ρ := by
  intro n j hjn ls e v ρP ρlP ρb ρ houtP houtb P hPF hwit hclP hcρ hA
  rw [erwp_opTableN_eq_erwpK A]
  refine erwpK_M_frame (V := fun _ _ => True) (Φ := fun _ => Φ) (Inv := fun _ => True)
    (flI := fun _ => A) (flO := fun _ => A) (Ti := fun _ => liftTabK T)
    (To := fun _ => liftTabK T) (Q := fun _ => Q) hF (fun _ => hT.toCR.lift)
    (liftTabK_abort fun m i en h => (hT.entry m i en h).1)
    (liftTabK_lin fun m i en h _ => (hT.entry m i en h).2.1)
    (fun _ _ => foldTwin_lift (OpTabN.twin_refl T) A l A) n j hjn () trivial ls e v ρP ρlP ρb ρ
    houtP houtb P hPF hwit hclP hcρ fun BM hBM => ?_
  have h := hA BM hBM
  rw [erwp_opTableN_eq_erwpK A] at h
  exact h

/-! ### The other variants -/

/-- **Mut Frame at `erwpK` across Kripke stops**, raises carrying the claim (`erwp_M_frameR`). -/
theorem erwpK_M_frameR {V : ι → ι → Prop} {Φ : ι → LocFam} {Inv : ι → Prop} {l : Loc} {A : Life}
    {F : Nat → Val → SPropS Loc Val A} (hF : DownFam A F) {flI flO : ι → Life}
    {Ti To : ι → OpTabK ι} (hT : ∀ x, (Ti x).LendOKCR A)
    (hlin : ∀ x m i en, Ti x m i = some en → en.abort = false → en.q = .lin)
    (hTT : ∀ x, Inv x → (Ti x).FoldTwin Inv (flI x) (flO x) (To x) l A) {Q : ι → PostN} :
    KFrame (ℍ := ℍ) V Φ Inv l A F (fun y => opTableK (flI y) (Ti y))
      (fun y => opTableRK (flO y) (To y) (claimR l A F)) (fun y => MFPost l A F (Q y)) Q :=
  KFrame.conv (TbO := fun y k ls t Ψ => BoLo.or
      (performStopGK (flO y) (To y) (fun _ _ _ => True) k ls t Ψ)
      (raiseStopRK (To y) (claimR l A F) k ls t Ψ))
    (erwpK_M_frameGen (RI := fun y => raiseStopK (Ti y))
      (RO := fun y => raiseStopRK (To y) (claimR l A F))
      (G := fun _ _ _ _ => True) hF hT hTT (canFold_of_lin hlin)
      (by intros; trivial)
      (fun x hx => raiseFold_claim (hTT x hx).twin (hT x).pa))
    (fun _ => or_local (performStopGK_local _ _ _) (raiseStopRK_free _ _)) (unguard)

/-- `erwp_M_frameR` from `erwpK_M_frameR`. -/
theorem erwp_M_frameR_of_K {Φ : LocFam} {l : Loc} {A : Life} {F : Nat → Val → SPropS Loc Val A}
    (hF : DownFam A F) {T : OpTabN} (hT : T.LendOKR A) {Q : PostN} :
    ∀ n j, n ≤ j → ∀ ls e (v : Val) (ρP ρlP ρb ρ : WRes) (houtP : ρP.InStratum A),
      ρb.InStratum (↓A) → ∀ (P : Val → SPropS Loc Val A),
      (∀ u r, SPropS.toU (P u) r → SPropS.toU (F j u) r) → ∀ (hwit : P v ⟨ρP, houtP⟩),
      ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP → ResU.CompS ρlP ρb ρ →
      (∀ BM, ResU.CompS ρb (ResU.single l (CellU.mutOf A v ρP houtP P hwit)) BM →
        erwp (ℍ := ℍ) (Φ.set l A F) (opTableN T) (MFPost l A F Q) n ls e BM) →
      erwp (ℍ := ℍ) Φ (opTableR T (claimR l A F)) Q n ls e ρ := by
  intro n j hjn ls e v ρP ρlP ρb ρ houtP houtb P hPF hwit hclP hcρ hA
  rw [erwp_eq_erwpK_of (opTableRK_lift A T (claimR l A F)) Φ Q]
  refine erwpK_M_frameR (V := fun _ _ => True) (Φ := fun _ => Φ) (Inv := fun _ => True)
    (flI := fun _ => A) (flO := fun _ => A) (Ti := fun _ => liftTabK T)
    (To := fun _ => liftTabK T) (Q := fun _ => Q) hF
    (fun _ => hT.toCR.lift)
    (liftTabK_lin fun m i en h ha => (hT.entry m i en h ha).1)
    (fun _ _ => foldTwin_lift (OpTabN.twin_refl T) A l A) n j hjn () trivial ls e v ρP ρlP ρb ρ houtP houtb
    P hPF hwit hclP hcρ fun BM hBM => ?_
  have h := hA BM hBM
  rw [erwp_opTableN_eq_erwpK A] at h
  exact h

/-- **Mut Frame at `erwpK` across Kripke stops**, cancellable stops (`erwp_M_frameT`). -/
theorem erwpK_M_frameT {V : ι → ι → Prop} {Φ : ι → LocFam} {Inv : ι → Prop} {l : Loc} {A : Life}
    {F : Nat → Val → SPropS Loc Val A} (hF : DownFam A F) {flI flO : ι → Life}
    {Ti To : ι → OpTabK ι} (hT : ∀ x, (Ti x).LendOKCR A)
    (hab : ∀ x m i en, Ti x m i = some en → en.abort = false)
    (hcan : CanFold Inv Ti To l A F)
    (hTT : ∀ x, Inv x → (Ti x).FoldTwin Inv (flI x) (flO x) (To x) l A) {Q : ι → PostN} :
    KFrame (ℍ := ℍ) V Φ Inv l A F (fun y => opTableK (flI y) (Ti y))
      (fun y => opTableK (flO y) (To y)) (fun y => MFPost l A F (Q y)) Q :=
  KFrame.conv (TbO := fun y k ls t Ψ => BoLo.or
      (performStopGK (flO y) (To y) (fun _ _ _ => True) k ls t Ψ)
      (raiseStopK (To y) k ls t Ψ))
    (erwpK_M_frameGen (RI := fun y => raiseStopK (Ti y))
      (RO := fun y => raiseStopK (To y))
      (G := fun _ _ _ _ => True) hF hT hTT hcan
      (by intros; trivial)
      (fun x _ => raiseFold_absurd (hab x) _))
    (fun _ => or_local (performStopGK_local _ _ _) (raiseStopK_free _)) (unguard)

/-- `erwp_M_frameT` from `erwpK_M_frameT`. -/
theorem erwp_M_frameT_of_K {Φ : LocFam} {l : Loc} {A : Life} {F : Nat → Val → SPropS Loc Val A}
    (hF : DownFam A F) {T T' : OpTabN} (hT : T.LendOKC A) (hTT' : T.Twin T')
    (hcan : ∀ m i en en', T m i = some en → T' m i = some en' → en.q ≠ .lin →
      ∀ k ls (K : Kont) (ρk ρp Z ρkL W'' : WRes) (v'' : Val) (χ : WRes) (hχ : χ.InStratum A)
        (P'' : Val → SPropS Loc Val A) (hw'' : P'' v'' ⟨χ, hχ⟩),
        NoOwn ρp → ResU.CompS ρk ρp Z →
        ResU.CompS (Z.del l) (ResU.single l (CellU.mutOf A v'' χ hχ P'' hw'')) Z →
        (Z.del l).InStratum (↓A) →
        (∀ u r, SPropS.toU (P'' u) r → SPropS.toU (F k u) r) →
        ResU.CompS χ (ResU.single l (CellU.ownOf v'')) W'' → ResU.CompS (Z.del l) W'' ρkL →
        cancelOKN en k ls K ρk → cancelOKN en' k ls K ρkL)
    {Q : PostN} :
    ∀ n j, n ≤ j → ∀ ls e (v : Val) (ρP ρlP ρb ρ : WRes) (houtP : ρP.InStratum A),
      ρb.InStratum (↓A) → ∀ (P : Val → SPropS Loc Val A),
      (∀ u r, SPropS.toU (P u) r → SPropS.toU (F j u) r) → ∀ (hwit : P v ⟨ρP, houtP⟩),
      ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP → ResU.CompS ρlP ρb ρ →
      (∀ BM, ResU.CompS ρb (ResU.single l (CellU.mutOf A v ρP houtP P hwit)) BM →
        erwp (ℍ := ℍ) (Φ.set l A F) (opTableN T) (MFPost l A F Q) n ls e BM) →
      erwp (ℍ := ℍ) Φ (opTableN T') Q n ls e ρ := by
  intro n j hjn ls e v ρP ρlP ρb ρ houtP houtb P hPF hwit hclP hcρ hA
  rw [erwp_opTableN_eq_erwpK A]
  refine erwpK_M_frameT (V := fun _ _ => True) (Φ := fun _ => Φ) (Inv := fun _ => True)
    (flI := fun _ => A) (flO := fun _ => A) (Ti := fun _ => liftTabK T)
    (To := fun _ => liftTabK T') (Q := fun _ => Q) hF
    (fun _ => hT.toCR.lift)
    (liftTabK_abort fun m i en h => (hT.entry m i en h).1)
    (canFold_lift fun m i en en' h h' _ hq => hcan m i en en' h h' hq)
    (fun _ _ => foldTwin_lift (hTT') A l A) n j hjn () trivial ls e v ρP ρlP ρb ρ houtP houtb
    P hPF hwit hclP hcρ fun BM hBM => ?_
  have h := hA BM hBM
  rw [erwp_opTableN_eq_erwpK A] at h
  exact h

/-- **Mut Frame at `erwpK` across Kripke stops**, over a cancel run (`erwp_M_frame_cancelRun`). -/
theorem erwpK_M_frame_cancelRun {V : ι → ι → Prop} {Φ : ι → LocFam} {Inv : ι → Prop} {l : Loc} {A : Life}
    {F : Nat → Val → SPropS Loc Val A} (hF : DownFam A F) {flI flO : ι → Life}
    {Ti To : ι → OpTabK ι} (hT : ∀ x, (Ti x).LendOKCR A)
    (hlin : ∀ x m i en, Ti x m i = some en → en.abort = false → en.q = .lin)
    (hTT : ∀ x, Inv x → (Ti x).FoldTwin Inv (flI x) (flO x) (To x) l A) :
    KFrame (ℍ := ℍ) V Φ Inv l A F (fun y => cancelTabK (flI y) (Ti y))
      (fun y => cancelTabRK (flO y) (To y) (claimR l A F)) (fun _ _ _ _ _ => False) (fun _ _ _ _ _ => False) :=
  KFrame.postIn (KFrame.conv (TbO := fun y k ls t Ψ => BoLo.or
      (performStopGK (flO y) (To y) (fun _ _ _ => True) k ls t Ψ)
      (cancelRaiseRK (To y) (claimR l A F) k ls t Ψ))
    (erwpK_M_frameGen (RI := fun y => cancelRaiseK (Ti y))
      (RO := fun y => cancelRaiseRK (To y) (claimR l A F))
      (G := fun _ _ _ _ => True) (Q := fun _ _ _ _ _ => False) hF hT hTT (canFold_of_lin hlin)
      (by intros; trivial)
      (fun x hx => cancelFold_claim (hTT x hx).twin (hT x).pa))
    (fun _ => or_local (performStopGK_local _ _ _) (cancelRaiseRK_free _ _)) (unguard))
    (fun _ => or_local (performStopK_local _ _) (cancelRaiseK_free _)) (fun _ _ _ _ _ h => h.elim)

/-- `erwp_M_frame_cancelRun` from `erwpK_M_frame_cancelRun`. -/
theorem erwp_M_frame_cancelRun_of_K {Φ : LocFam} {l : Loc} {A : Life}
    {F : Nat → Val → SPropS Loc Val A} (hF : DownFam A F) {T : OpTabN} (hT : T.LendOK A) :
    ∀ n j, n ≤ j → ∀ ls e (v : Val) (ρP ρlP ρb ρ : WRes) (houtP : ρP.InStratum A),
      ρb.InStratum (↓A) → ∀ (P : Val → SPropS Loc Val A),
      (∀ u r, SPropS.toU (P u) r → SPropS.toU (F j u) r) → ∀ (hwit : P v ⟨ρP, houtP⟩),
      ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP → ResU.CompS ρlP ρb ρ →
      (∀ BM, ResU.CompS ρb (ResU.single l (CellU.mutOf A v ρP houtP P hwit)) BM →
        erwp (ℍ := ℍ) (Φ.set l A F) (cancelTabN T) (fun _ _ _ _ => False) n ls e BM) →
      erwp (ℍ := ℍ) Φ (cancelTabR T (claimR l A F)) (fun _ _ _ _ => False) n ls e ρ := by
  intro n j hjn ls e v ρP ρlP ρb ρ houtP houtb P hPF hwit hclP hcρ hA
  rw [erwp_eq_erwpK_of (cancelTabRK_lift A T (claimR l A F)) Φ _]
  refine erwpK_M_frame_cancelRun (V := fun _ _ => True) (Φ := fun _ => Φ) (Inv := fun _ => True)
    (flI := fun _ => A) (flO := fun _ => A) (Ti := fun _ => liftTabK T)
    (To := fun _ => liftTabK T) hF
    (fun _ => hT.toCR.lift)
    (liftTabK_lin fun m i en h _ => (hT.entry m i en h).2.1)
    (fun _ _ => foldTwin_lift (OpTabN.twin_refl T) A l A) n j hjn () trivial ls e v ρP ρlP ρb ρ houtP houtb
    P hPF hwit hclP hcρ fun BM hBM => ?_
  have h := hA BM hBM
  rw [erwp_eq_erwpK_of (cancelTabK_lift A T) _ _] at h
  exact h

/-- **Mut Frame at `erwpK` across Kripke stops**, raises, must-resume and cancellable stops (`erwp_M_frameCR`). -/
theorem erwpK_M_frameCR {V : ι → ι → Prop} {Φ : ι → LocFam} {Inv : ι → Prop} {l : Loc} {A : Life}
    {F : Nat → Val → SPropS Loc Val A} (hF : DownFam A F) {flI flO : ι → Life}
    {Ti To : ι → OpTabK ι} (hT : ∀ x, (Ti x).LendOKCR A)
    (hcan : CanFold Inv Ti To l A F)
    (hTT : ∀ x, Inv x → (Ti x).FoldTwin Inv (flI x) (flO x) (To x) l A) {Q : ι → PostN} :
    KFrame (ℍ := ℍ) V Φ Inv l A F (fun y => opTableK (flI y) (Ti y))
      (fun y => opTableRK (flO y) (To y) (claimR l A F)) (fun y => MFPost l A F (Q y)) Q :=
  KFrame.conv (TbO := fun y k ls t Ψ => BoLo.or
      (performStopGK (flO y) (To y) (fun _ _ _ => True) k ls t Ψ)
      (raiseStopRK (To y) (claimR l A F) k ls t Ψ))
    (erwpK_M_frameGen (RI := fun y => raiseStopK (Ti y))
      (RO := fun y => raiseStopRK (To y) (claimR l A F))
      (G := fun _ _ _ _ => True) hF hT hTT hcan
      (by intros; trivial)
      (fun x hx => raiseFold_claim (hTT x hx).twin (hT x).pa))
    (fun _ => or_local (performStopGK_local _ _ _) (raiseStopRK_free _ _)) (unguard)

/-- `erwp_M_frameCR` from `erwpK_M_frameCR`. -/
theorem erwp_M_frameCR_of_K {Φ : LocFam} {l : Loc} {A : Life} {F : Nat → Val → SPropS Loc Val A}
    (hF : DownFam A F) {T T' : OpTabN} (hT : T.LendOKCR A) (hTT' : T.Twin T')
    (hcan : ∀ m i en en', T m i = some en → T' m i = some en' → en.abort = false →
      en.q ≠ .lin →
      ∀ k ls (K : Kont) (ρk ρp Z ρkL W'' : WRes) (v'' : Val) (χ : WRes) (hχ : χ.InStratum A)
        (P'' : Val → SPropS Loc Val A) (hw'' : P'' v'' ⟨χ, hχ⟩),
        NoOwn ρp → ResU.CompS ρk ρp Z →
        ResU.CompS (Z.del l) (ResU.single l (CellU.mutOf A v'' χ hχ P'' hw'')) Z →
        (Z.del l).InStratum (↓A) →
        (∀ u r, SPropS.toU (P'' u) r → SPropS.toU (F k u) r) →
        ResU.CompS χ (ResU.single l (CellU.ownOf v'')) W'' → ResU.CompS (Z.del l) W'' ρkL →
        cancelOKN en k ls K ρk → cancelOKN en' k ls K ρkL)
    {Q : PostN} :
    ∀ n j, n ≤ j → ∀ ls e (v : Val) (ρP ρlP ρb ρ : WRes) (houtP : ρP.InStratum A),
      ρb.InStratum (↓A) → ∀ (P : Val → SPropS Loc Val A),
      (∀ u r, SPropS.toU (P u) r → SPropS.toU (F j u) r) → ∀ (hwit : P v ⟨ρP, houtP⟩),
      ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP → ResU.CompS ρlP ρb ρ →
      (∀ BM, ResU.CompS ρb (ResU.single l (CellU.mutOf A v ρP houtP P hwit)) BM →
        erwp (ℍ := ℍ) (Φ.set l A F) (opTableN T) (MFPost l A F Q) n ls e BM) →
      erwp (ℍ := ℍ) Φ (opTableR T' (claimR l A F)) Q n ls e ρ := by
  intro n j hjn ls e v ρP ρlP ρb ρ houtP houtb P hPF hwit hclP hcρ hA
  rw [erwp_eq_erwpK_of (opTableRK_lift A T' (claimR l A F)) Φ Q]
  refine erwpK_M_frameCR (V := fun _ _ => True) (Φ := fun _ => Φ) (Inv := fun _ => True)
    (flI := fun _ => A) (flO := fun _ => A) (Ti := fun _ => liftTabK T)
    (To := fun _ => liftTabK T') (Q := fun _ => Q) hF
    (fun _ => hT.lift)
    (canFold_lift hcan)
    (fun _ _ => foldTwin_lift (hTT') A l A) n j hjn () trivial ls e v ρP ρlP ρb ρ houtP houtb
    P hPF hwit hclP hcρ fun BM hBM => ?_
  have h := hA BM hBM
  rw [erwp_opTableN_eq_erwpK A] at h
  exact h

/-- **Mut Frame at `erwpK` across Kripke stops**, over a cancel run that stops (`erwp_M_frame_cancelRunCR`). -/
theorem erwpK_M_frame_cancelRunCR {V : ι → ι → Prop} {Φ : ι → LocFam} {Inv : ι → Prop} {l : Loc} {A : Life}
    {F : Nat → Val → SPropS Loc Val A} (hF : DownFam A F) {flI flO : ι → Life}
    {Ti To : ι → OpTabK ι} (hT : ∀ x, (Ti x).LendOKCR A)
    (hcan : CanFold Inv Ti To l A F)
    (hTT : ∀ x, Inv x → (Ti x).FoldTwin Inv (flI x) (flO x) (To x) l A) :
    KFrame (ℍ := ℍ) V Φ Inv l A F (fun y => cancelTabK (flI y) (Ti y))
      (fun y => cancelTabRK (flO y) (To y) (claimR l A F)) (fun _ _ _ _ _ => False) (fun _ _ _ _ _ => False) :=
  KFrame.postIn (KFrame.conv (TbO := fun y k ls t Ψ => BoLo.or
      (performStopGK (flO y) (To y) (fun _ _ _ => True) k ls t Ψ)
      (cancelRaiseRK (To y) (claimR l A F) k ls t Ψ))
    (erwpK_M_frameGen (RI := fun y => cancelRaiseK (Ti y))
      (RO := fun y => cancelRaiseRK (To y) (claimR l A F))
      (G := fun _ _ _ _ => True) (Q := fun _ _ _ _ _ => False) hF hT hTT hcan
      (by intros; trivial)
      (fun x hx => cancelFold_claim (hTT x hx).twin (hT x).pa))
    (fun _ => or_local (performStopGK_local _ _ _) (cancelRaiseRK_free _ _)) (unguard))
    (fun _ => or_local (performStopK_local _ _) (cancelRaiseK_free _)) (fun _ _ _ _ _ h => h.elim)

/-- `erwp_M_frame_cancelRunCR` from `erwpK_M_frame_cancelRunCR`. -/
theorem erwp_M_frame_cancelRunCR_of_K {Φ : LocFam} {l : Loc} {A : Life}
    {F : Nat → Val → SPropS Loc Val A} (hF : DownFam A F) {T T' : OpTabN} (hT : T.LendOKCR A)
    (hTT' : T.Twin T')
    (hcan : ∀ m i en en', T m i = some en → T' m i = some en' → en.abort = false →
      en.q ≠ .lin →
      ∀ k ls (K : Kont) (ρk ρp Z ρkL W'' : WRes) (v'' : Val) (χ : WRes) (hχ : χ.InStratum A)
        (P'' : Val → SPropS Loc Val A) (hw'' : P'' v'' ⟨χ, hχ⟩),
        NoOwn ρp → ResU.CompS ρk ρp Z →
        ResU.CompS (Z.del l) (ResU.single l (CellU.mutOf A v'' χ hχ P'' hw'')) Z →
        (Z.del l).InStratum (↓A) →
        (∀ u r, SPropS.toU (P'' u) r → SPropS.toU (F k u) r) →
        ResU.CompS χ (ResU.single l (CellU.ownOf v'')) W'' → ResU.CompS (Z.del l) W'' ρkL →
        cancelOKN en k ls K ρk → cancelOKN en' k ls K ρkL) :
    ∀ n j, n ≤ j → ∀ ls e (v : Val) (ρP ρlP ρb ρ : WRes) (houtP : ρP.InStratum A),
      ρb.InStratum (↓A) → ∀ (P : Val → SPropS Loc Val A),
      (∀ u r, SPropS.toU (P u) r → SPropS.toU (F j u) r) → ∀ (hwit : P v ⟨ρP, houtP⟩),
      ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP → ResU.CompS ρlP ρb ρ →
      (∀ BM, ResU.CompS ρb (ResU.single l (CellU.mutOf A v ρP houtP P hwit)) BM →
        erwp (ℍ := ℍ) (Φ.set l A F) (cancelTabN T) (fun _ _ _ _ => False) n ls e BM) →
      erwp (ℍ := ℍ) Φ (cancelTabR T' (claimR l A F)) (fun _ _ _ _ => False) n ls e ρ := by
  intro n j hjn ls e v ρP ρlP ρb ρ houtP houtb P hPF hwit hclP hcρ hA
  rw [erwp_eq_erwpK_of (cancelTabRK_lift A T' (claimR l A F)) Φ _]
  refine erwpK_M_frame_cancelRunCR (V := fun _ _ => True) (Φ := fun _ => Φ) (Inv := fun _ => True)
    (flI := fun _ => A) (flO := fun _ => A) (Ti := fun _ => liftTabK T)
    (To := fun _ => liftTabK T') hF
    (fun _ => hT.lift)
    (canFold_lift hcan)
    (fun _ _ => foldTwin_lift (hTT') A l A) n j hjn () trivial ls e v ρP ρlP ρb ρ houtP houtb
    P hPF hwit hclP hcρ fun BM hBM => ?_
  have h := hA BM hBM
  rw [erwp_eq_erwpK_of (cancelTabK_lift A T) _ _] at h
  exact h

/-- **Mut Frame at `erwpK` across Kripke stops**, the inner raises already carrying a claim (`erwp_M_frameRR`). -/
theorem erwpK_M_frameRR {V : ι → ι → Prop} {Φ : ι → LocFam} {Inv : ι → Prop} {l : Loc} {A : Life}
    {F : Nat → Val → SPropS Loc Val A} (hF : DownFam A F) {flI flO : ι → Life}
    {Ti To : ι → OpTabK ι} (hT : ∀ x, (Ti x).LendOKCR A)
    (hlin : ∀ x m i en, Ti x m i = some en → en.abort = false → en.q = .lin)
    {R : Nat → WProp} (hR : ∀ k ρ, R k ρ → ρ.InStratum A)
    (hTT : ∀ x, Inv x → (Ti x).FoldTwin Inv (flI x) (flO x) (To x) l A) {Q : ι → PostN} :
    KFrame (ℍ := ℍ) V Φ Inv l A F (fun y => opTableRK (flI y) (Ti y) R)
      (fun y => opTableRK (flO y) (To y) (fun k => claimR l A F k ⋆ R k)) (fun y => MFPost l A F (Q y)) Q :=
  KFrame.conv (TbO := fun y k ls t Ψ => BoLo.or
      (performStopGK (flO y) (To y) (fun _ _ _ => True) k ls t Ψ)
      (raiseStopRK (To y) (fun k => claimR l A F k ⋆ R k) k ls t Ψ))
    (erwpK_M_frameGen (RI := fun y => raiseStopRK (Ti y) R)
      (RO := fun y => raiseStopRK (To y) (fun k => claimR l A F k ⋆ R k))
      (G := fun _ _ _ _ => True) hF hT hTT (canFold_of_lin hlin)
      (by intros; trivial)
      (fun x hx => raiseFold_claimR (hTT x hx).twin (hT x).pa hR))
    (fun _ => or_local (performStopGK_local _ _ _) (raiseStopRK_free _ _)) (unguard)

/-- `erwp_M_frameRR` from `erwpK_M_frameRR`. -/
theorem erwp_M_frameRR_of_K {Φ : LocFam} {l : Loc} {A : Life} {F : Nat → Val → SPropS Loc Val A}
    (hF : DownFam A F) {T : OpTabN} (hT : T.LendOKR A) {R : Nat → WProp}
    (hR : ∀ k ρ, R k ρ → ρ.InStratum A) {Q : PostN} :
    ∀ n j, n ≤ j → ∀ ls e (v : Val) (ρP ρlP ρb ρ : WRes) (houtP : ρP.InStratum A),
      ρb.InStratum (↓A) → ∀ (P : Val → SPropS Loc Val A),
      (∀ u r, SPropS.toU (P u) r → SPropS.toU (F j u) r) → ∀ (hwit : P v ⟨ρP, houtP⟩),
      ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP → ResU.CompS ρlP ρb ρ →
      (∀ BM, ResU.CompS ρb (ResU.single l (CellU.mutOf A v ρP houtP P hwit)) BM →
        erwp (ℍ := ℍ) (Φ.set l A F) (opTableR T R) (MFPost l A F Q) n ls e BM) →
      erwp (ℍ := ℍ) Φ (opTableR T (fun k => claimR l A F k ⋆ R k)) Q n ls e ρ := by
  intro n j hjn ls e v ρP ρlP ρb ρ houtP houtb P hPF hwit hclP hcρ hA
  rw [erwp_eq_erwpK_of (opTableRK_lift A T (fun k => claimR l A F k ⋆ R k)) Φ Q]
  refine erwpK_M_frameRR (V := fun _ _ => True) (Φ := fun _ => Φ) (Inv := fun _ => True)
    (flI := fun _ => A) (flO := fun _ => A) (Ti := fun _ => liftTabK T)
    (To := fun _ => liftTabK T) (Q := fun _ => Q) hF
    (fun _ => hT.toCR.lift)
    (liftTabK_lin fun m i en h ha => (hT.entry m i en h ha).1)
    (hR)
    (fun _ _ => foldTwin_lift (OpTabN.twin_refl T) A l A) n j hjn () trivial ls e v ρP ρlP ρb ρ houtP houtb
    P hPF hwit hclP hcρ fun BM hBM => ?_
  have h := hA BM hBM
  rw [erwp_eq_erwpK_of (opTableRK_lift A T R) _ _] at h
  exact h

/-- **Mut Frame at `erwpK` across Kripke stops**, cancellable stops, the inner raises carrying a claim (`erwp_M_frameCRR`). -/
theorem erwpK_M_frameCRR {V : ι → ι → Prop} {Φ : ι → LocFam} {Inv : ι → Prop} {l : Loc} {A : Life}
    {F : Nat → Val → SPropS Loc Val A} (hF : DownFam A F) {flI flO : ι → Life}
    {Ti To : ι → OpTabK ι} (hT : ∀ x, (Ti x).LendOKCR A)
    (hcan : CanFold Inv Ti To l A F)
    {R : Nat → WProp} (hR : ∀ k ρ, R k ρ → ρ.InStratum A)
    (hTT : ∀ x, Inv x → (Ti x).FoldTwin Inv (flI x) (flO x) (To x) l A) {Q : ι → PostN} :
    KFrame (ℍ := ℍ) V Φ Inv l A F (fun y => opTableRK (flI y) (Ti y) R)
      (fun y => opTableRK (flO y) (To y) (fun k => claimR l A F k ⋆ R k)) (fun y => MFPost l A F (Q y)) Q :=
  KFrame.conv (TbO := fun y k ls t Ψ => BoLo.or
      (performStopGK (flO y) (To y) (fun _ _ _ => True) k ls t Ψ)
      (raiseStopRK (To y) (fun k => claimR l A F k ⋆ R k) k ls t Ψ))
    (erwpK_M_frameGen (RI := fun y => raiseStopRK (Ti y) R)
      (RO := fun y => raiseStopRK (To y) (fun k => claimR l A F k ⋆ R k))
      (G := fun _ _ _ _ => True) hF hT hTT hcan
      (by intros; trivial)
      (fun x hx => raiseFold_claimR (hTT x hx).twin (hT x).pa hR))
    (fun _ => or_local (performStopGK_local _ _ _) (raiseStopRK_free _ _)) (unguard)

/-- `erwp_M_frameCRR` from `erwpK_M_frameCRR`. -/
theorem erwp_M_frameCRR_of_K {Φ : LocFam} {l : Loc} {A : Life} {F : Nat → Val → SPropS Loc Val A}
    (hF : DownFam A F) {T T' : OpTabN} (hT : T.LendOKCR A) (hTT' : T.Twin T')
    (hcan : ∀ m i en en', T m i = some en → T' m i = some en' → en.abort = false →
      en.q ≠ .lin →
      ∀ k ls (K : Kont) (ρk ρp Z ρkL W'' : WRes) (v'' : Val) (χ : WRes) (hχ : χ.InStratum A)
        (P'' : Val → SPropS Loc Val A) (hw'' : P'' v'' ⟨χ, hχ⟩),
        NoOwn ρp → ResU.CompS ρk ρp Z →
        ResU.CompS (Z.del l) (ResU.single l (CellU.mutOf A v'' χ hχ P'' hw'')) Z →
        (Z.del l).InStratum (↓A) →
        (∀ u r, SPropS.toU (P'' u) r → SPropS.toU (F k u) r) →
        ResU.CompS χ (ResU.single l (CellU.ownOf v'')) W'' → ResU.CompS (Z.del l) W'' ρkL →
        cancelOKN en k ls K ρk → cancelOKN en' k ls K ρkL)
    {R : Nat → WProp} (hR : ∀ k ρ, R k ρ → ρ.InStratum A) {Q : PostN} :
    ∀ n j, n ≤ j → ∀ ls e (v : Val) (ρP ρlP ρb ρ : WRes) (houtP : ρP.InStratum A),
      ρb.InStratum (↓A) → ∀ (P : Val → SPropS Loc Val A),
      (∀ u r, SPropS.toU (P u) r → SPropS.toU (F j u) r) → ∀ (hwit : P v ⟨ρP, houtP⟩),
      ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP → ResU.CompS ρlP ρb ρ →
      (∀ BM, ResU.CompS ρb (ResU.single l (CellU.mutOf A v ρP houtP P hwit)) BM →
        erwp (ℍ := ℍ) (Φ.set l A F) (opTableR T R) (MFPost l A F Q) n ls e BM) →
      erwp (ℍ := ℍ) Φ (opTableR T' (fun k => claimR l A F k ⋆ R k)) Q n ls e ρ := by
  intro n j hjn ls e v ρP ρlP ρb ρ houtP houtb P hPF hwit hclP hcρ hA
  rw [erwp_eq_erwpK_of (opTableRK_lift A T' (fun k => claimR l A F k ⋆ R k)) Φ Q]
  refine erwpK_M_frameCRR (V := fun _ _ => True) (Φ := fun _ => Φ) (Inv := fun _ => True)
    (flI := fun _ => A) (flO := fun _ => A) (Ti := fun _ => liftTabK T)
    (To := fun _ => liftTabK T') (Q := fun _ => Q) hF
    (fun _ => hT.lift)
    (canFold_lift hcan)
    (hR)
    (fun _ _ => foldTwin_lift (hTT') A l A) n j hjn () trivial ls e v ρP ρlP ρb ρ houtP houtb
    P hPF hwit hclP hcρ fun BM hBM => ?_
  have h := hA BM hBM
  rw [erwp_eq_erwpK_of (opTableRK_lift A T R) _ _] at h
  exact h

/-- **Mut Frame at `erwpK` across Kripke stops**, over a cancel run whose raises carry a claim (`erwp_M_frame_cancelRunCRR`). -/
theorem erwpK_M_frame_cancelRunCRR {V : ι → ι → Prop} {Φ : ι → LocFam} {Inv : ι → Prop} {l : Loc} {A : Life}
    {F : Nat → Val → SPropS Loc Val A} (hF : DownFam A F) {flI flO : ι → Life}
    {Ti To : ι → OpTabK ι} (hT : ∀ x, (Ti x).LendOKCR A)
    (hcan : CanFold Inv Ti To l A F)
    {R : Nat → WProp} (hR : ∀ k ρ, R k ρ → ρ.InStratum A)
    (hTT : ∀ x, Inv x → (Ti x).FoldTwin Inv (flI x) (flO x) (To x) l A) :
    KFrame (ℍ := ℍ) V Φ Inv l A F (fun y => cancelTabRK (flI y) (Ti y) R)
      (fun y => cancelTabRK (flO y) (To y) (fun k => claimR l A F k ⋆ R k)) (fun _ _ _ _ _ => False) (fun _ _ _ _ _ => False) :=
  KFrame.postIn (KFrame.conv (TbO := fun y k ls t Ψ => BoLo.or
      (performStopGK (flO y) (To y) (fun _ _ _ => True) k ls t Ψ)
      (cancelRaiseRK (To y) (fun k => claimR l A F k ⋆ R k) k ls t Ψ))
    (erwpK_M_frameGen (RI := fun y => cancelRaiseRK (Ti y) R)
      (RO := fun y => cancelRaiseRK (To y) (fun k => claimR l A F k ⋆ R k))
      (G := fun _ _ _ _ => True) (Q := fun _ _ _ _ _ => False) hF hT hTT hcan
      (by intros; trivial)
      (fun x hx => cancelFold_claimR (hTT x hx).twin (hT x).pa hR))
    (fun _ => or_local (performStopGK_local _ _ _) (cancelRaiseRK_free _ _)) (unguard))
    (fun _ => or_local (performStopK_local _ _) (cancelRaiseRK_free _ _)) (fun _ _ _ _ _ h => h.elim)

/-- `erwp_M_frame_cancelRunCRR` from `erwpK_M_frame_cancelRunCRR`. -/
theorem erwp_M_frame_cancelRunCRR_of_K {Φ : LocFam} {l : Loc} {A : Life}
    {F : Nat → Val → SPropS Loc Val A} (hF : DownFam A F) {T T' : OpTabN} (hT : T.LendOKCR A)
    (hTT' : T.Twin T')
    (hcan : ∀ m i en en', T m i = some en → T' m i = some en' → en.abort = false →
      en.q ≠ .lin →
      ∀ k ls (K : Kont) (ρk ρp Z ρkL W'' : WRes) (v'' : Val) (χ : WRes) (hχ : χ.InStratum A)
        (P'' : Val → SPropS Loc Val A) (hw'' : P'' v'' ⟨χ, hχ⟩),
        NoOwn ρp → ResU.CompS ρk ρp Z →
        ResU.CompS (Z.del l) (ResU.single l (CellU.mutOf A v'' χ hχ P'' hw'')) Z →
        (Z.del l).InStratum (↓A) →
        (∀ u r, SPropS.toU (P'' u) r → SPropS.toU (F k u) r) →
        ResU.CompS χ (ResU.single l (CellU.ownOf v'')) W'' → ResU.CompS (Z.del l) W'' ρkL →
        cancelOKN en k ls K ρk → cancelOKN en' k ls K ρkL)
    {R : Nat → WProp} (hR : ∀ k ρ, R k ρ → ρ.InStratum A) :
    ∀ n j, n ≤ j → ∀ ls e (v : Val) (ρP ρlP ρb ρ : WRes) (houtP : ρP.InStratum A),
      ρb.InStratum (↓A) → ∀ (P : Val → SPropS Loc Val A),
      (∀ u r, SPropS.toU (P u) r → SPropS.toU (F j u) r) → ∀ (hwit : P v ⟨ρP, houtP⟩),
      ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP → ResU.CompS ρlP ρb ρ →
      (∀ BM, ResU.CompS ρb (ResU.single l (CellU.mutOf A v ρP houtP P hwit)) BM →
        erwp (ℍ := ℍ) (Φ.set l A F) (cancelTabR T R) (fun _ _ _ _ => False) n ls e BM) →
      erwp (ℍ := ℍ) Φ (cancelTabR T' (fun k => claimR l A F k ⋆ R k)) (fun _ _ _ _ => False) n ls e ρ := by
  intro n j hjn ls e v ρP ρlP ρb ρ houtP houtb P hPF hwit hclP hcρ hA
  rw [erwp_eq_erwpK_of (cancelTabRK_lift A T' (fun k => claimR l A F k ⋆ R k)) Φ _]
  refine erwpK_M_frame_cancelRunCRR (V := fun _ _ => True) (Φ := fun _ => Φ) (Inv := fun _ => True)
    (flI := fun _ => A) (flO := fun _ => A) (Ti := fun _ => liftTabK T)
    (To := fun _ => liftTabK T') hF
    (fun _ => hT.lift)
    (canFold_lift hcan)
    (hR)
    (fun _ _ => foldTwin_lift (hTT') A l A) n j hjn () trivial ls e v ρP ρlP ρb ρ houtP houtb
    P hPF hwit hclP hcρ fun BM hBM => ?_
  have h := hA BM hBM
  rw [erwp_eq_erwpK_of (cancelTabRK_lift A T R) _ _] at h
  exact h

/-- **Mut Frame at `erwpK` across Kripke stops**, the stops guarded by the fold (`erwp_M_frameCRG`). -/
theorem erwpK_M_frameCRG {V : ι → ι → Prop} {Φ : ι → LocFam} {Inv : ι → Prop} {l : Loc} {A : Life}
    {F : Nat → Val → SPropS Loc Val A} (hF : DownFam A F) {flI flO : ι → Life}
    {Ti To : ι → OpTabK ι} (hT : ∀ x, (Ti x).LendOKCR A)
    (hcan : CanFold Inv Ti To l A F)
    (hTT : ∀ x, Inv x → (Ti x).FoldTwin Inv (flI x) (flO x) (To x) l A) {Q : ι → PostN} :
    KFrame (ℍ := ℍ) V Φ Inv l A F (fun y => opTableK (flI y) (Ti y))
      (fun y => opTableGRK (flO y) (To y) (CellFold l A F) (claimR l A F)) (fun y => MFPost l A F (Q y)) Q :=
  KFrame.conv (TbO := fun y k ls t Ψ => BoLo.or
      (performStopGK (flO y) (To y) (CellFold l A F) k ls t Ψ)
      (raiseStopRK (To y) (claimR l A F) k ls t Ψ))
    (erwpK_M_frameGen (RI := fun y => raiseStopK (Ti y))
      (RO := fun y => raiseStopRK (To y) (claimR l A F))
      (G := fun _ => CellFold l A F) hF hT hTT hcan
      (fun _ _ _ _ _ _ _ _ _ hχ _ hw'' hPk hW'' hkL =>
        cellFold_fold (hχ := hχ) (hw'' := hw'') hPk hW'' hkL)
      (fun x hx => raiseFold_claim (hTT x hx).twin (hT x).pa))
    (fun _ => or_local (performStopGK_local _ _ _) (raiseStopRK_free _ _)) (fun _ _ _ _ _ _ h => h)

/-- `erwp_M_frameCRG` from `erwpK_M_frameCRG`. -/
theorem erwp_M_frameCRG_of_K {Φ : LocFam} {l : Loc} {A : Life} {F : Nat → Val → SPropS Loc Val A}
    (hF : DownFam A F) {T T' : OpTabN} (hT : T.LendOKCR A) (hTT' : T.Twin T')
    (hcan : ∀ m i en en', T m i = some en → T' m i = some en' → en.abort = false →
      en.q ≠ .lin →
      ∀ k ls (K : Kont) (ρk ρp Z ρkL W'' : WRes) (v'' : Val) (χ : WRes) (hχ : χ.InStratum A)
        (P'' : Val → SPropS Loc Val A) (hw'' : P'' v'' ⟨χ, hχ⟩),
        NoOwn ρp → ResU.CompS ρk ρp Z →
        ResU.CompS (Z.del l) (ResU.single l (CellU.mutOf A v'' χ hχ P'' hw'')) Z →
        (Z.del l).InStratum (↓A) →
        (∀ u r, SPropS.toU (P'' u) r → SPropS.toU (F k u) r) →
        ResU.CompS χ (ResU.single l (CellU.ownOf v'')) W'' → ResU.CompS (Z.del l) W'' ρkL →
        cancelOKN en k ls K ρk → cancelOKN en' k ls K ρkL)
    {Q : PostN} :
    ∀ n j, n ≤ j → ∀ ls e (v : Val) (ρP ρlP ρb ρ : WRes) (houtP : ρP.InStratum A),
      ρb.InStratum (↓A) → ∀ (P : Val → SPropS Loc Val A),
      (∀ u r, SPropS.toU (P u) r → SPropS.toU (F j u) r) → ∀ (hwit : P v ⟨ρP, houtP⟩),
      ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP → ResU.CompS ρlP ρb ρ →
      (∀ BM, ResU.CompS ρb (ResU.single l (CellU.mutOf A v ρP houtP P hwit)) BM →
        erwp (ℍ := ℍ) (Φ.set l A F) (opTableN T) (MFPost l A F Q) n ls e BM) →
      erwp (ℍ := ℍ) Φ (opTableGR T' (CellFold l A F) (claimR l A F)) Q n ls e ρ := by
  intro n j hjn ls e v ρP ρlP ρb ρ houtP houtb P hPF hwit hclP hcρ hA
  rw [erwp_eq_erwpK_of (opTableGRK_lift A T' (CellFold l A F) (claimR l A F)) Φ Q]
  refine erwpK_M_frameCRG (V := fun _ _ => True) (Φ := fun _ => Φ) (Inv := fun _ => True)
    (flI := fun _ => A) (flO := fun _ => A) (Ti := fun _ => liftTabK T)
    (To := fun _ => liftTabK T') (Q := fun _ => Q) hF
    (fun _ => hT.lift)
    (canFold_lift hcan)
    (fun _ _ => foldTwin_lift (hTT') A l A) n j hjn () trivial ls e v ρP ρlP ρb ρ houtP houtb
    P hPF hwit hclP hcρ fun BM hBM => ?_
  have h := hA BM hBM
  rw [erwp_opTableN_eq_erwpK A] at h
  exact h

/-- **Mut Frame at `erwpK` across Kripke stops**, over a cancel run, the stops guarded by the fold (`erwp_M_frame_cancelRunCRG`). -/
theorem erwpK_M_frame_cancelRunCRG {V : ι → ι → Prop} {Φ : ι → LocFam} {Inv : ι → Prop} {l : Loc} {A : Life}
    {F : Nat → Val → SPropS Loc Val A} (hF : DownFam A F) {flI flO : ι → Life}
    {Ti To : ι → OpTabK ι} (hT : ∀ x, (Ti x).LendOKCR A)
    (hcan : CanFold Inv Ti To l A F)
    (hTT : ∀ x, Inv x → (Ti x).FoldTwin Inv (flI x) (flO x) (To x) l A) :
    KFrame (ℍ := ℍ) V Φ Inv l A F (fun y => cancelTabK (flI y) (Ti y))
      (fun y => cancelTabGRK (flO y) (To y) (CellFold l A F) (claimR l A F)) (fun _ _ _ _ _ => False) (fun _ _ _ _ _ => False) :=
  KFrame.postIn (KFrame.conv (TbO := fun y k ls t Ψ => BoLo.or
      (performStopGK (flO y) (To y) (CellFold l A F) k ls t Ψ)
      (cancelRaiseRK (To y) (claimR l A F) k ls t Ψ))
    (erwpK_M_frameGen (RI := fun y => cancelRaiseK (Ti y))
      (RO := fun y => cancelRaiseRK (To y) (claimR l A F))
      (G := fun _ => CellFold l A F) (Q := fun _ _ _ _ _ => False) hF hT hTT hcan
      (fun _ _ _ _ _ _ _ _ _ hχ _ hw'' hPk hW'' hkL =>
        cellFold_fold (hχ := hχ) (hw'' := hw'') hPk hW'' hkL)
      (fun x hx => cancelFold_claim (hTT x hx).twin (hT x).pa))
    (fun _ => or_local (performStopGK_local _ _ _) (cancelRaiseRK_free _ _)) (fun _ _ _ _ _ _ h => h))
    (fun _ => or_local (performStopK_local _ _) (cancelRaiseK_free _)) (fun _ _ _ _ _ h => h.elim)

/-- `erwp_M_frame_cancelRunCRG` from `erwpK_M_frame_cancelRunCRG`. -/
theorem erwp_M_frame_cancelRunCRG_of_K {Φ : LocFam} {l : Loc} {A : Life}
    {F : Nat → Val → SPropS Loc Val A} (hF : DownFam A F) {T T' : OpTabN} (hT : T.LendOKCR A)
    (hTT' : T.Twin T')
    (hcan : ∀ m i en en', T m i = some en → T' m i = some en' → en.abort = false →
      en.q ≠ .lin →
      ∀ k ls (K : Kont) (ρk ρp Z ρkL W'' : WRes) (v'' : Val) (χ : WRes) (hχ : χ.InStratum A)
        (P'' : Val → SPropS Loc Val A) (hw'' : P'' v'' ⟨χ, hχ⟩),
        NoOwn ρp → ResU.CompS ρk ρp Z →
        ResU.CompS (Z.del l) (ResU.single l (CellU.mutOf A v'' χ hχ P'' hw'')) Z →
        (Z.del l).InStratum (↓A) →
        (∀ u r, SPropS.toU (P'' u) r → SPropS.toU (F k u) r) →
        ResU.CompS χ (ResU.single l (CellU.ownOf v'')) W'' → ResU.CompS (Z.del l) W'' ρkL →
        cancelOKN en k ls K ρk → cancelOKN en' k ls K ρkL) :
    ∀ n j, n ≤ j → ∀ ls e (v : Val) (ρP ρlP ρb ρ : WRes) (houtP : ρP.InStratum A),
      ρb.InStratum (↓A) → ∀ (P : Val → SPropS Loc Val A),
      (∀ u r, SPropS.toU (P u) r → SPropS.toU (F j u) r) → ∀ (hwit : P v ⟨ρP, houtP⟩),
      ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP → ResU.CompS ρlP ρb ρ →
      (∀ BM, ResU.CompS ρb (ResU.single l (CellU.mutOf A v ρP houtP P hwit)) BM →
        erwp (ℍ := ℍ) (Φ.set l A F) (cancelTabN T) (fun _ _ _ _ => False) n ls e BM) →
      erwp (ℍ := ℍ) Φ (cancelTabGR T' (CellFold l A F) (claimR l A F)) (fun _ _ _ _ => False) n ls e ρ := by
  intro n j hjn ls e v ρP ρlP ρb ρ houtP houtb P hPF hwit hclP hcρ hA
  rw [erwp_eq_erwpK_of (cancelTabGRK_lift A T' (CellFold l A F) (claimR l A F)) Φ _]
  refine erwpK_M_frame_cancelRunCRG (V := fun _ _ => True) (Φ := fun _ => Φ) (Inv := fun _ => True)
    (flI := fun _ => A) (flO := fun _ => A) (Ti := fun _ => liftTabK T)
    (To := fun _ => liftTabK T') hF
    (fun _ => hT.lift)
    (canFold_lift hcan)
    (fun _ _ => foldTwin_lift (hTT') A l A) n j hjn () trivial ls e v ρP ρlP ρb ρ houtP houtb
    P hPF hwit hclP hcρ fun BM hBM => ?_
  have h := hA BM hBM
  rw [erwp_eq_erwpK_of (cancelTabK_lift A T) _ _] at h
  exact h

/-- **Mut Frame at `erwpK` across Kripke stops**, the stops guarded by the fold, no raise (`erwp_M_frameF`). -/
theorem erwpK_M_frameF {V : ι → ι → Prop} {Φ : ι → LocFam} {Inv : ι → Prop} {l : Loc} {A : Life}
    {F : Nat → Val → SPropS Loc Val A} (hF : DownFam A F) {flI flO : ι → Life}
    {Ti To : ι → OpTabK ι} (hT : ∀ x, (Ti x).LendOKCR A)
    (hab : ∀ x m i en, Ti x m i = some en → en.abort = false)
    (hlin : ∀ x m i en, Ti x m i = some en → en.abort = false → en.q = .lin)
    (hTT : ∀ x, Inv x → (Ti x).FoldTwin Inv (flI x) (flO x) (To x) l A) {Q : ι → PostN} :
    KFrame (ℍ := ℍ) V Φ Inv l A F (fun y => opTableK (flI y) (Ti y))
      (fun y => opTableGK (flO y) (To y) (CellFold l A F)) (fun y => MFPost l A F (Q y)) Q :=
  KFrame.conv (TbO := fun y k ls t Ψ => BoLo.or
      (performStopGK (flO y) (To y) (CellFold l A F) k ls t Ψ)
      ((fun _ _ _ _ _ _ => False : ι → TableK ι) y k ls t Ψ))
    (erwpK_M_frameGen (RI := fun y => raiseStopK (Ti y))
      (RO := (fun _ _ _ _ _ _ => False : ι → TableK ι))
      (G := fun _ => CellFold l A F) hF hT hTT (canFold_of_lin hlin)
      (fun _ _ _ _ _ _ _ _ _ hχ _ hw'' hPk hW'' hkL =>
        cellFold_fold (hχ := hχ) (hw'' := hw'') hPk hW'' hkL)
      (fun x _ => raiseFold_absurd (hab x) _))
    (fun _ => or_local (performStopGK_local _ _ _) ((fun _ _ _ _ _ _ h => h))) (noRaise)

/-- `erwp_M_frameF` from `erwpK_M_frameF`. -/
theorem erwp_M_frameF_of_K {Φ : LocFam} {l : Loc} {A : Life} {F : Nat → Val → SPropS Loc Val A}
    (hF : DownFam A F) {T : OpTabN} (hT : T.LendOK A) {Q : PostN} :
    ∀ n j, n ≤ j → ∀ ls e (v : Val) (ρP ρlP ρb ρ : WRes) (houtP : ρP.InStratum A),
      ρb.InStratum (↓A) → ∀ (P : Val → SPropS Loc Val A),
      (∀ u r, SPropS.toU (P u) r → SPropS.toU (F j u) r) → ∀ (hwit : P v ⟨ρP, houtP⟩),
      ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP → ResU.CompS ρlP ρb ρ →
      (∀ BM, ResU.CompS ρb (ResU.single l (CellU.mutOf A v ρP houtP P hwit)) BM →
        erwp (ℍ := ℍ) (Φ.set l A F) (opTableN T) (MFPost l A F Q) n ls e BM) →
      erwp (ℍ := ℍ) Φ (opTableG T (CellFold l A F)) Q n ls e ρ := by
  intro n j hjn ls e v ρP ρlP ρb ρ houtP houtb P hPF hwit hclP hcρ hA
  rw [erwp_eq_erwpK_of (opTableGK_lift A T (CellFold l A F)) Φ Q]
  refine erwpK_M_frameF (V := fun _ _ => True) (Φ := fun _ => Φ) (Inv := fun _ => True)
    (flI := fun _ => A) (flO := fun _ => A) (Ti := fun _ => liftTabK T)
    (To := fun _ => liftTabK T) (Q := fun _ => Q) hF
    (fun _ => hT.toCR.lift)
    (liftTabK_abort fun m i en h => (hT.entry m i en h).1)
    (liftTabK_lin fun m i en h _ => (hT.entry m i en h).2.1)
    (fun _ _ => foldTwin_lift (OpTabN.twin_refl T) A l A) n j hjn () trivial ls e v ρP ρlP ρb ρ houtP houtb
    P hPF hwit hclP hcρ fun BM hBM => ?_
  have h := hA BM hBM
  rw [erwp_opTableN_eq_erwpK A] at h
  exact h

/-- **Mut Frame at `erwpK` across Kripke stops**, cancellable stops guarded by the fold, no raise (`erwp_M_frameTF`). -/
theorem erwpK_M_frameTF {V : ι → ι → Prop} {Φ : ι → LocFam} {Inv : ι → Prop} {l : Loc} {A : Life}
    {F : Nat → Val → SPropS Loc Val A} (hF : DownFam A F) {flI flO : ι → Life}
    {Ti To : ι → OpTabK ι} (hT : ∀ x, (Ti x).LendOKCR A)
    (hab : ∀ x m i en, Ti x m i = some en → en.abort = false)
    (hcan : CanFold Inv Ti To l A F)
    (hTT : ∀ x, Inv x → (Ti x).FoldTwin Inv (flI x) (flO x) (To x) l A) {Q : ι → PostN} :
    KFrame (ℍ := ℍ) V Φ Inv l A F (fun y => opTableK (flI y) (Ti y))
      (fun y => opTableGK (flO y) (To y) (CellFold l A F)) (fun y => MFPost l A F (Q y)) Q :=
  KFrame.conv (TbO := fun y k ls t Ψ => BoLo.or
      (performStopGK (flO y) (To y) (CellFold l A F) k ls t Ψ)
      ((fun _ _ _ _ _ _ => False : ι → TableK ι) y k ls t Ψ))
    (erwpK_M_frameGen (RI := fun y => raiseStopK (Ti y))
      (RO := (fun _ _ _ _ _ _ => False : ι → TableK ι))
      (G := fun _ => CellFold l A F) hF hT hTT hcan
      (fun _ _ _ _ _ _ _ _ _ hχ _ hw'' hPk hW'' hkL =>
        cellFold_fold (hχ := hχ) (hw'' := hw'') hPk hW'' hkL)
      (fun x _ => raiseFold_absurd (hab x) _))
    (fun _ => or_local (performStopGK_local _ _ _) ((fun _ _ _ _ _ _ h => h))) (noRaise)

/-- `erwp_M_frameTF` from `erwpK_M_frameTF`. -/
theorem erwp_M_frameTF_of_K {Φ : LocFam} {l : Loc} {A : Life} {F : Nat → Val → SPropS Loc Val A}
    (hF : DownFam A F) {T T' : OpTabN} (hT : T.LendOKC A) (hTT' : T.Twin T')
    (hcan : ∀ m i en en', T m i = some en → T' m i = some en' → en.q ≠ .lin →
      ∀ k ls (K : Kont) (ρk ρp Z ρkL W'' : WRes) (v'' : Val) (χ : WRes) (hχ : χ.InStratum A)
        (P'' : Val → SPropS Loc Val A) (hw'' : P'' v'' ⟨χ, hχ⟩),
        NoOwn ρp → ResU.CompS ρk ρp Z →
        ResU.CompS (Z.del l) (ResU.single l (CellU.mutOf A v'' χ hχ P'' hw'')) Z →
        (Z.del l).InStratum (↓A) →
        (∀ u r, SPropS.toU (P'' u) r → SPropS.toU (F k u) r) →
        ResU.CompS χ (ResU.single l (CellU.ownOf v'')) W'' → ResU.CompS (Z.del l) W'' ρkL →
        cancelOKN en k ls K ρk → cancelOKN en' k ls K ρkL)
    {Q : PostN} :
    ∀ n j, n ≤ j → ∀ ls e (v : Val) (ρP ρlP ρb ρ : WRes) (houtP : ρP.InStratum A),
      ρb.InStratum (↓A) → ∀ (P : Val → SPropS Loc Val A),
      (∀ u r, SPropS.toU (P u) r → SPropS.toU (F j u) r) → ∀ (hwit : P v ⟨ρP, houtP⟩),
      ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP → ResU.CompS ρlP ρb ρ →
      (∀ BM, ResU.CompS ρb (ResU.single l (CellU.mutOf A v ρP houtP P hwit)) BM →
        erwp (ℍ := ℍ) (Φ.set l A F) (opTableN T) (MFPost l A F Q) n ls e BM) →
      erwp (ℍ := ℍ) Φ (opTableG T' (CellFold l A F)) Q n ls e ρ := by
  intro n j hjn ls e v ρP ρlP ρb ρ houtP houtb P hPF hwit hclP hcρ hA
  rw [erwp_eq_erwpK_of (opTableGK_lift A T' (CellFold l A F)) Φ Q]
  refine erwpK_M_frameTF (V := fun _ _ => True) (Φ := fun _ => Φ) (Inv := fun _ => True)
    (flI := fun _ => A) (flO := fun _ => A) (Ti := fun _ => liftTabK T)
    (To := fun _ => liftTabK T') (Q := fun _ => Q) hF
    (fun _ => hT.toCR.lift)
    (liftTabK_abort fun m i en h => (hT.entry m i en h).1)
    (canFold_lift fun m i en en' h h' _ hq => hcan m i en en' h h' hq)
    (fun _ _ => foldTwin_lift (hTT') A l A) n j hjn () trivial ls e v ρP ρlP ρb ρ houtP houtb
    P hPF hwit hclP hcρ fun BM hBM => ?_
  have h := hA BM hBM
  rw [erwp_opTableN_eq_erwpK A] at h
  exact h


/-! ### At the typed world -/

/-- **The Mut Frame at the typed world** (`erwpK_M_frameCR` at `KW`). The borrowed run's entries
owe along `KW.Owed` at the lend's world (`KW.lend`, its view `Φ.set ℓ A F`, `KW.lend_view`) at the
floor bound `A`; the lender's, along `KW.Owed` at its own world at its floor; the frame's invariant
is `FoldInv A`. `FoldTwin` is `foldTwin_owed`. -/
theorem erwpK_M_frameCR_KW {V : KW → KW → Prop} {Φ : KW → LocFam} {l : Loc} {A : Life}
    {F : Nat → Val → SPropS Loc Val A} (hF : DownFam A F) {Ti To : KW → OpTabK KW}
    (hT : ∀ x, (Ti x).LendOKCR A) (hcan : CanFold (fun y => y.Θ.FoldInv A) Ti To l A F)
    (hTw : ∀ x, x.Θ.FoldInv A → ∀ m i en, Ti x m i = some en → ∃ en', To x m i = some en' ∧
      en'.q = en.q ∧ en'.abort = en.abort ∧ en'.PA = en.PA ∧ en'.PB = en.PB ∧ en'.wc = en.wc ∧
      (en.abort = false →
        (∀ f z ρ, (x.lend l A F).Owed f (z.lend l A F) ρ → en.wk f z ρ) ∧
        (∀ f z ρ, en'.wk f z ρ → x.Owed f z ρ)))
    {Q : KW → PostN} :
    KFrame (ℍ := ℍ) V Φ (fun y => y.Θ.FoldInv A) l A F (fun y => opTableK A (Ti y))
      (fun y => opTableRK y.lo (To y) (claimR l A F)) (fun y => MFPost l A F (Q y)) Q :=
  erwpK_M_frameCR (flI := fun _ => A) (flO := fun y => y.lo) hF hT hcan
    (fun x hx => foldTwin_owed hF hx (hTw x hx))

end BoCa.Fig16.LogRel.Core.Chain.SI

end
