import Core.Chain.SI.AFrameK
import Core.Chain.MFrameK835N

/-!
# The Mut Anti-Frames at `erwpK`  `[spec §19, §27, §62]`

`docs/new-core/scope-835-iframes.md`. Each Mut Anti-Frame across stops, restated at `erwpK` over
any world index (`erwpK_M_antiFrame*`), as an instance of `erwpK_M_antiFrameGen`
(`SI/AFrameK.lean`); and its `erwp` statement, word for word, proved again from the restated
frame at one world (`erwp_M_antiFrame*_of_K`).

The callback and the anti-frame stop at different tables (`Ti`, `To`), related across the seal
by `OpTabK.SealTwin` (`sealTwin_owed` at `KW`, by the share transfer). At one world both are the
lifted table and `SealTwin` holds of a twin (`sealTwin_lift`).
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

/-- **A Mut Anti-Frame at `erwpK`**: the cell `ℓ ↦ mut(β, v, ρ_v, F j)` beside `ρ_a`, opened for a
callback in `erwpK` at the tables `TbI` and the post `QI`, at a world where `Inv` holds: the
computation is in `erwpK` at the tables `TbO` and the post `Q`. -/
def AKFrame (V : ι → ι → Prop) (Φ : ι → LocFam) (Inv : ι → Prop) (l : Loc) (β : Life)
    (F : Nat → Val → SPropS Loc Val β) (TbI TbO : ι → TableK ι) (QI Q : ι → PostN) : Prop :=
  ∀ n (x : ι), Inv x → ∀ ls e (v : Val) (σP : WRes) (hstr : σP.InStratum β) (j : Nat)
    (hwit : F j v ⟨σP, hstr⟩) (ρa ρ : WRes),
    ResU.CompS (ResU.single l (CellU.mutOf β v σP hstr (F j) hwit)) ρa ρ →
    (∀ W X, ResU.CompS σP (ResU.single l (CellU.ownOf v)) W → ResU.CompS ρa W X →
      erwpK (ℍ := ℍ) V Φ TbI QI x n ls e X) →
    erwpK (ℍ := ℍ) V Φ TbO Q x n ls e ρ

/-- A frame at one outer table is a frame at every table allowing its stops. -/
theorem AKFrame.conv {V : ι → ι → Prop} {Φ : ι → LocFam} {Inv : ι → Prop} {l : Loc} {β : Life}
    {F : Nat → Val → SPropS Loc Val β} {TbI TbO TbO' : ι → TableK ι} {QI Q : ι → PostN}
    (h : AKFrame (ℍ := ℍ) V Φ Inv l β F TbI TbO QI Q) (hL : ∀ x, (TbO x).Local)
    (hc : ∀ x k ls t Ψ ρ, TbO x k ls t Ψ ρ → TbO' x k ls t Ψ ρ) :
    AKFrame (ℍ := ℍ) V Φ Inv l β F TbI TbO' QI Q := by
  intro n x hx ls e v σP hstr j hwit ρa ρ hsplit hA
  exact erwpK_mono (fun _ _ h => h) (fun _ _ _ _ _ h => h)
    (fun x k ls t Ψ Ψ' ρ hΨ hT => hc x k ls t Ψ' ρ (hL x k ls t Ψ Ψ' ρ hΨ hT)) n x ls e ρ
    (h n x hx ls e v σP hstr j hwit ρa ρ hsplit hA)

/-- A frame for one callback table and post is a frame for every table and post inside them. -/
theorem AKFrame.convIn {V : ι → ι → Prop} {Φ : ι → LocFam} {Inv : ι → Prop} {l : Loc} {β : Life}
    {F : Nat → Val → SPropS Loc Val β} {TbI TbI' TbO : ι → TableK ι} {QI QI' Q : ι → PostN}
    (h : AKFrame (ℍ := ℍ) V Φ Inv l β F TbI TbO QI Q) (hL : ∀ x, (TbI' x).Local)
    (hc : ∀ x k ls t Ψ ρ, TbI' x k ls t Ψ ρ → TbI x k ls t Ψ ρ)
    (hQ : ∀ y k ls v ρ, QI' y k ls v ρ → QI y k ls v ρ) :
    AKFrame (ℍ := ℍ) V Φ Inv l β F TbI' TbO QI' Q := by
  intro n x hx ls e v σP hstr j hwit ρa ρ hsplit hA
  exact h n x hx ls e v σP hstr j hwit ρa ρ hsplit fun W X hW hX =>
    erwpK_mono (fun _ _ h => h) hQ
      (fun x k ls t Ψ Ψ' ρ hΨ hT => hc x k ls t Ψ' ρ (hL x k ls t Ψ Ψ' ρ hΨ hT)) n x ls e X
      (hA W X hW hX)

theorem performStopGK_noRaise {fl : ι → Life} {T : ι → OpTabK ι} {G : ι → ShareG} (x : ι)
    (k : Nat) (ls : List SRec) (t : Expr) (Ψ : ContK ι) (ρ : WRes)
    (h : performStopGK (fl x) (T x) (G x) k ls t Ψ ρ) :
    BoLo.or (performStopGK (fl x) (T x) (G x) k ls t Ψ)
      ((fun _ _ _ _ _ _ => False : ι → TableK ι) x k ls t Ψ) ρ :=
  Or.inl h

theorem performStopK_raise {fl : ι → Life} {T : ι → OpTabK ι} (x : ι) (k : Nat)
    (ls : List SRec) (t : Expr) (Ψ : ContK ι) (ρ : WRes)
    (h : BoLo.or (performStopK (fl x) (T x) k ls t Ψ)
      ((fun _ _ _ _ _ _ => False : ι → TableK ι) x k ls t Ψ) ρ) :
    opTableK (fl x) (T x) k ls t Ψ ρ :=
  h.elim Or.inl False.elim

theorem OpTabK.SealTwin.twin {Inv : ι → Prop} {lo lo' : Life} {Ti To : OpTabK ι} {l : Loc}
    {β : Life} {F : Nat → Val → SPropS Loc Val β} (h : Ti.SealTwin Inv lo lo' To l β F) :
    Ti.Twin To := by
  intro m i en hTe
  obtain ⟨en', h₁, h₂, h₃, h₄, h₅, h₆, -⟩ := h m i en hTe
  exact ⟨en', h₁, h₂, h₃, h₄, h₅, h₆⟩

/-! ### `erwp_M_antiFrame` -/

/-- **Mut Anti-Frame at `erwpK` across Kripke stops** (`erwp_M_antiFrame`): a table of
must-resume stops, the callback's stops guarded by the fold. -/
theorem erwpK_M_antiFrame {V : ι → ι → Prop} {Φ : ι → LocFam} {Inv : ι → Prop}
    (hΦ : ∀ x, Inv x → (Φ x).Down) {l : Loc} {β : Life} {F : Nat → Val → SPropS Loc Val β}
    (hF : ∀ x, Inv x → Φ x l = some ⟨β, F⟩) {flI flO : ι → Life} {Ti To : ι → OpTabK ι}
    (hT : ∀ x m i en, Ti x m i = some en → en.abort = false → en.q = .lin ∧ en.wc = extF)
    (hTT : ∀ x, Inv x → (Ti x).SealTwin Inv (flI x) (flO x) (To x) l β F) {Q : ι → PostN} :
    AKFrame (ℍ := ℍ) V Φ Inv l β F (fun y => opTableGK (flI y) (Ti y) (CellFold l β F))
      (fun y => opTableK (flO y) (To y)) (fun y => AFPost l β F (Q y)) Q :=
  AKFrame.convIn (AKFrame.conv
    (erwpK_M_antiFrameGen (G := fun _ => CellFold l β F)
      (RI := (fun _ _ _ _ _ _ => False : ι → TableK ι))
      (RO := (fun _ _ _ _ _ _ => False : ι → TableK ι)) hΦ hF
      (fun x m i en h ha => ⟨by rw [(hT x m i en h ha).1]; decide, (hT x m i en h ha).2⟩) hTT
      (fun _ _ _ _ h => h) (asealCan_of_lin fun x m i en h ha => (hT x m i en h ha).1)
      (fun _ _ => asealRaise_none _))
    (fun _ => or_local (performStopK_local _ _) (fun _ _ _ _ _ _ h => h)) performStopK_raise)
    (fun _ => performStopGK_local _ _ _) performStopGK_noRaise (fun _ _ _ _ _ h => h)

/-- `erwp_M_antiFrame` from `erwpK_M_antiFrame`. -/
theorem erwp_M_antiFrame_of_K {Φ : LocFam} (hΦ : Φ.Down) {l : Loc} {β : Life}
    {F : Nat → Val → SPropS Loc Val β} (hF : Φ l = some ⟨β, F⟩) {T : OpTabN} (hT : T.AFOK)
    {Q : PostN} :
    ∀ n ls e (v : Val) (σP : WRes) (hstr : σP.InStratum β) (j : Nat) (hwit : F j v ⟨σP, hstr⟩)
      (ρa ρ : WRes),
      ResU.CompS (ResU.single l (CellU.mutOf β v σP hstr (F j) hwit)) ρa ρ →
      (∀ W X, ResU.CompS σP (ResU.single l (CellU.ownOf v)) W → ResU.CompS ρa W X →
        erwp (ℍ := ℍ) Φ (opTableG T (CellFold l β F)) (AFPost l β F Q) n ls e X) →
      erwp (ℍ := ℍ) Φ (opTableN T) Q n ls e ρ := by
  intro n ls e v σP hstr j hwit ρa ρ hsplit hA
  rw [erwp_opTableN_eq_erwpK β]
  refine erwpK_M_antiFrame (V := fun _ _ => True) (Φ := fun _ => Φ) (Inv := fun _ => True)
    (flI := fun _ => β) (flO := fun _ => β) (Ti := fun _ => liftTabK T)
    (To := fun _ => liftTabK T) (Q := fun _ => Q) (fun _ _ => hΦ) (fun _ _ => hF)
    (fun _ m i en h => by
      obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some h
      exact hT m i en₀ h₀)
    (fun _ _ => sealTwin_lift (OpTabN.twin_refl T) β l β F) n () trivial ls e v σP hstr j hwit
    ρa ρ hsplit fun W X hW hX => ?_
  have h := hA W X hW hX
  rw [erwp_eq_erwpK_of (opTableGK_lift β T (CellFold l β F)) Φ _] at h
  exact h

/-! ### The other variants -/

/-- **Mut Anti-Frame at `erwpK` across Kripke stops**, cancellable stops at the twin, the
callback's stops guarded by the fold (`erwp_M_antiFrameC`). -/
theorem erwpK_M_antiFrameC {V : ι → ι → Prop} {Φ : ι → LocFam} {Inv : ι → Prop}
    (hΦ : ∀ x, Inv x → (Φ x).Down) {l : Loc} {β : Life} {F : Nat → Val → SPropS Loc Val β}
    (hF : ∀ x, Inv x → Φ x l = some ⟨β, F⟩) {flI flO : ι → Life} {Ti To : ι → OpTabK ι}
    (hT : ∀ x m i en, Ti x m i = some en → en.abort = false → en.q ≠ .unr ∧ en.wc = extF)
    (hTT : ∀ x, Inv x → (Ti x).SealTwin Inv (flI x) (flO x) (To x) l β F)
    (hcan : ASealCan Inv Ti To l β F) {Q : ι → PostN} :
    AKFrame (ℍ := ℍ) V Φ Inv l β F (fun y => opTableGK (flI y) (Ti y) (CellFold l β F))
      (fun y => opTableK (flO y) (To y)) (fun y => AFPost l β F (Q y)) Q :=
  AKFrame.convIn (AKFrame.conv
    (erwpK_M_antiFrameGen (G := fun _ => CellFold l β F)
      (RI := (fun _ _ _ _ _ _ => False : ι → TableK ι))
      (RO := (fun _ _ _ _ _ _ => False : ι → TableK ι)) hΦ hF hT hTT
      (fun _ _ _ _ h => h) hcan (fun _ _ => asealRaise_none _))
    (fun _ => or_local (performStopK_local _ _) (fun _ _ _ _ _ _ h => h)) performStopK_raise)
    (fun _ => performStopGK_local _ _ _) performStopGK_noRaise (fun _ _ _ _ _ h => h)

/-- `T`'s entries are `claimT`'s, up to the cancel obligation. -/
theorem claimT_twinRev (T : OpTabN) (Φ : LocFam) (T₁ : OpTabN) (R : Nat → WProp) :
    (@OpTabN.claimT ℍ _ T Φ T₁ R).Twin T := by
  intro m i en' h
  obtain ⟨en, hTe, rfl⟩ := claimT_some h
  refine ⟨en, hTe, ?_⟩
  by_cases hq : en.q = .cancel <;> simp [hq]

/-- **`erwp_M_antiFrameC`'s cancel obligations at one world**: the anti-frame's cancel run at `T`'s
cancellable stop is the callback's at `claimT`'s, the cell sealed at its `raise`
(`erwp_M_antiFrame_cancelRun`). -/
theorem asealCan_claimT {Φ : LocFam} (hΦ : Φ.Down) {l : Loc} {β : Life}
    {F : Nat → Val → SPropS Loc Val β} (hF : Φ l = some ⟨β, F⟩) {T : OpTabN}
    (hT : ∀ m i en, T m i = some en → en.abort = false → en.q ≠ .unr ∧ en.wc = extF)
    (hfin : ∀ m i en, T m i = some en → en.q = .cancel →
      en.fin = some (cancelOblN (ℍ := ℍ) Φ OpTabN.empty)) :
    ASealCan (fun _ : Unit => True)
      (fun _ => liftTabK (@OpTabN.claimT ℍ _ T Φ OpTabN.empty (claimR l β F)))
      (fun _ => liftTabK T) l β F := by
  intro _ _ m i en en' hT' hTe ha hql _ _ k ls K w σ h hw R ρk' hRk hX
  obtain ⟨enI, hI, rfl⟩ := liftTabK_some hT'
  obtain ⟨enO, hO, rfl⟩ := liftTabK_some hTe
  obtain ⟨en₁, h₁, hen⟩ := claimT_some hI
  rw [hO] at h₁
  cases Option.some.inj h₁
  have hqI : enI.q = enO.q := by subst hen; by_cases hq : enO.q = .cancel <;> simp [hq]
  have hab : enO.abort = false := by
    have : enI.abort = enO.abort := by subst hen; by_cases hq : enO.q = .cancel <;> simp [hq]
    exact this ▸ ha
  have hqc : enO.q = .cancel := by
    have h1 := (hT m i enO hO hab).1
    have h2 : enO.q ≠ .lin := hqI ▸ hql
    cases h : enO.q <;> simp_all
  refine (cancelOKK_liftEntK enO k ls K ρk').mpr fun P hP => ?_
  rw [hfin m i enO hO hqc] at hP
  cases hP
  have hrun : ∀ W X, ResU.CompS σ (ResU.single l (CellU.ownOf w)) W → ResU.CompS R W X →
      erwp (ℍ := ℍ) Φ (cancelTabR OpTabN.empty (claimR l β F)) (fun _ _ _ _ => False) k ls
        (K.dead.plug (raiseE (.val (cancelVal none)))) X := by
    intro W X hW hX'
    have hc := (cancelOKK_liftEntK enI k ls K X).mp (hX W X hW hX')
    subst hen
    simp only [hqc, if_true] at hc
    exact hc _ rfl
  exact erwp_M_antiFrame_cancelRun hΦ hF k ls _ w σ h k hw R ρk' hRk hrun

/-- `erwp_M_antiFrameC` from `erwpK_M_antiFrameC`. -/
theorem erwp_M_antiFrameC_of_K {Φ : LocFam} (hΦ : Φ.Down) {l : Loc} {β : Life}
    {F : Nat → Val → SPropS Loc Val β} (hF : Φ l = some ⟨β, F⟩) {T : OpTabN}
    (hT : ∀ m i en, T m i = some en → en.abort = false → en.q ≠ .unr ∧ en.wc = extF)
    (hfin : ∀ m i en, T m i = some en → en.q = .cancel →
      en.fin = some (cancelOblN (ℍ := ℍ) Φ OpTabN.empty))
    {Q : PostN} :
    ∀ n ls e (v : Val) (σP : WRes) (hstr : σP.InStratum β) (j : Nat) (hwit : F j v ⟨σP, hstr⟩)
      (ρa ρ : WRes),
      ResU.CompS (ResU.single l (CellU.mutOf β v σP hstr (F j) hwit)) ρa ρ →
      (∀ W X, ResU.CompS σP (ResU.single l (CellU.ownOf v)) W → ResU.CompS ρa W X →
        erwp (ℍ := ℍ) Φ (opTableG (@OpTabN.claimT ℍ _ T Φ OpTabN.empty (claimR l β F))
          (CellFold l β F)) (AFPost l β F Q) n ls e X) →
      erwp (ℍ := ℍ) Φ (opTableN T) Q n ls e ρ := by
  intro n ls e v σP hstr j hwit ρa ρ hsplit hA
  rw [erwp_opTableN_eq_erwpK β]
  refine erwpK_M_antiFrameC (V := fun _ _ => True) (Φ := fun _ => Φ) (Inv := fun _ => True)
    (flI := fun _ => β) (flO := fun _ => β)
    (Ti := fun _ => liftTabK (@OpTabN.claimT ℍ _ T Φ OpTabN.empty (claimR l β F)))
    (To := fun _ => liftTabK T) (Q := fun _ => Q) (fun _ _ => hΦ) (fun _ _ => hF)
    (fun _ m i en h ha => by
      obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some h
      obtain ⟨en', h', hq, hab, -, -, hwc⟩ := claimT_twinRev T Φ OpTabN.empty (claimR l β F) m i
        en₀ h₀
      have := hT m i en' h' (hab.trans ha)
      exact ⟨by show en₀.q ≠ .unr; rw [← hq]; exact this.1,
        by show en₀.wc = extF; rw [← hwc]; exact this.2⟩)
    (fun _ _ => sealTwin_lift (claimT_twinRev T Φ OpTabN.empty (claimR l β F)) β l β F)
    (asealCan_claimT hΦ hF hT hfin) n () trivial ls e v σP hstr j hwit ρa ρ hsplit
    fun W X hW hX => ?_
  have h := hA W X hW hX
  rw [erwp_eq_erwpK_of (opTableGK_lift β _ (CellFold l β F)) Φ _] at h
  exact h

/-- **Mut Anti-Frame at `erwpK` across Kripke stops, raises and layered cancel runs**
(`erwp_M_antiFrameCR`). -/
theorem erwpK_M_antiFrameCR {V : ι → ι → Prop} {Φ : ι → LocFam} {Inv : ι → Prop}
    (hΦ : ∀ x, Inv x → (Φ x).Down) {l : Loc} {β : Life} {F : Nat → Val → SPropS Loc Val β}
    (hF : ∀ x, Inv x → Φ x l = some ⟨β, F⟩) {flI flO : ι → Life} {Ti To : ι → OpTabK ι}
    (hT : ∀ x m i en, Ti x m i = some en → en.abort = false → en.q ≠ .unr ∧ en.wc = extF)
    (hTT : ∀ x, Inv x → (Ti x).SealTwin Inv (flI x) (flO x) (To x) l β F)
    {G : ShareG} (hG : ∀ k ls ρ, G k ls ρ → CellFold l β F k ls ρ)
    {Rin Rout : Nat → WProp} (hRin : ∀ k ρ, Rin k ρ → claimR l β F k ρ)
    (hRout : ∀ k (w : Val) (σ : WRes) (h : σ.InStratum β) (hw : F k w ⟨σ, h⟩),
      Rout k (ResU.single l (CellU.mutOf β w σ h (F k) hw)))
    (hcan : ASealCan Inv Ti To l β F) {Q : ι → PostN} :
    AKFrame (ℍ := ℍ) V Φ Inv l β F (fun y => opTableGRK (flI y) (Ti y) G Rin)
      (fun y => opTableRK (flO y) (To y) Rout) (fun y => AFPost l β F (Q y)) Q :=
  erwpK_M_antiFrameGen (G := fun _ => G) (RI := fun y => raiseStopRK (Ti y) Rin)
    (RO := fun y => raiseStopRK (To y) Rout) hΦ hF hT hTT (fun _ => hG) hcan
    (fun x hx => asealRaise_claim (hTT x hx).twin hRin hRout)

/-- `erwp_M_antiFrameCR` from `erwpK_M_antiFrameCR`. -/
theorem erwp_M_antiFrameCR_of_K {Φ : LocFam} (hΦ : Φ.Down) {l : Loc} {β : Life}
    {F : Nat → Val → SPropS Loc Val β} (hF : Φ l = some ⟨β, F⟩) {T T' : OpTabN}
    (hTT' : T.Twin T')
    (hT : ∀ m i en, T m i = some en → en.abort = false → en.q ≠ .unr ∧ en.wc = extF)
    {G : ShareG} (hG : ∀ k ls ρ, G k ls ρ → CellFold l β F k ls ρ)
    {Rin Rout : Nat → WProp} (hRin : ∀ k ρ, Rin k ρ → claimR l β F k ρ)
    (hRout : ∀ k (w : Val) (σ : WRes) (h : σ.InStratum β) (hw : F k w ⟨σ, h⟩),
      Rout k (ResU.single l (CellU.mutOf β w σ h (F k) hw)))
    (hcan : ∀ m i en en', T m i = some en → T' m i = some en' → en.abort = false →
      en.q ≠ .lin → ∀ k ls (K : Kont) (w : Val) (σ : WRes) (h : σ.InStratum β)
        (hw : F k w ⟨σ, h⟩) (R ρk' : WRes),
        ResU.CompS (ResU.single l (CellU.mutOf β w σ h (F k) hw)) R ρk' →
        (∀ W X, ResU.CompS σ (ResU.single l (CellU.ownOf w)) W → ResU.CompS R W X →
          cancelOKN en k ls K X) →
        cancelOKN en' k ls K ρk')
    {Q : PostN} :
    ∀ n ls e (v : Val) (σP : WRes) (hstr : σP.InStratum β) (j : Nat) (hwit : F j v ⟨σP, hstr⟩)
      (ρa ρ : WRes),
      ResU.CompS (ResU.single l (CellU.mutOf β v σP hstr (F j) hwit)) ρa ρ →
      (∀ W X, ResU.CompS σP (ResU.single l (CellU.ownOf v)) W → ResU.CompS ρa W X →
        erwp (ℍ := ℍ) Φ (opTableGR T G Rin) (AFPost l β F Q) n ls e X) →
      erwp (ℍ := ℍ) Φ (opTableR T' Rout) Q n ls e ρ := by
  intro n ls e v σP hstr j hwit ρa ρ hsplit hA
  rw [erwp_eq_erwpK_of (opTableRK_lift β T' Rout) Φ Q]
  refine erwpK_M_antiFrameCR (V := fun _ _ => True) (Φ := fun _ => Φ) (Inv := fun _ => True)
    (flI := fun _ => β) (flO := fun _ => β) (Ti := fun _ => liftTabK T)
    (To := fun _ => liftTabK T') (Q := fun _ => Q) (fun _ _ => hΦ) (fun _ _ => hF)
    (fun _ m i en h => by
      obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some h
      exact hT m i en₀ h₀)
    (fun _ _ => sealTwin_lift hTT' β l β F) hG hRin hRout (asealCan_lift hcan) n () trivial ls e
    v σP hstr j hwit ρa ρ hsplit fun W X hW hX => ?_
  have h := hA W X hW hX
  rw [erwp_eq_erwpK_of (opTableGRK_lift β T G Rin) Φ _] at h
  exact h

/-- **Mut Anti-Frame at `erwpK` across Kripke stops over a cancel run that stops**
(`erwp_M_antiFrame_cancelRunCR`). -/
theorem erwpK_M_antiFrame_cancelRunCR {V : ι → ι → Prop} {Φ : ι → LocFam} {Inv : ι → Prop}
    (hΦ : ∀ x, Inv x → (Φ x).Down) {l : Loc} {β : Life} {F : Nat → Val → SPropS Loc Val β}
    (hF : ∀ x, Inv x → Φ x l = some ⟨β, F⟩) {flI flO : ι → Life} {Ti To : ι → OpTabK ι}
    (hT : ∀ x m i en, Ti x m i = some en → en.abort = false → en.q ≠ .unr ∧ en.wc = extF)
    (hTT : ∀ x, Inv x → (Ti x).SealTwin Inv (flI x) (flO x) (To x) l β F)
    {G : ShareG} (hG : ∀ k ls ρ, G k ls ρ → CellFold l β F k ls ρ)
    {Rin Rout : Nat → WProp} (hRin : ∀ k ρ, Rin k ρ → claimR l β F k ρ)
    (hRout : ∀ k (w : Val) (σ : WRes) (h : σ.InStratum β) (hw : F k w ⟨σ, h⟩),
      Rout k (ResU.single l (CellU.mutOf β w σ h (F k) hw)))
    (hcan : ASealCan Inv Ti To l β F) :
    AKFrame (ℍ := ℍ) V Φ Inv l β F (fun y => cancelTabGRK (flI y) (Ti y) G Rin)
      (fun y => cancelTabRK (flO y) (To y) Rout) (fun _ _ _ _ _ => False)
      (fun _ _ _ _ _ => False) :=
  AKFrame.convIn
    (erwpK_M_antiFrameGen (G := fun _ => G) (RI := fun y => cancelRaiseRK (Ti y) Rin)
      (RO := fun y => cancelRaiseRK (To y) Rout) (Q := fun _ _ _ _ _ => False) hΦ hF hT hTT
      (fun _ => hG) hcan (fun x hx => asealCancel_claim (hTT x hx).twin hRin hRout))
    (fun _ => or_local (performStopGK_local _ _ _) (cancelRaiseRK_free _ _))
    (fun _ _ _ _ _ _ h => h) (fun _ _ _ _ _ h => h.elim)

/-- `erwp_M_antiFrame_cancelRunCR` from `erwpK_M_antiFrame_cancelRunCR`. -/
theorem erwp_M_antiFrame_cancelRunCR_of_K {Φ : LocFam} (hΦ : Φ.Down) {l : Loc} {β : Life}
    {F : Nat → Val → SPropS Loc Val β} (hF : Φ l = some ⟨β, F⟩) {T T' : OpTabN}
    (hTT' : T.Twin T')
    (hT : ∀ m i en, T m i = some en → en.abort = false → en.q ≠ .unr ∧ en.wc = extF)
    {G : ShareG} (hG : ∀ k ls ρ, G k ls ρ → CellFold l β F k ls ρ)
    {Rin Rout : Nat → WProp} (hRin : ∀ k ρ, Rin k ρ → claimR l β F k ρ)
    (hRout : ∀ k (w : Val) (σ : WRes) (h : σ.InStratum β) (hw : F k w ⟨σ, h⟩),
      Rout k (ResU.single l (CellU.mutOf β w σ h (F k) hw)))
    (hcan : ∀ m i en en', T m i = some en → T' m i = some en' → en.abort = false →
      en.q ≠ .lin → ∀ k ls (K : Kont) (w : Val) (σ : WRes) (h : σ.InStratum β)
        (hw : F k w ⟨σ, h⟩) (R ρk' : WRes),
        ResU.CompS (ResU.single l (CellU.mutOf β w σ h (F k) hw)) R ρk' →
        (∀ W X, ResU.CompS σ (ResU.single l (CellU.ownOf w)) W → ResU.CompS R W X →
          cancelOKN en k ls K X) →
        cancelOKN en' k ls K ρk') :
    ∀ n ls e (v : Val) (σP : WRes) (hstr : σP.InStratum β) (j : Nat) (hwit : F j v ⟨σP, hstr⟩)
      (ρa ρ : WRes),
      ResU.CompS (ResU.single l (CellU.mutOf β v σP hstr (F j) hwit)) ρa ρ →
      (∀ W X, ResU.CompS σP (ResU.single l (CellU.ownOf v)) W → ResU.CompS ρa W X →
        erwp (ℍ := ℍ) Φ (cancelTabGR T G Rin) (fun _ _ _ _ => False) n ls e X) →
      erwp (ℍ := ℍ) Φ (cancelTabR T' Rout) (fun _ _ _ _ => False) n ls e ρ := by
  intro n ls e v σP hstr j hwit ρa ρ hsplit hA
  rw [erwp_eq_erwpK_of (cancelTabRK_lift β T' Rout) Φ _]
  refine erwpK_M_antiFrame_cancelRunCR (V := fun _ _ => True) (Φ := fun _ => Φ)
    (Inv := fun _ => True) (flI := fun _ => β) (flO := fun _ => β) (Ti := fun _ => liftTabK T)
    (To := fun _ => liftTabK T') (fun _ _ => hΦ) (fun _ _ => hF)
    (fun _ m i en h => by
      obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some h
      exact hT m i en₀ h₀)
    (fun _ _ => sealTwin_lift hTT' β l β F) hG hRin hRout (asealCan_lift hcan) n () trivial ls e
    v σP hstr j hwit ρa ρ hsplit fun W X hW hX => ?_
  have h := hA W X hW hX
  rw [erwp_eq_erwpK_of (cancelTabGRK_lift β T G Rin) Φ _] at h
  exact h

/-! ### At the typed world -/

/-- **The Mut Anti-Frame at the typed world** (`erwpK_M_antiFrameCR` at `KW`, at the world's
view). The callback's entries and the anti-frame's owe along `KW.Owed` at the same world, at the
same floor bound; the frame's invariant is `KW.SealInv` (a valid location typing, the cell's key,
the view at the cell's lifetime). `SealTwin` is `sealTwin_owed`. -/
theorem erwpK_M_antiFrameCR_KW {V : KW → KW → Prop} {l : Loc} {β : Life}
    {F : Nat → Val → SPropS Loc Val β} {Ti To : KW → OpTabK KW}
    (hT : ∀ x m i en, Ti x m i = some en → en.abort = false → en.q ≠ .unr ∧ en.wc = extF)
    (hTw : ∀ x, KW.SealInv l β F x → ∀ m i en, Ti x m i = some en → ∃ en', To x m i = some en' ∧
      en'.q = en.q ∧ en'.abort = en.abort ∧ en'.PA = en.PA ∧ en'.PB = en.PB ∧ en'.wc = en.wc ∧
      (en.abort = false →
        (∀ f z ρ, x.Owed f z ρ → en.wk f z ρ) ∧ (∀ f z ρ, en'.wk f z ρ → x.Owed f z ρ)))
    {G : ShareG} (hG : ∀ k ls ρ, G k ls ρ → CellFold l β F k ls ρ)
    {Rin Rout : Nat → WProp} (hRin : ∀ k ρ, Rin k ρ → claimR l β F k ρ)
    (hRout : ∀ k (w : Val) (σ : WRes) (h : σ.InStratum β) (hw : F k w ⟨σ, h⟩),
      Rout k (ResU.single l (CellU.mutOf β w σ h (F k) hw)))
    (hcan : ASealCan (KW.SealInv l β F) Ti To l β F) {Q : KW → PostN} :
    AKFrame (ℍ := ℍ) V (fun y => y.Θ.view y.c) (KW.SealInv l β F) l β F
      (fun y => opTableGRK y.lo (Ti y) G Rin) (fun y => opTableRK y.lo (To y) Rout)
      (fun y => AFPost l β F (Q y)) Q :=
  erwpK_M_antiFrameCR (flI := fun y => y.lo) (flO := fun y => y.lo)
    (fun x hx => LocTy.view_down hx.1.1 x.c) (fun x hx => kw_seal_view x hx) hT
    (fun x hx => sealTwin_owed hx.2.1 (hTw x hx)) hG hRin hRout hcan

end BoCa.Fig16.LogRel.Core.Chain.SI

end
