import Core.Chain.SI.RFrameK
import Core.Chain.MFrameK835N

/-!
# The reborrow frames at `erwpK`  `[spec §19, §27, §62]`

`docs/new-core/scope-835-iframes.md`. Each reborrow frame across stops (`[TR]` 6.150), restated
at `erwpK` over any world index (`erwpK_reb*`), as an instance of `erwpK_rebGenK`
(`SI/RFrameK.lean`); and its `erwp` statement, word for word, proved again from the restated frame
at one world (`erwp_reb*_of_K`).

The borrowed run and the lender stop at different tables (`Ti`, `To`), related across the fold by
`OpTabK.RebTwin` (`rebTwin_owed` at `KW`, by the share transfer). At one world both are the lifted
table and `RebTwin` holds of a twin (`rebTwin_lift`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Head Kont performE raiseE cancelVal opPayload)
open BoCa.Lifetime (LSub LifeVar)

variable {ι : Type}

/-- **A reborrow frame at `erwpK`**: the lender holds `ρᵢ` and `ρ_b ∈ Res_β`, the borrowed
computation, handed `ρ_b ● χ`, is in `erwpK` at the tables `TbI` and the post `QI`, at a world where
`Inv` holds: the computation is in `erwpK` at the tables `TbO` and the post `Q`. -/
def RKFrame (V : ι → ι → Prop) (Φ : ι → LocFam) (Inv : ι → Prop) (β : Life) (ρi χ : WRes)
    (Ok : List SRec → Prop) (TbI TbO : ι → TableK ι) (QI Q : ι → PostN) : Prop :=
  ∀ n (x : ι), Inv x → ∀ ls e (ρb ρ : WRes), ResU.CompS ρi ρb ρ → ρb.InStratum β → Ok ls →
    (∀ Bχ, ResU.CompS ρb χ Bχ → erwpK (ℍ := ℍ) V Φ TbI QI x n ls e Bχ) →
    erwpK (ℍ := ℍ) V Φ TbO Q x n ls e ρ

/-- A frame for one borrowed post is a frame for every post inside it. -/
theorem RKFrame.postIn {V : ι → ι → Prop} {Φ : ι → LocFam} {Inv : ι → Prop} {β : Life}
    {ρi χ : WRes} {Ok : List SRec → Prop} {TbI TbO : ι → TableK ι} {QI QI' Q : ι → PostN}
    (h : RKFrame (ℍ := ℍ) V Φ Inv β ρi χ Ok TbI TbO QI Q) (hL : ∀ x, (TbI x).Local)
    (hQ : ∀ y k ls v ρ, QI' y k ls v ρ → QI y k ls v ρ) :
    RKFrame (ℍ := ℍ) V Φ Inv β ρi χ Ok TbI TbO QI' Q := by
  intro n x hx ls e ρb ρ hc hb hr hA
  exact h n x hx ls e ρb ρ hc hb hr fun Bχ hBχ =>
    erwpK_mono (fun _ _ h => h) hQ (fun x k ls t Ψ Ψ' ρ hΨ h => hL x k ls t Ψ Ψ' ρ hΨ h) n x ls
      e Bχ (hA Bχ hBχ)

/-! ### `erwp_rebGen` and `erwp_rebGen_cancelRun` -/

/-- **`[TR]` 6.150 at `erwpK` across Kripke stops, raises and layered cancel runs**
(`erwp_rebGen`). -/
theorem erwpK_rebGen {V : ι → ι → Prop} {Φ : ι → LocFam} {Inv : ι → Prop} {β : Life}
    {le : Loc} {s : LSet} {v : Val} {R : WRes} {hs : R.InStratum s.join} {χ : WRes}
    {Ok : List SRec → Prop} {Pv : WRes → WRes → Prop}
    (hE : ∀ x, Inv x →
      RebEntryGP (ℍ := ℍ) (Φ x) β (ResU.single le (CellU.immOf s v R hs)) χ R Ok Pv)
    (hreb : ResU.Reb β R χ)
    (hOk : ∀ (ls ls'' lsO : List SRec) (ψ Ks : WRes), Ok ls → (∀ y, y ∈ ls'' ↔ y ∈ ls) →
      ResU.CompS ψ (ResU.single le (CellU.immOf s v R hs)) Ks → extF ls'' lsO Ks → Ok lsO)
    {flI flO : ι → Life} {Ti To : ι → OpTabK ι} (hT : ∀ x, (Ti x).RebOKR β)
    (hTT : ∀ x, Inv x → (Ti x).RebTwin Inv (flI x) (flO x) (To x) β
      (ResU.single le (CellU.immOf s v R hs)) χ R Pv)
    (hcan : RebCanK Inv Ti To β (ResU.single le (CellU.immOf s v R hs)) χ R Ok)
    {Q : ι → PostN} :
    RKFrame (ℍ := ℍ) V Φ Inv β (ResU.single le (CellU.immOf s v R hs)) χ Ok
      (fun y => opTableK (flI y) (Ti y)) (fun y => opTableK (flO y) (To y))
      (fun y => RebPost β (Q y)) Q :=
  erwpK_rebGenK (RI := fun y => raiseStopK (Ti y)) (RO := fun y => raiseStopK (To y)) hE hreb hOk
    hT hTT hcan (fun x hx => rebRaise_same (hTT x hx).twin (hT x).pa)

/-- `erwp_rebGen` from `erwpK_rebGen`. -/
theorem erwp_rebGen_of_K {Φ : LocFam} {β : Life} {le : Loc} {s : LSet} {v : Val}
    {R : WRes} {hs : R.InStratum s.join} {χ : WRes} {Ok : List SRec → Prop}
    (hE : RebEntryG (ℍ := ℍ) Φ β (ResU.single le (CellU.immOf s v R hs)) χ R Ok)
    (hreb : ResU.Reb β R χ)
    (hOk : ∀ (ls ls'' lsO : List SRec) (ψ Ks : WRes), Ok ls → (∀ y, y ∈ ls'' ↔ y ∈ ls) →
      ResU.CompS ψ (ResU.single le (CellU.immOf s v R hs)) Ks → extF ls'' lsO Ks → Ok lsO)
    {Tb : OpTabN} (hT : Tb.RebOKR β)
    (hcan : RebClosed β (ResU.single le (CellU.immOf s v R hs)) χ Ok Tb) {Q : PostN} :
    ∀ n ls e (ρb ρ : WRes),
      ResU.CompS (ResU.single le (CellU.immOf s v R hs)) ρb ρ → ρb.InStratum β → Ok ls →
      (∀ Bχ, ResU.CompS ρb χ Bχ →
        erwp (ℍ := ℍ) Φ (opTableN Tb) (RebPost β Q) n ls e Bχ) →
      erwp (ℍ := ℍ) Φ (opTableN Tb) Q n ls e ρ := by
  intro n ls e ρb ρ hc hb hr hA
  rw [erwp_opTableN_eq_erwpK β]
  refine erwpK_rebGen (V := fun _ _ => True) (Φ := fun _ => Φ) (Inv := fun _ => True)
    (flI := fun _ => β) (flO := fun _ => β) (Ti := fun _ => liftTabK Tb)
    (To := fun _ => liftTabK Tb) (Q := fun _ => Q) (fun _ _ => hE.toP) hreb hOk
    (fun _ => hT.liftK) (fun _ _ => rebTwin_lift (OpTabN.twin_refl Tb) β β _ χ R _)
    (rebCanK_lift hreb hcan) n () trivial ls e ρb ρ hc hb hr fun Bχ hBχ => ?_
  have h := hA Bχ hBχ
  rw [erwp_opTableN_eq_erwpK β] at h
  exact h

/-- **`[TR]` 6.150 at `erwpK` over a cancel run** (`erwp_rebGen_cancelRun`). -/
theorem erwpK_rebGen_cancelRun {V : ι → ι → Prop} {Φ : ι → LocFam} {Inv : ι → Prop} {β : Life}
    {le : Loc} {s : LSet} {v : Val} {R : WRes} {hs : R.InStratum s.join} {χ : WRes}
    {Ok : List SRec → Prop} {Pv : WRes → WRes → Prop}
    (hE : ∀ x, Inv x →
      RebEntryGP (ℍ := ℍ) (Φ x) β (ResU.single le (CellU.immOf s v R hs)) χ R Ok Pv)
    (hreb : ResU.Reb β R χ)
    (hOk : ∀ (ls ls'' lsO : List SRec) (ψ Ks : WRes), Ok ls → (∀ y, y ∈ ls'' ↔ y ∈ ls) →
      ResU.CompS ψ (ResU.single le (CellU.immOf s v R hs)) Ks → extF ls'' lsO Ks → Ok lsO)
    {flI flO : ι → Life} {Ti To : ι → OpTabK ι} (hT : ∀ x, (Ti x).RebOKR β)
    (hTT : ∀ x, Inv x → (Ti x).RebTwin Inv (flI x) (flO x) (To x) β
      (ResU.single le (CellU.immOf s v R hs)) χ R Pv)
    (hcan : RebCanK Inv Ti To β (ResU.single le (CellU.immOf s v R hs)) χ R Ok) :
    RKFrame (ℍ := ℍ) V Φ Inv β (ResU.single le (CellU.immOf s v R hs)) χ Ok
      (fun y => cancelTabK (flI y) (Ti y)) (fun y => cancelTabK (flO y) (To y))
      (fun _ _ _ _ _ => False) (fun _ _ _ _ _ => False) :=
  RKFrame.postIn (erwpK_rebGenK (RI := fun y => cancelRaiseK (Ti y))
      (RO := fun y => cancelRaiseK (To y)) (Q := fun _ _ _ _ _ => False) hE hreb hOk hT hTT hcan
      (fun x hx => rebCancel_same (hTT x hx).twin (hT x).pa))
    (fun _ => or_local (performStopK_local _ _) (cancelRaiseK_free _)) (fun _ _ _ _ _ h => h.elim)

/-- `erwp_rebGen_cancelRun` from `erwpK_rebGen_cancelRun`. -/
theorem erwp_rebGen_cancelRun_of_K {Φ : LocFam} {β : Life} {le : Loc} {s : LSet} {v : Val}
    {R : WRes} {hs : R.InStratum s.join} {χ : WRes} {Ok : List SRec → Prop}
    (hE : RebEntryG (ℍ := ℍ) Φ β (ResU.single le (CellU.immOf s v R hs)) χ R Ok)
    (hreb : ResU.Reb β R χ)
    (hOk : ∀ (ls ls'' lsO : List SRec) (ψ Ks : WRes), Ok ls → (∀ y, y ∈ ls'' ↔ y ∈ ls) →
      ResU.CompS ψ (ResU.single le (CellU.immOf s v R hs)) Ks → extF ls'' lsO Ks → Ok lsO)
    {T₁ : OpTabN} (hT₁ : T₁.RebOKR β)
    (hcan : RebClosed β (ResU.single le (CellU.immOf s v R hs)) χ Ok T₁) :
    ∀ n ls e (ρb ρ : WRes),
      ResU.CompS (ResU.single le (CellU.immOf s v R hs)) ρb ρ → ρb.InStratum β → Ok ls →
      (∀ Bχ, ResU.CompS ρb χ Bχ →
        erwp (ℍ := ℍ) Φ (cancelTabN T₁) (fun _ _ _ _ => False) n ls e Bχ) →
      erwp (ℍ := ℍ) Φ (cancelTabN T₁) (fun _ _ _ _ => False) n ls e ρ := by
  intro n ls e ρb ρ hc hb hr hA
  rw [erwp_eq_erwpK_of (cancelTabK_lift β T₁) Φ _]
  refine erwpK_rebGen_cancelRun (V := fun _ _ => True) (Φ := fun _ => Φ) (Inv := fun _ => True)
    (flI := fun _ => β) (flO := fun _ => β) (Ti := fun _ => liftTabK T₁)
    (To := fun _ => liftTabK T₁) (fun _ _ => hE.toP) hreb hOk
    (fun _ => hT₁.liftK) (fun _ _ => rebTwin_lift (OpTabN.twin_refl T₁) β β _ χ R _)
    (rebCanK_lift hreb hcan) n () trivial ls e ρb ρ hc hb hr fun Bχ hBχ => ?_
  have h := hA Bχ hBχ
  rw [erwp_eq_erwpK_of (cancelTabK_lift β T₁) Φ _] at h
  exact h

/-! ### At the record's cell and at a chain view -/

/-- **`[TR]` 6.150 at `erwpK` across Kripke stops**, at the record's cell (`erwp_reborrow`): the
entry hands `hpost` the validity the typed discharge reads (`rebEntryGV_top`). -/
theorem erwpK_reborrow {V : ι → ι → Prop} {Φ : ι → LocFam} {Inv : ι → Prop} (r : FrameRec)
    (x : LifeVar) (hx : ¬ VFree x r.T) {β : Life} {s : LSet} {hs : r.R.InStratum s.join}
    (hS : TmplSpec r (tmpl r)) (hRβ : r.R.InStratum β)
    (hshape : vShape (r.T.immReborrow (.var x)) (r.δ.extend x β) r.v (canon r β))
    (hβs : ∀ y, s.mem y → β ⊑ y) {flI flO : ι → Life} {Ti To : ι → OpTabK ι}
    (hT : ∀ x, (Ti x).RebOKR β)
    (hlin : ∀ x m i en, Ti x m i = some en → en.abort = false → en.q = .lin)
    (hab : ∀ x m i en, Ti x m i = some en → en.abort = false)
    (hTT : ∀ x, Inv x → (Ti x).RebTwin Inv (flI x) (flO x) (To x) β
      (ResU.single r.le (CellU.immOf s r.v r.R hs)) (canon r β) r.R
      (fun w Y => ResU.Valid w ∧ ResU.Valid Y))
    {Q : ι → PostN} :
    RKFrame (ℍ := ℍ) V Φ Inv β (ResU.single r.le (CellU.immOf s r.v r.R hs)) (canon r β)
      (fun ls => r ∈ rsOf ls) (fun y => opTableK (flI y) (Ti y))
      (fun y => opTableK (flO y) (To y)) (fun y => RebPost β (Q y)) Q :=
  erwpK_rebGenK (RI := fun y => raiseStopK (Ti y)) (RO := fun y => raiseStopK (To y))
    (fun _ _ => rebEntryGV_top r x hx hS hRβ hshape hβs) (canon_reb hS hRβ) okKept_top hT hTT
    (rebCanK_of_lin hlin) (fun x _ => rebRaise_absurd (hab x) _)

/-- `erwp_reborrow` from `erwpK_reborrow`. -/
theorem erwp_reborrow_of_K {Φ : LocFam} (r : FrameRec) (x : LifeVar) (hx : ¬ VFree x r.T)
    {β : Life} {s : LSet} {hs : r.R.InStratum s.join} (hS : TmplSpec r (tmpl r))
    (hRβ : r.R.InStratum β)
    (hshape : vShape (r.T.immReborrow (.var x)) (r.δ.extend x β) r.v (canon r β))
    (hβs : ∀ y, s.mem y → β ⊑ y) {Tb : OpTabN} (hT : Tb.RebOK β) {Q : PostN} :
    ∀ n ls e (ρb ρ : WRes),
      ResU.CompS (ResU.single r.le (CellU.immOf s r.v r.R hs)) ρb ρ → ρb.InStratum β →
      r ∈ rsOf ls →
      (∀ Bχ, ResU.CompS ρb (canon r β) Bχ →
        erwp (ℍ := ℍ) Φ (opTableN Tb) (RebPost β Q) n ls e Bχ) →
      erwp (ℍ := ℍ) Φ (opTableN Tb) Q n ls e ρ := by
  intro n ls e ρb ρ hc hb hr hA
  rw [erwp_opTableN_eq_erwpK β]
  refine erwpK_reborrow (V := fun _ _ => True) (Φ := fun _ => Φ) (Inv := fun _ => True)
    (flI := fun _ => β) (flO := fun _ => β) (Ti := fun _ => liftTabK Tb)
    (To := fun _ => liftTabK Tb) (Q := fun _ => Q) r x hx hS hRβ hshape hβs
    (fun _ => hT.toR.liftK) (liftTabK_lin fun m i en h _ => (hT.entry m i en h).2.1)
    (liftTabK_abort fun m i en h => (hT.entry m i en h).1)
    (fun _ _ => rebTwin_lift (OpTabN.twin_refl Tb) β β _ _ _ _) n () trivial ls e ρb ρ hc hb hr
    fun Bχ hBχ => ?_
  have h := hA Bχ hBχ
  rw [erwp_opTableN_eq_erwpK β] at h
  exact h

/-- **`[TR]` 6.150 at `erwpK` over a cancel run**, at the record's cell
(`erwp_reborrow_cancelRun`). -/
theorem erwpK_reborrow_cancelRun {V : ι → ι → Prop} {Φ : ι → LocFam} {Inv : ι → Prop}
    (r : FrameRec) (x : LifeVar) (hx : ¬ VFree x r.T) {β : Life} {s : LSet}
    {hs : r.R.InStratum s.join} (hS : TmplSpec r (tmpl r)) (hRβ : r.R.InStratum β)
    (hshape : vShape (r.T.immReborrow (.var x)) (r.δ.extend x β) r.v (canon r β))
    (hβs : ∀ y, s.mem y → β ⊑ y) {flI flO : ι → Life} {Ti To : ι → OpTabK ι}
    (hT : ∀ x, (Ti x).RebOKR β)
    (hlin : ∀ x m i en, Ti x m i = some en → en.abort = false → en.q = .lin)
    (hTT : ∀ x, Inv x → (Ti x).RebTwin Inv (flI x) (flO x) (To x) β
      (ResU.single r.le (CellU.immOf s r.v r.R hs)) (canon r β) r.R
      (fun w Y => ResU.Valid w ∧ ResU.Valid Y)) :
    RKFrame (ℍ := ℍ) V Φ Inv β (ResU.single r.le (CellU.immOf s r.v r.R hs)) (canon r β)
      (fun ls => r ∈ rsOf ls) (fun y => cancelTabK (flI y) (Ti y))
      (fun y => cancelTabK (flO y) (To y)) (fun _ _ _ _ _ => False) (fun _ _ _ _ _ => False) :=
  erwpK_rebGen_cancelRun (fun _ _ => rebEntryGV_top r x hx hS hRβ hshape hβs) (canon_reb hS hRβ)
    okKept_top hT hTT (rebCanK_of_lin hlin)

/-- `erwp_reborrow_cancelRun` from `erwpK_reborrow_cancelRun`. -/
theorem erwp_reborrow_cancelRun_of_K {Φ : LocFam} (r : FrameRec) (x : LifeVar)
    (hx : ¬ VFree x r.T) {β : Life} {s : LSet} {hs : r.R.InStratum s.join}
    (hS : TmplSpec r (tmpl r)) (hRβ : r.R.InStratum β)
    (hshape : vShape (r.T.immReborrow (.var x)) (r.δ.extend x β) r.v (canon r β))
    (hβs : ∀ y, s.mem y → β ⊑ y) {T₁ : OpTabN} (hT : T₁.RebOK β) :
    ∀ n ls e (ρb ρ : WRes),
      ResU.CompS (ResU.single r.le (CellU.immOf s r.v r.R hs)) ρb ρ → ρb.InStratum β →
      r ∈ rsOf ls →
      (∀ Bχ, ResU.CompS ρb (canon r β) Bχ →
        erwp (ℍ := ℍ) Φ (cancelTabN T₁) (fun _ _ _ _ => False) n ls e Bχ) →
      erwp (ℍ := ℍ) Φ (cancelTabN T₁) (fun _ _ _ _ => False) n ls e ρ := by
  intro n ls e ρb ρ hc hb hr hA
  rw [erwp_eq_erwpK_of (cancelTabK_lift β T₁) Φ _]
  refine erwpK_reborrow_cancelRun (V := fun _ _ => True) (Φ := fun _ => Φ)
    (Inv := fun _ => True) (flI := fun _ => β) (flO := fun _ => β) (Ti := fun _ => liftTabK T₁)
    (To := fun _ => liftTabK T₁) r x hx hS hRβ hshape hβs
    (fun _ => hT.toR.liftK) (liftTabK_lin fun m i en h _ => (hT.entry m i en h).2.1)
    (fun _ _ => rebTwin_lift (OpTabN.twin_refl T₁) β β _ _ _ _) n () trivial ls e ρb ρ hc hb hr
    fun Bχ hBχ => ?_
  have h := hA Bχ hBχ
  rw [erwp_eq_erwpK_of (cancelTabK_lift β T₁) Φ _] at h
  exact h

/-- **`[TR]` 6.150 at `erwpK` across Kripke stops, cancellable ones included**, at the record's
cell (`erwp_reborrowT`). -/
theorem erwpK_reborrowT {V : ι → ι → Prop} {Φ : ι → LocFam} {Inv : ι → Prop} (r : FrameRec)
    (x : LifeVar) (hx : ¬ VFree x r.T) {β : Life} {s : LSet} {hs : r.R.InStratum s.join}
    (hS : TmplSpec r (tmpl r)) (hRβ : r.R.InStratum β)
    (hshape : vShape (r.T.immReborrow (.var x)) (r.δ.extend x β) r.v (canon r β))
    (hβs : ∀ y, s.mem y → β ⊑ y) {flI flO : ι → Life} {Ti To : ι → OpTabK ι}
    (hT : ∀ x, (Ti x).RebOKR β)
    (hab : ∀ x m i en, Ti x m i = some en → en.abort = false)
    (hTT : ∀ x, Inv x → (Ti x).RebTwin Inv (flI x) (flO x) (To x) β
      (ResU.single r.le (CellU.immOf s r.v r.R hs)) (canon r β) r.R
      (fun w Y => ResU.Valid w ∧ ResU.Valid Y))
    (hcan : RebCanK Inv Ti To β (ResU.single r.le (CellU.immOf s r.v r.R hs)) (canon r β) r.R
      (fun ls => r ∈ rsOf ls))
    {Q : ι → PostN} :
    RKFrame (ℍ := ℍ) V Φ Inv β (ResU.single r.le (CellU.immOf s r.v r.R hs)) (canon r β)
      (fun ls => r ∈ rsOf ls) (fun y => opTableK (flI y) (Ti y))
      (fun y => opTableK (flO y) (To y)) (fun y => RebPost β (Q y)) Q :=
  erwpK_rebGenK (RI := fun y => raiseStopK (Ti y)) (RO := fun y => raiseStopK (To y))
    (fun _ _ => rebEntryGV_top r x hx hS hRβ hshape hβs) (canon_reb hS hRβ) okKept_top hT hTT
    hcan (fun x _ => rebRaise_absurd (hab x) _)

/-- **`erwp_reborrowT`'s cancel obligations at one world**: the lender's cancel run at the folded
share is the borrowed continuation's, re-entered at the canonical image
(`erwp_reborrow_cancelRun`). -/
theorem rebCanK_cancelRun {Φ : LocFam} (r : FrameRec) (x : LifeVar) (hx : ¬ VFree x r.T)
    {β : Life} {s : LSet} {hs : r.R.InStratum s.join} (hS : TmplSpec r (tmpl r))
    (hRβ : r.R.InStratum β)
    (hshape : vShape (r.T.immReborrow (.var x)) (r.δ.extend x β) r.v (canon r β))
    (hβs : ∀ y, s.mem y → β ⊑ y) {Tb T₁ : OpTabN} (hT : Tb.RebOKC β) (hT₁ : T₁.RebOK β)
    (hfin : ∀ m i en, Tb m i = some en → en.q = .cancel →
      en.fin = some (cancelOblN (ℍ := ℍ) Φ T₁)) :
    RebCanK (fun _ : Unit => True) (fun _ => liftTabK Tb) (fun _ => liftTabK Tb) β
      (ResU.single r.le (CellU.immOf s r.v r.R hs)) (canon r β) r.R (fun ls => r ∈ rsOf ls) := by
  have hreb : ResU.Reb β r.R (canon r β) := canon_reb hS hRβ
  have hχsplit := ResU.restrictDom_split hreb
  have hχimm : NoOwn ((canon r β).restrictDom (r.R.restrict Kind.imm)) :=
    noOwn_of_imm fun m ψ e => ResU.reb_imm_image hreb (ResU.restrictDom_get_inv e)
  intro _ _ m i en en' hTe hTe' ha hql _ k ls K ρk ρp w ψ Ks hnp hkw hsplit hψβ hKs hr hin
  obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some hTe
  obtain ⟨en₀', h₀', rfl⟩ := liftTabK_some hTe'
  rw [h₀] at h₀'
  cases Option.some.inj h₀'
  have hqc : en₀.q = .cancel := by
    have h1 := (hT.entry m i en₀ h₀).2.1
    have h2 : en₀.q ≠ .lin := hql
    cases h : en₀.q <;> simp_all
  refine (cancelOKK_liftEntK en₀ k ls K Ks).mpr fun P hP => ?_
  rw [hfin m i en₀ h₀ hqc] at hP
  cases hP
  have hin' := (cancelOKK_liftEntK en₀ k ls K ρk).mp hin _ (hfin m i en₀ h₀ hqc)
  refine erwp_reborrow_cancelRun r x hx hS hRβ hshape hβs hT₁ k ls _ ψ Ks
    (ResU.CompS.comm hKs) hψβ hr (fun Bχ hBχ => ?_)
  obtain ⟨Xk, g, hXk, hXkg, hg⟩ :=
    rebReentry_split (σB := PMap.empty) (ResU.comp_empty_right ψ) hBχ hχsplit hsplit hkw hnp
      hχimm
  obtain rfl := ResU.CompS.functional hXk (ResU.comp_empty_right ρk)
  exact erwp_garbage hXkg hg hin'

/-- `erwp_reborrowT` from `erwpK_reborrowT`. -/
theorem erwp_reborrowT_of_K {Φ : LocFam} (r : FrameRec) (x : LifeVar) (hx : ¬ VFree x r.T)
    {β : Life} {s : LSet} {hs : r.R.InStratum s.join} (hS : TmplSpec r (tmpl r))
    (hRβ : r.R.InStratum β)
    (hshape : vShape (r.T.immReborrow (.var x)) (r.δ.extend x β) r.v (canon r β))
    {Tb T₁ : OpTabN} (hT : Tb.RebOKC β) (hT₁ : T₁.RebOK β)
    (hfin : ∀ m i en, Tb m i = some en → en.q = .cancel →
      en.fin = some (cancelOblN (ℍ := ℍ) Φ T₁)) (hβs : ∀ y, s.mem y → β ⊑ y) {Q : PostN} :
    ∀ n ls e (ρb ρ : WRes),
      ResU.CompS (ResU.single r.le (CellU.immOf s r.v r.R hs)) ρb ρ → ρb.InStratum β →
      r ∈ rsOf ls →
      (∀ Bχ, ResU.CompS ρb (canon r β) Bχ →
        erwp (ℍ := ℍ) Φ (opTableN Tb) (RebPost β Q) n ls e Bχ) →
      erwp (ℍ := ℍ) Φ (opTableN Tb) Q n ls e ρ := by
  intro n ls e ρb ρ hc hb hr hA
  rw [erwp_opTableN_eq_erwpK β]
  refine erwpK_reborrowT (V := fun _ _ => True) (Φ := fun _ => Φ) (Inv := fun _ => True)
    (flI := fun _ => β) (flO := fun _ => β) (Ti := fun _ => liftTabK Tb)
    (To := fun _ => liftTabK Tb) (Q := fun _ => Q) r x hx hS hRβ hshape hβs
    (fun _ => hT.toR.liftK) (liftTabK_abort fun m i en h => (hT.entry m i en h).1)
    (fun _ _ => rebTwin_lift (OpTabN.twin_refl Tb) β β _ _ _ _)
    (rebCanK_cancelRun r x hx hS hRβ hshape hβs hT hT₁ hfin) n () trivial ls e ρb ρ hc hb hr
    fun Bχ hBχ => ?_
  have h := hA Bχ hBχ
  rw [erwp_opTableN_eq_erwpK β] at h
  exact h

/-- **`[TR]` 6.150 at a chain view, at `erwpK` across Kripke stops** (`erwp_reborrowDeep`). -/
theorem erwpK_reborrowDeep {V : ι → ι → Prop} {Φ : ι → LocFam} {Inv : ι → Prop} (r : FrameRec)
    {p₀ : Option Loc} {l₀ : Loc} {S₀ : VTy} {u₀ : Val} (hch₀ : Chain r.R r.T r.v p₀ l₀ S₀ u₀)
    {w₀ : WRes} (x : LifeVar) (hx : ¬ VFree x S₀) {β : Life} {s : LSet}
    {hs : w₀.InStratum s.join} (hS : TmplSpecD r S₀ u₀ w₀ (tmplD r S₀ u₀ w₀))
    (hRβ : w₀.InStratum β) (hβc : (CellU.immOf s u₀ w₀ hs).InStratum β)
    (hshape : vShape (S₀.immReborrow (.var x)) (r.δ.extend x β) u₀ (canonD r S₀ u₀ w₀ β))
    {flI flO : ι → Life} {Ti To : ι → OpTabK ι} (hT : ∀ x, (Ti x).RebOKR β)
    (hlin : ∀ x m i en, Ti x m i = some en → en.abort = false → en.q = .lin)
    (hab : ∀ x m i en, Ti x m i = some en → en.abort = false)
    (hTT : ∀ x, Inv x → (Ti x).RebTwin Inv (flI x) (flO x) (To x) β
      (ResU.single l₀ (CellU.immOf s u₀ w₀ hs)) (canonD r S₀ u₀ w₀ β) w₀
      (fun w Y => ResU.Valid w ∧ ResU.Valid Y))
    {Q : ι → PostN} :
    RKFrame (ℍ := ℍ) V Φ Inv β (ResU.single l₀ (CellU.immOf s u₀ w₀ hs)) (canonD r S₀ u₀ w₀ β)
      (fun ls => r ∈ rsOf ls) (fun y => opTableK (flI y) (Ti y))
      (fun y => opTableK (flO y) (To y)) (fun y => RebPost β (Q y)) Q :=
  erwpK_rebGenK (RI := fun y => raiseStopK (Ti y)) (RO := fun y => raiseStopK (To y))
    (fun _ _ => rebEntryGV_deep r hch₀ x hx hS hRβ hβc hshape) (canonD_reb hS hRβ)
    (okKept_deep hch₀) hT hTT (rebCanK_of_lin hlin) (fun x _ => rebRaise_absurd (hab x) _)

/-- `erwp_reborrowDeep` from `erwpK_reborrowDeep`. -/
theorem erwp_reborrowDeep_of_K {Φ : LocFam} (r : FrameRec) {p₀ : Option Loc} {l₀ : Loc} {S₀ : VTy}
    {u₀ : Val} (hch₀ : Chain r.R r.T r.v p₀ l₀ S₀ u₀) {w₀ : WRes} (x : LifeVar) (hx : ¬ VFree x S₀)
    {β : Life} {s : LSet} {hs : w₀.InStratum s.join} (hS : TmplSpecD r S₀ u₀ w₀ (tmplD r S₀ u₀ w₀))
    (hRβ : w₀.InStratum β) (hβc : (CellU.immOf s u₀ w₀ hs).InStratum β)
    (hshape : vShape (S₀.immReborrow (.var x)) (r.δ.extend x β) u₀ (canonD r S₀ u₀ w₀ β))
    {Tb : OpTabN} (hT : Tb.RebOK β) {Q : PostN} :
    ∀ n ls e (ρb ρ : WRes),
      ResU.CompS (ResU.single l₀ (CellU.immOf s u₀ w₀ hs)) ρb ρ → ρb.InStratum β →
      r ∈ rsOf ls →
      (∀ Bχ, ResU.CompS ρb (canonD r S₀ u₀ w₀ β) Bχ →
        erwp (ℍ := ℍ) Φ (opTableN Tb) (RebPost β Q) n ls e Bχ) →
      erwp (ℍ := ℍ) Φ (opTableN Tb) Q n ls e ρ := by
  intro n ls e ρb ρ hc hb hr hA
  rw [erwp_opTableN_eq_erwpK β]
  refine erwpK_reborrowDeep (V := fun _ _ => True) (Φ := fun _ => Φ) (Inv := fun _ => True)
    (flI := fun _ => β) (flO := fun _ => β) (Ti := fun _ => liftTabK Tb)
    (To := fun _ => liftTabK Tb) (Q := fun _ => Q) r hch₀ x hx hS hRβ hβc hshape
    (fun _ => hT.toR.liftK) (liftTabK_lin fun m i en h _ => (hT.entry m i en h).2.1)
    (liftTabK_abort fun m i en h => (hT.entry m i en h).1)
    (fun _ _ => rebTwin_lift (OpTabN.twin_refl Tb) β β _ _ _ _) n () trivial ls e ρb ρ hc hb hr
    fun Bχ hBχ => ?_
  have h := hA Bχ hBχ
  rw [erwp_opTableN_eq_erwpK β] at h
  exact h

/-! ### At the typed world -/

/-- **The reborrow at the typed world** (`erwpK_reborrowT` at `KW`). The borrowed entries and the
lender's owe along `KW.Owed` at the same world, at the floor bound of the world; a borrowed stop at
`f` is the lender's at `min f (↓β)`. `RebTwin` is `rebTwin_owed`. -/
theorem erwpK_reborrowT_KW {V : KW → KW → Prop} {Φ : KW → LocFam} (r : FrameRec) (x : LifeVar)
    (hx : ¬ VFree x r.T) {β : Life} {s : LSet} {hs : r.R.InStratum s.join}
    (hS : TmplSpec r (tmpl r)) (hRβ : r.R.InStratum β)
    (hshape : vShape (r.T.immReborrow (.var x)) (r.δ.extend x β) r.v (canon r β))
    (hβs : ∀ y, s.mem y → β ⊑ y) {Ti To : KW → OpTabK KW} (hT : ∀ x, (Ti x).RebOKR β)
    (hab : ∀ x m i en, Ti x m i = some en → en.abort = false)
    (hTw : ∀ x m i en, Ti x m i = some en → ∃ en', To x m i = some en' ∧ en'.q = en.q ∧
      en'.abort = en.abort ∧ en'.PA = en.PA ∧ en'.PB = en.PB ∧ en'.wc = en.wc ∧
      (en.abort = false →
        (∀ f z ρ, x.Owed f z ρ → en.wk f z ρ) ∧ (∀ f z ρ, en'.wk f z ρ → x.Owed f z ρ)))
    (hcan : RebCanK (fun _ => True) Ti To β (ResU.single r.le (CellU.immOf s r.v r.R hs))
      (canon r β) r.R (fun ls => r ∈ rsOf ls))
    {Q : KW → PostN} :
    RKFrame (ℍ := ℍ) V Φ (fun _ => True) β (ResU.single r.le (CellU.immOf s r.v r.R hs))
      (canon r β) (fun ls => r ∈ rsOf ls) (fun y => opTableK y.lo (Ti y))
      (fun y => opTableK y.lo (To y)) (fun y => RebPost β (Q y)) Q :=
  erwpK_reborrowT (flI := fun y => y.lo) (flO := fun y => y.lo) r x hx hS hRβ hshape hβs hT hab
    (fun x _ => rebTwin_owed (canon_reb hS hRβ) (hTw x)) hcan

end BoCa.Fig16.LogRel.Core.Chain.SI

end
