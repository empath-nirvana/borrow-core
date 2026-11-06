import Core.Chain.SI.IFrameK

/-!
# The Mut Anti-Frame across Kripke stops  `[spec §19, §27, §62]`

`docs/new-core/scope-835-iframes.md`. The Mut Anti-Frames (`erwp_M_antiFrame` and its variants) at
`erwpK`, the stop choosing its floor (`SI/ErwpK.lean`). Every variant is one strong induction on
the index with three cases, each the existing one:

* **a return**: 6.66's end, the post read at the world the callback chose;
* **a stop**: the cell sealed in the continuation's share (`rwpG_M_antiFrameGV`); the anti-frame's
  stop chooses its floor and owes its continuation at the worlds `y` its entry allows;
  `OpTabK.SealTwin` gives the callback's entry's order at the callback's share and the frame's
  invariant at `y`, where the cell is opened again by induction on the index; a cancellable stop's
  cancel obligation is the anti-frame's by `hcan`, read at `y`;
* **a raise**: no continuation is owed, so no world is read; the case is the existing one
  (`ASealRaise`).

`erwpK_M_antiFrameGen` is that induction; the variants (`Core/Chain/AFrameK835N.lean`) are its
instances.

**The typed world.** The callback and the anti-frame run at the same world: the seal changes the
share, not the world. `sealTwin_owed` discharges `SealTwin` at `KW` by the share transfer
(`LocTy.ExtP.share`): the callback's share `ℓ ↦ own(w) ● σ′ ● R` has its borrow cells dominated by
the sealed share `R ● ℓ ↦ mut(β, w, σ′)`'s (`seal_cellIn`): `σ′`'s cells lie above `β`, the sealed
cell's lifetime. The frame's invariant is that the cell's key and view are kept, which `KW.Owed`
gives at the sealed share (`kw_owed_seal`).
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

/-! ### The conditions on the tables -/

/-- **The anti-frame's table across the seal, at the floor-choosing stop.** `To` is `Ti`'s twin; at
the shares of the seal (the callback's `ℓ ↦ own(w) ● σ′ ● R`, the anti-frame's
`R ● ℓ ↦ mut(β, w, σ′, F k)`, valid), for every floor `f` a callback's stop may choose, the
anti-frame's stop may choose a floor `f'` with every world its entry allows at `f'` at the sealed
share one the callback's entry allows at `f` at the callback's share, and one where `Inv` holds. -/
def OpTabK.SealTwin (Inv : ι → Prop) (lo lo' : Life) (Ti To : OpTabK ι) (l : Loc) (β : Life)
    (F : Nat → Val → SPropS Loc Val β) : Prop :=
  ∀ m i en, Ti m i = some en → ∃ en', To m i = some en' ∧ en'.q = en.q ∧
    en'.abort = en.abort ∧ en'.PA = en.PA ∧ en'.PB = en.PB ∧ en'.wc = en.wc ∧
    (en.abort = false → ∀ (k : Nat) (w : Val) (σ' : WRes) (h' : σ'.InStratum β)
      (hw' : F k w ⟨σ', h'⟩) (R rest ρk ρk' : WRes),
      ResU.CompS (ResU.single l (CellU.ownOf w)) rest ρk → ResU.CompS σ' R rest →
      ResU.CompS R (ResU.single l (CellU.mutOf β w σ' h' (F k) hw')) ρk' → ResU.Valid ρk' →
      ∀ f, f ≤ lo → ∃ f', f' ≤ lo' ∧ ∀ y, en'.wk f' y ρk' → en.wk f y ρk ∧ Inv y)

/-- **The cancel obligations across the seal**: a cancellable stop's, the callback's at every
opening of the sealed share, is the anti-frame's at the sealed share, at every resumption world
where `Inv` holds (the frame re-enters only there). -/
def ASealCan (Inv : ι → Prop) (Ti To : ι → OpTabK ι) (l : Loc) (β : Life)
    (F : Nat → Val → SPropS Loc Val β) : Prop :=
  ∀ x, Inv x → ∀ m i en en', Ti x m i = some en → To x m i = some en' → en.abort = false →
    en.q ≠ .lin → ∀ y, Inv y → ∀ k ls (K : Kont) (w : Val) (σ : WRes) (h : σ.InStratum β)
      (hw : F k w ⟨σ, h⟩) (R ρk' : WRes),
      ResU.CompS (ResU.single l (CellU.mutOf β w σ h (F k) hw)) R ρk' →
      (∀ W X, ResU.CompS σ (ResU.single l (CellU.ownOf w)) W → ResU.CompS R W X →
        cancelOKK en y k ls K X) →
      cancelOKK en' y k ls K ρk'

theorem asealCan_of_lin {Inv : ι → Prop} {Ti To : ι → OpTabK ι} {l : Loc} {β : Life}
    {F : Nat → Val → SPropS Loc Val β}
    (hlin : ∀ x m i en, Ti x m i = some en → en.abort = false → en.q = .lin) :
    ASealCan Inv Ti To l β F := by
  intro x _ m i en _ hT _ ha hq
  exact absurd (hlin x m i en hT ha) hq

/-- **A raise across the seal**: a raise of the callback at `RI` hands back the cell's content,
and the raise with the cell sealed is a raise of the anti-frame at `RO`. -/
def ASealRaise (l : Loc) (β : Life) (F : Nat → Val → SPropS Loc Val β) (RI RO : TableK ι) :
    Prop :=
  ∀ k ls t (Ψ Ψ' : ContK ι) (ρ' : WRes), RI k ls t Ψ ρ' →
    ∃ (w : Val) (σ : WRes) (h : σ.InStratum β) (hw : F k w ⟨σ, h⟩) (R rest : WRes),
      ResU.CompS (ResU.single l (CellU.ownOf w)) rest ρ' ∧ ResU.CompS σ R rest ∧
      ∀ X, ResU.CompS R (ResU.single l (CellU.mutOf β w σ h (F k) hw)) X → RO k ls t Ψ' X

/-- A table with no raise. -/
theorem asealRaise_none {l : Loc} {β : Life} {F : Nat → Val → SPropS Loc Val β}
    (RO : TableK ι) :
    ASealRaise l β F (fun _ _ _ _ _ => False) RO := fun _ _ _ _ _ _ h => h.elim

/-- **A `raise` carrying the cell's claim, sealed again** (`erwp_M_antiFrameCR`'s case). -/
theorem asealRaise_claim {l : Loc} {β : Life} {F : Nat → Val → SPropS Loc Val β}
    {Ti To : OpTabK ι} (hTw : Ti.Twin To) {Rin Rout : Nat → WProp}
    (hRin : ∀ k ρ, Rin k ρ → claimR l β F k ρ)
    (hRout : ∀ k (w : Val) (σ : WRes) (h : σ.InStratum β) (hw : F k w ⟨σ, h⟩),
      Rout k (ResU.single l (CellU.mutOf β w σ h (F k) hw))) :
    ASealRaise l β F (raiseStopRK Ti Rin) (raiseStopRK To Rout) := by
  intro k ls t Ψ Ψ' ρ' hr
  obtain ⟨K, m, i, v₀, en, hp⟩ := hr
  obtain ⟨⟨rfl, hK, hTe, hab⟩, σ₁, ρR, hcσR, hpa, hR⟩ := pure_sep_iff.mp hp
  obtain ⟨w, σ, hσ, hFk, hclm⟩ := hRin _ _ hR
  obtain ⟨en', hTe', -, hab', hPA', -, -⟩ := hTw m i en hTe
  obtain ⟨rest, hrest, hρ'⟩ := compS_reassoc hclm (ResU.CompS.comm hcσR)
  refine ⟨w, σ, hσ, hFk, σ₁, rest, hρ', hrest, fun X hX => ?_⟩
  exact ⟨K, m, i, v₀, en', pure_sep_mk ⟨rfl, hK, hTe', hab'.trans hab⟩
    ⟨σ₁, _, hX, hPA' ▸ hpa, hRout k w σ hσ hFk⟩⟩

/-- **A cancel's `raise` carrying the cell's claim, sealed again**
(`erwp_M_antiFrame_cancelRunCR`'s case). -/
theorem asealCancel_claim {l : Loc} {β : Life} {F : Nat → Val → SPropS Loc Val β}
    {Ti To : OpTabK ι} (hTw : Ti.Twin To) {Rin Rout : Nat → WProp}
    (hRin : ∀ k ρ, Rin k ρ → claimR l β F k ρ)
    (hRout : ∀ k (w : Val) (σ : WRes) (h : σ.InStratum β) (hw : F k w ⟨σ, h⟩),
      Rout k (ResU.single l (CellU.mutOf β w σ h (F k) hw))) :
    ASealRaise l β F (cancelRaiseRK Ti Rin) (cancelRaiseRK To Rout) := by
  intro k ls t Ψ Ψ' ρ' hr
  obtain ⟨K, err, hp⟩ := hr
  obtain ⟨hpur, y1, y2, hy, ⟨τa, τb, hcab, herr, hnb⟩, hR⟩ := pure_sep_iff.mp hp
  obtain ⟨w, σ, hσ, hFk, hclm⟩ := hRin _ _ hR
  obtain ⟨rest, hrest, hρ'⟩ := compS_reassoc hclm (ResU.CompS.comm hy)
  refine ⟨w, σ, hσ, hFk, y1, rest, hρ', hrest, fun X hX => ?_⟩
  exact ⟨K, err, pure_sep_mk hpur ⟨y1, _, hX,
    ⟨τa, τb, hcab, errOkK_twin hTw herr, hnb⟩, hRout k w σ hσ hFk⟩⟩

/-! ### The anti-frame -/

/-- The callback's share with `σ_B`, re-read: `R ● σ_B ● σ′ ● ℓ ↦ own(w)` is `ρ_k ● σ_B`. -/
theorem seal_back {l : Loc} {w : Val} {σ' R rest ρk : WRes}
    (hk1 : ResU.CompS (ResU.single l (CellU.ownOf w)) rest ρk) (hk2 : ResU.CompS σ' R rest) :
    ∀ (σB ac X₀ W : WRes), ResU.CompS R σB ac →
      ResU.CompS σ' (ResU.single l (CellU.ownOf w)) W → ResU.CompS ac W X₀ →
      ResU.CompS ρk σB X₀ := by
  intro σB ac X₀ W hac hW hX₀
  obtain ⟨t, ht1, ht2⟩ := compS_reassoc hac hX₀
  obtain ⟨ac3, hac3, hW3⟩ := compS_lcomm (ResU.CompS.comm ht1) ht2
  obtain ⟨WR, hWR, hX₀'⟩ := compS_reassoc' hac3 hW3
  obtain ⟨ac2, hac2, hac2W⟩ := compS_exch hW hWR
  obtain rfl : ac2 = rest := ResU.CompS.functional hac2 hk2
  obtain rfl : WR = ρk := ResU.CompS.functional (ResU.CompS.comm hac2W) hk1
  exact hX₀'

/-- **The Mut Anti-Frame across Kripke stops, over any raise tables.** The cell
`ℓ ↦ mut(β, v, ρ_v, F j)`, `Φ ℓ = (β, F)` at every world where `Inv` holds, opened for a callback in
`erwpK` at the guarded table (`Ti`'s stops at the floor bound `flI` guarded by `G`, raises at `RI`):
the computation is in `erwpK`, its stops at `To`'s at the floor bound `flO`, its raises at `RO`.

At a return, 6.66, the post at the world the callback chose. At a stop, the cell sealed in the
continuation's share; `SealTwin` gives the anti-frame's floor, and at every world `y` its entry
allows there the callback's continuation at `y` and `Inv y`; the cell is opened again at `y` at the
index the resume is at. A cancellable stop's cancel obligation is the anti-frame's by `hcan`, read
at `y`. A raise is `hR`. -/
theorem erwpK_M_antiFrameGen {V : ι → ι → Prop} {Φ : ι → LocFam} {Inv : ι → Prop}
    (hΦ : ∀ x, Inv x → (Φ x).Down) {l : Loc} {β : Life} {F : Nat → Val → SPropS Loc Val β}
    (hF : ∀ x, Inv x → Φ x l = some ⟨β, F⟩) {flI flO : ι → Life} {Ti To : ι → OpTabK ι}
    {G : ι → ShareG} {RI RO : ι → TableK ι}
    (hT : ∀ x m i en, Ti x m i = some en → en.abort = false → en.q ≠ .unr ∧ en.wc = extF)
    (hTT : ∀ x, Inv x → (Ti x).SealTwin Inv (flI x) (flO x) (To x) l β F)
    (hG : ∀ x k ls ρ, G x k ls ρ → CellFold l β F k ls ρ)
    (hcan : ASealCan Inv Ti To l β F)
    (hR : ∀ x, Inv x → ASealRaise l β F (RI x) (RO x)) {Q : ι → PostN} :
    ∀ n (x : ι), Inv x → ∀ ls e (v : Val) (σP : WRes) (hstr : σP.InStratum β) (j : Nat)
      (hwit : F j v ⟨σP, hstr⟩) (ρa ρ : WRes),
      ResU.CompS (ResU.single l (CellU.mutOf β v σP hstr (F j) hwit)) ρa ρ →
      (∀ W X, ResU.CompS σP (ResU.single l (CellU.ownOf v)) W → ResU.CompS ρa W X →
        erwpK (ℍ := ℍ) V Φ
          (fun y k ls t Ψ => BoLo.or (performStopGK (flI y) (Ti y) (G y) k ls t Ψ)
            (RI y k ls t Ψ))
          (fun y => AFPost l β F (Q y)) x n ls e X) →
      erwpK (ℍ := ℍ) V Φ
        (fun y k ls t Ψ => BoLo.or (performStopK (flO y) (To y) k ls t Ψ) (RO y k ls t Ψ))
        Q x n ls e ρ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x hx ls e v σP hstr j hwit ρa ρ hsplit hA
  rw [erwpK_eq]
  refine rwpG_M_antiFrameGV (hΦ x hx) (hF x hx) hsplit fun W X hW hX => ?_
  have h := hA W X hW hX
  rw [erwpK_eq] at h
  refine rwpG_mono_le (fun k hk ls' t ρ' ht => ?_) h
  rcases ht with ⟨v', rfl, y₀, hy₀, w, σ', h', hw', R, rest, h1, h2, hQ⟩ | ⟨K, m, i, v₀, en, hp⟩ |
      hr
  · exact ⟨w, σ', h', hw', R, rest, h1, h2, fun X hX _ => Or.inl ⟨v', rfl, y₀, hy₀, hQ X hX⟩⟩
  · -- a stop: seal the cell in the continuation's share
    obtain ⟨⟨rfl, hK, hTe, ha⟩, ρa', ρk, hcak, hPA, hGk, -, f, hf, hcont⟩ := pure_sep_iff.mp hp
    obtain ⟨w, σ', h', hw', R, rest, hk1, hk2⟩ := hG x _ _ _ hGk
    obtain ⟨hqu, hwc⟩ := hT x m i en hTe ha
    obtain ⟨en', hTe', hq', hab', hPA', hPB', hwc', hwk⟩ := hTT x hx m i en hTe
    obtain ⟨y, hy1, hy2⟩ := compS_lcomm hk1 hcak
    obtain ⟨R', hR', hσR'⟩ := compS_lcomm hk2 hy1
    refine ⟨w, σ', h', hw', R', y, hy2, hσR', fun X hX hvX => ?_⟩
    obtain ⟨ρk', hRk, hX'⟩ := compS_reassoc hR' hX
    have hvk' : ResU.Valid ρk' := (ResU.Valid.split hX' hvX).2
    obtain ⟨f', hf', hwk'⟩ := hwk ha k w σ' h' hw' R rest ρk ρk' hk1 hk2 hRk hvk' f hf
    have hwe : ∀ ls'', en'.wc ls' ls'' ρk' → en.wc ls' ls'' ρk := by
      intro ls'' he
      rw [hwc', hwc] at he; rw [hwc]
      exact extF_seal hk1 hk2 hRk (CellU.kind_mutOf _ _ _ _ _ _) (CellU.wit_mutOf _ _ _ _ _ _) he
    refine Or.inr (Or.inl ⟨K, m, i, v₀, en', pure_sep_mk ⟨rfl, hK, hTe', hab'.trans ha⟩
      ⟨ρa', ρk', hX', hPA' ▸ hPA, fun hu' => absurd (hq'.symm.trans hu') hqu, f', hf',
        fun y hy ls'' he => ⟨fun k' hk' w' σB XB hB hXB => ?_, fun hql => ?_⟩⟩⟩)
    · -- the world the anti-frame's continuation is resumed at, read at the callback's share
      obtain ⟨hyi, hyInv⟩ := hwk' y hy
      simp only [erwpCK, show k' < n by omega, if_true]
      obtain ⟨ac, hac, hacX⟩ := compS_exch hRk hXB
      refine ih k' (by omega) y hyInv ls'' _ w σ' h' k hw' ac XB (ResU.CompS.comm hacX)
        fun W X₀ hW hX₀ => ?_
      have hc := (hcont y hyi ls'' (hwe ls'' he)).1 k' (by omega) w' σB X₀ (hPB' ▸ hB)
        (seal_back hk1 hk2 σB ac X₀ W hac hW hX₀)
      simp only [erwpCK, show k' < n by omega, if_true] at hc
      exact hc
    · -- a cancellable stop: the cancel obligation is the anti-frame's, at the resumption world
      obtain ⟨hyi, hyInv⟩ := hwk' y hy
      have hql' : en.q ≠ .lin := hq' ▸ hql
      refine hcan x hx m i en en' hTe hTe' ha hql' y hyInv k ls'' K w σ' h' hw' R ρk'
        (ResU.CompS.comm hRk) fun W X₀ hW hX₀ => ?_
      obtain rfl : X₀ = ρk := by
        have h0 := seal_back hk1 hk2 PMap.empty R X₀ W (ResU.comp_empty_right R) hW hX₀
        exact ResU.CompS.functional h0 (ResU.comp_empty_right ρk)
      exact (hcont y hyi ls'' (hwe ls'' he)).2 hql'
  · -- a raise: no continuation is owed
    obtain ⟨w, σ, hσ, hFk, R, rest, h1, h2, hRO⟩ := hR x hx k ls' t _ (erwpCK (ℍ := ℍ) V Φ
      (fun y k ls t Ψ => BoLo.or (performStopK (flO y) (To y) k ls t Ψ) (RO y k ls t Ψ)) Q n) ρ' hr
    exact ⟨w, σ, hσ, hFk, R, rest, h1, h2, fun X hX _ => Or.inr (Or.inr (hRO X hX))⟩

/-! ### The constant world -/

/-- **`SealTwin` at one world**: a twin of the lifted table, every world allowed. -/
theorem sealTwin_lift {T T' : OpTabN} (hTw : T.Twin T') (lo : Life) (l : Loc) (β : Life)
    (F : Nat → Val → SPropS Loc Val β) :
    (liftTabK T).SealTwin (fun _ => True) lo lo (liftTabK T') l β F := by
  intro m i en hT
  obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some hT
  obtain ⟨en₀', h₀', hq, ha, hPA, hPB, hwc⟩ := hTw m i en₀ h₀
  refine ⟨liftEntK en₀', liftTabK_of_some h₀', hq, ha, hPA, ?_, hwc,
    fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ f hf => ⟨f, hf, fun _ _ => ⟨trivial, trivial⟩⟩⟩
  show (fun _ => en₀'.PB) = fun _ => en₀.PB
  rw [hPB]

/-- `erwp_M_antiFrameCR`'s `hcan` at one world. -/
theorem asealCan_lift {T T' : OpTabN} {l : Loc} {β : Life} {F : Nat → Val → SPropS Loc Val β}
    (hcan : ∀ m i en en', T m i = some en → T' m i = some en' → en.abort = false →
      en.q ≠ .lin → ∀ k ls (K : Kont) (w : Val) (σ : WRes) (h : σ.InStratum β)
        (hw : F k w ⟨σ, h⟩) (R ρk' : WRes),
        ResU.CompS (ResU.single l (CellU.mutOf β w σ h (F k) hw)) R ρk' →
        (∀ W X, ResU.CompS σ (ResU.single l (CellU.ownOf w)) W → ResU.CompS R W X →
          cancelOKN en k ls K X) →
        cancelOKN en' k ls K ρk') :
    ASealCan (fun _ : Unit => True) (fun _ => liftTabK T) (fun _ => liftTabK T') l β F := by
  intro _ _ m i en en' hT hT' ha hq _ _ k ls K w σ h hw R ρk' hRk hX
  obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some hT
  obtain ⟨en₀', h₀', rfl⟩ := liftTabK_some hT'
  exact (cancelOKK_liftEntK en₀' k ls K ρk').mpr (hcan m i en₀ en₀' h₀ h₀' ha hq k ls K w σ h hw
    R ρk' hRk fun W X hW hX' => (cancelOKK_liftEntK en₀ k ls K X).mp (hX W X hW hX'))

/-! ### The typed world -/

/-- A borrow cell of a composite is a borrow cell of one of its parts, no longer-lived. -/
theorem CellIn.split {ρ₁ ρ₂ ρ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ) {b : Life} (h : CellIn ρ b) :
    CellIn ρ₁ b ∨ CellIn ρ₂ b := by
  obtain ⟨m, ψ, e, k, hb⟩ := h
  rcases ResU.Comp.get hc m with ⟨-, -, f⟩ | ⟨χ, f₁, -, f⟩ | ⟨χ, -, f₂, f⟩ |
      ⟨χ₁, χ₂, χ, f₁, f₂, f, hC⟩
  · rw [e] at f; cases f
  · rw [e] at f; cases Option.some.inj f; exact Or.inl ⟨m, _, f₁, k, hb⟩
  · rw [e] at f; cases Option.some.inj f; exact Or.inr ⟨m, _, f₂, k, hb⟩
  · rw [e] at f; cases Option.some.inj f
    have hk := CellU.CompatS.kinds (hc.1 m χ₁ χ₂ f₁ f₂)
    rw [CellU.CompS.at hC] at hb
    rcases min_le_iff.mp hb with hb | hb
    · exact Or.inl ⟨m, χ₁, f₁, by rw [hk.1]; decide, hb⟩
    · exact Or.inr ⟨m, χ₂, f₂, by rw [hk.2]; decide, hb⟩

/-- **The callback's share is dominated by the sealed share**: a borrow cell of
`ℓ ↦ own(w) ● σ′ ● R` is one of `R`, or one of `σ′`, which lies above `β`, the sealed cell's
lifetime. -/
theorem seal_cellIn {l : Loc} {β : Life} {F : Nat → Val → SPropS Loc Val β} {k : Nat} {w : Val}
    {σ' : WRes} {h' : σ'.InStratum β} {hw' : F k w ⟨σ', h'⟩} {R rest ρk ρk' : WRes}
    (hk1 : ResU.CompS (ResU.single l (CellU.ownOf w)) rest ρk) (hk2 : ResU.CompS σ' R rest)
    (hRk : ResU.CompS R (ResU.single l (CellU.mutOf β w σ' h' (F k) hw')) ρk') :
    ∀ a, CellIn ρk a → CellIn ρk' a := by
  intro a ha
  rcases CellIn.split hk1 ha with ⟨m, ψ, e, hk, -⟩ | ha
  · obtain ⟨-, rfl⟩ := ResU.single_get_eq_some e
    exact absurd rfl hk
  rcases CellIn.split hk2 ha with ha | ha
  · have hβa : β < a := ha.of_stratum h'
    obtain ⟨m, ψ, e, hk, hle⟩ := CellIn.of_right hRk (CellIn.single
      (ψ := CellU.mutOf β w σ' h' (F k) hw') (by rw [CellU.kind_mutOf]; exact fun c => Kind.noConfusion c))
    exact ⟨m, ψ, e, hk, le_trans hle (le_of_lt hβa)⟩
  · exact CellIn.of_left hRk ha

/-- **The view is consistent with the callback's share** when it is with the sealed share, valid. -/
theorem consistentX_seal {c : Loc → Option Life} {l : Loc} {β : Life}
    {F : Nat → Val → SPropS Loc Val β} {k : Nat} {w : Val} {σ' : WRes} {h' : σ'.InStratum β}
    {hw' : F k w ⟨σ', h'⟩} {R rest ρk ρk' : WRes}
    (hk1 : ResU.CompS (ResU.single l (CellU.ownOf w)) rest ρk) (hk2 : ResU.CompS σ' R rest)
    (hRk : ResU.CompS R (ResU.single l (CellU.mutOf β w σ' h' (F k) hw')) ρk')
    (hv : ResU.Valid ρk') (hc : ConsistentX c ρk') : ConsistentX c ρk := by
  have hvm := (ResU.Valid.split hRk hv).2
  have hcσ := consistentX_mut_wit (consistentX_right hRk hc hv) hvm
  exact consistentX_compS hk1 (consistentX_of_top (ResU.inStratum_single_own _ l w) c)
    (consistentX_compS hk2 hcσ (consistentX_left hRk hc hv))

/-- The cell's entry in the view. -/
theorem LocTy.view_of_key {Θ : LocTy} {c : Loc → Option Life} {l : Loc} {β : Life}
    {F : Nat → Val → SPropS Loc Val β} (hc : c l = some β) (hΘ : Θ l β = some F) :
    Θ.view c l = some ⟨β, F⟩ := by
  rw [LocTy.view_apply, hc]
  simp only [hΘ]
  rfl

/-- **The typed seal across a Kripke stop.** The anti-frame's stop at `x`, at the floor `f`, owes
its continuation at `y` (`KW.Owed`) at the sealed share. Then `y` is owed at the callback's share,
and, where `x` holds the cell's key, `y` holds it and its view is at the cell's lifetime. -/
theorem kw_owed_seal {x y : KW} {f : Life} {l : Loc} {β : Life}
    {F : Nat → Val → SPropS Loc Val β} {k : Nat} {w : Val} {σ' : WRes} {h' : σ'.InStratum β}
    {hw' : F k w ⟨σ', h'⟩} {R rest ρk ρk' : WRes}
    (hk1 : ResU.CompS (ResU.single l (CellU.ownOf w)) rest ρk) (hk2 : ResU.CompS σ' R rest)
    (hRk : ResU.CompS R (ResU.single l (CellU.mutOf β w σ' h' (F k) hw')) ρk')
    (hv : ResU.Valid ρk') (hy : x.Owed f y ρk') :
    x.Owed f y ρk ∧ (x.Θ l β = some F → y.Θ l β = some F ∧ y.c l = some β) := by
  have hkm : (CellU.mutOf β w σ' h' (F k) hw').kind ≠ Kind.imm := by
    rw [CellU.kind_mutOf]; exact fun c => Kind.noConfusion c
  have hl : ρk'.get l = some (CellU.mutOf β w σ' h' (F k) hw') :=
    (ResU.CompS.get_left_of_ne_imm (ResU.CompS.comm hRk) (ResU.single_get_self _ _) hkm).2
  refine ⟨⟨hy.1.share fun a _ ha => seal_cellIn hk1 hk2 hRk a ha, hy.2.1,
    consistentX_seal hk1 hk2 hRk hv hy.2.2.1, hy.2.2.2⟩, fun hx => ⟨?_, ?_⟩⟩
  · refine (hy.1.1.1 l β F hx ?_).1
    exact CellIn.of_right hRk (CellIn.single (ψ := CellU.mutOf β w σ' h' (F k) hw')
      (by rw [CellU.kind_mutOf]; exact fun c => Kind.noConfusion c))
  · exact consistentX_get hy.2.2.1 hv hl (CellU.kind_mutOf _ _ _ _ _ _)

/-- **The anti-frame's invariant at the typed world**: a valid location typing, the cell's key and
the view at the cell's lifetime. -/
def KW.SealInv (l : Loc) (β : Life) (F : Nat → Val → SPropS Loc Val β) (y : KW) : Prop :=
  y.Θ.OK ∧ y.Θ l β = some F ∧ y.c l = some β

/-- **`SealTwin` at the typed world.** The callback's entries and the anti-frame's owe along
`KW.Owed` at the same world `x`; the anti-frame's stop takes the callback's floor; the frame's
invariant is `KW.SealInv`. -/
theorem sealTwin_owed {x : KW} {l : Loc} {β : Life} {F : Nat → Val → SPropS Loc Val β}
    (hx : x.Θ l β = some F) {lo : Life} {Ti To : OpTabK KW}
    (hTw : ∀ m i en, Ti m i = some en → ∃ en', To m i = some en' ∧ en'.q = en.q ∧
      en'.abort = en.abort ∧ en'.PA = en.PA ∧ en'.PB = en.PB ∧ en'.wc = en.wc ∧
      (en.abort = false →
        (∀ f z ρ, x.Owed f z ρ → en.wk f z ρ) ∧ (∀ f z ρ, en'.wk f z ρ → x.Owed f z ρ))) :
    Ti.SealTwin (KW.SealInv l β F) lo lo To l β F := by
  intro m i en hTe
  obtain ⟨en', hTe', h₁, h₂, h₃, h₄, h₅, hwk⟩ := hTw m i en hTe
  refine ⟨en', hTe', h₁, h₂, h₃, h₄, h₅, fun ha k w σ' h' hw' R rest ρk ρk' hk1 hk2 hRk hv f hf =>
    ⟨f, hf, fun y hy => ?_⟩⟩
  obtain ⟨hin, hout⟩ := hwk ha
  obtain ⟨h, hyI⟩ := kw_owed_seal hk1 hk2 hRk hv (hout _ _ _ hy)
  exact ⟨hin _ _ _ h, (hout _ _ _ hy).2.1, hyI hx⟩

/-- The anti-frame's invariant gives the cell's entry at the world's view. -/
theorem kw_seal_view {l : Loc} {β : Life} {F : Nat → Val → SPropS Loc Val β} (x : KW)
    (hx : KW.SealInv l β F x) : x.Θ.view x.c l = some ⟨β, F⟩ :=
  LocTy.view_of_key hx.2.2 hx.2.1

end BoCa.Fig16.LogRel.Core.Chain.SI

end
