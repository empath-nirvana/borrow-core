import Core.Chain.SI.AFrameK
import Core.Chain.SI.RebRaiseC

/-!
# The reborrow frame across Kripke stops  `[spec §19, §27, §62]`

`docs/new-core/scope-835-iframes.md`. `[TR]` 6.150 across stops (`erwp_rebGen`,
`erwp_rebGen_cancelRun` and the frames they generalise) at `erwpK`, the stop choosing its floor
(`SI/ErwpK.lean`). One strong induction on the index with three cases, each the existing one:

* **a return**: 6.150's exit, the post read at the world the borrowed run chose;
* **a stop**: the reborrow folded into the continuation's share `ψ ● ρᵢ`; the lender's stop
  chooses its floor and owes its continuation at the worlds `y` its entry allows;
  `OpTabK.RebTwin` gives the borrowed entry's order at the borrowed share and the frame's
  invariant at `y`, where the frame is re-entered at the image by induction on the index; a
  cancellable stop's cancel obligation is the lender's by `hcan`, read at `y`;
* **a raise**: no continuation is owed, so no world is read (`RebRaiseFold`).

**The entry.** `RebEntryGP` is `RebEntryG` with a fact `Pv` about the run's final resource and
the lender's post resource handed to `hpost`: `True` (`RebEntryG.toP`) or their validity
(`rebEntryGV_top`, `rebEntryGV_deep`, from `rwpG_rebGV` and `rwpG_rebDeepGV`).

**The typed world.** The borrowed run and the lender run at the same world: the reborrow changes
the share, not the location typing. `rebTwin_owed` discharges `RebTwin` at `KW` by the share
transfer (`LocTy.ExtP.share`): a borrow cell of the borrowed share shorter-lived than `β` is the
lender's (`reb_cellIn`), since every cell of the image is at `β` or longer-lived (`reb_at_ge`). The
lender's stop chooses a floor below `β`.
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

/-! ### The entry -/

/-- **`RebEntryG` with a fact `Pv` about the run's final resource `w` and the lender's post `Y`
handed to `hpost`.** -/
def RebEntryGP (Φ : LocFam) (β : Life) (ρi χ R : WRes) (Ok : List SRec → Prop)
    (Pv : WRes → WRes → Prop) : Prop :=
  ∀ (Qin Qout : PostG) (n : Nat) (ls : List SRec) (e : Expr) (ρb ρ : WRes),
    ResU.CompS ρi ρb ρ → ρb.InStratum β → Ok ls →
    (∀ k, k ≤ n → ∀ ls'' t (ρ' : WRes), Qin k ls'' t ρ' → (∀ y, y ∈ ls'' ↔ y ∈ ls) →
      ∃ ρo ρk, ResU.CompS ρo ρk ρ' ∧ ρo.InStratum β ∧
        ∀ (ρp w ψ Yo Y : WRes), NoOwn ρp → ResU.CompS ρk ρp w →
          ResU.SubKeep w (χ.restrictDom R.exclPart) ψ →
          ResU.CompS ψ (χ.restrictDom R.exclPart) w → ψ.InStratum β →
          ResU.CompS ρo ψ Yo → ResU.CompS Yo ρi Y → Pv w Y →
          ∃ ρ'L ρpL, ResU.CompS ρ'L ρpL Y ∧ NoOwn ρpL ∧ Qout k ls'' t ρ'L) →
    (∀ Bχ, ResU.CompS ρb χ Bχ → rwpG (ℍ := ℍ) Φ Qin n ls e Bχ) →
    rwpG (ℍ := ℍ) Φ Qout n ls e ρ

/-- `RebEntryG` hands `hpost` nothing more. -/
theorem RebEntryG.toP {Φ : LocFam} {β : Life} {ρi χ R : WRes} {Ok : List SRec → Prop}
    (h : RebEntryG (ℍ := ℍ) Φ β ρi χ R Ok) : RebEntryGP (ℍ := ℍ) Φ β ρi χ R Ok fun _ _ => True :=
  fun Qin Qout n ls e ρb ρ hc hb hr hpost hA => h Qin Qout n ls e ρb ρ hc hb hr
    (fun k hk ls'' t ρ' hQ hls => by
      obtain ⟨ρo, ρk, h1, h2, h3⟩ := hpost k hk ls'' t ρ' hQ hls
      exact ⟨ρo, ρk, h1, h2, fun ρp w ψ Yo Y a b c d e f g => h3 ρp w ψ Yo Y a b c d e f g trivial⟩)
    hA

/-- The resources' validity: `rwpG_rebGV` at the record's cell. -/
theorem rebEntryGV_top {Φ : LocFam} (r : FrameRec) (x : LifeVar) (hx : ¬ VFree x r.T)
    {β : Life} {s : LSet} {hs : r.R.InStratum s.join} (hS : TmplSpec r (tmpl r))
    (hRβ : r.R.InStratum β)
    (hshape : vShape (r.T.immReborrow (.var x)) (r.δ.extend x β) r.v (canon r β))
    (hβs : ∀ y, s.mem y → β ⊑ y) :
    RebEntryGP (ℍ := ℍ) Φ β (ResU.single r.le (CellU.immOf s r.v r.R hs)) (canon r β) r.R
      (fun ls => r ∈ rsOf ls) (fun w Y => ResU.Valid w ∧ ResU.Valid Y) :=
  fun _ _ _ _ _ _ _ hc hb hr hpost hA => rwpG_rebGV r x hx hS hRβ hshape hc hb hr hβs
    (fun k hk ls'' t ρ' hQ hls => by
      obtain ⟨ρo, ρk, h1, h2, h3⟩ := hpost k hk ls'' t ρ' hQ hls
      exact ⟨ρo, ρk, h1, h2, fun ρp w ψ Yo Y a b c d e f g hw hY =>
        h3 ρp w ψ Yo Y a b c d e f g ⟨hw, hY⟩⟩) hA

/-- The resources' validity: `rwpG_rebDeepGV` at a chain view. -/
theorem rebEntryGV_deep {Φ : LocFam} (r : FrameRec) {p₀ : Option Loc} {l₀ : Loc} {S₀ : VTy}
    {u₀ : Val} (hch₀ : Chain r.R r.T r.v p₀ l₀ S₀ u₀) {w₀ : WRes} (x : LifeVar)
    (hx : ¬ VFree x S₀) {β : Life} {s : LSet} {hs : w₀.InStratum s.join}
    (hS : TmplSpecD r S₀ u₀ w₀ (tmplD r S₀ u₀ w₀)) (hRβ : w₀.InStratum β)
    (hβc : (CellU.immOf s u₀ w₀ hs).InStratum β)
    (hshape : vShape (S₀.immReborrow (.var x)) (r.δ.extend x β) u₀ (canonD r S₀ u₀ w₀ β)) :
    RebEntryGP (ℍ := ℍ) Φ β (ResU.single l₀ (CellU.immOf s u₀ w₀ hs)) (canonD r S₀ u₀ w₀ β) w₀
      (fun ls => r ∈ rsOf ls) (fun w Y => ResU.Valid w ∧ ResU.Valid Y) :=
  fun _ _ _ _ _ _ _ hc hb hr hpost hA => rwpG_rebDeepGV r hch₀ x hx hS hRβ hβc hshape hc hb hr
    (fun k hk ls'' t ρ' hQ hls => by
      obtain ⟨ρo, ρk, h1, h2, h3⟩ := hpost k hk ls'' t ρ' hQ hls
      exact ⟨ρo, ρk, h1, h2, fun ρp w ψ Yo Y a b c d e f g hw hY =>
        h3 ρp w ψ Yo Y a b c d e f g ⟨hw, hY⟩⟩) hA

/-! ### The conditions on the tables -/

/-- `OpTabN.RebOKR` over a world index. -/
structure OpTabK.RebOKR (T : OpTabK ι) (β : Life) : Prop where
  entry : ∀ m i en, T m i = some en → en.abort = false → en.q ≠ .unr ∧ en.wc = extF
  pa : ∀ m i en, T m i = some en → ∀ k ls v (ρ : WRes), en.PA k ls v ρ → ρ.InStratum β
  pb : ∀ m i en, T m i = some en → ∀ y k ls w (ρ : WRes), en.PB y k ls w ρ → ρ.InStratum β

/-- **The lender's table across the reborrow's fold, at the floor-choosing stop.** `To` is `Ti`'s
twin; at the shares of the fold (the borrowed `ρ_k`, `ρ_k ● ρ_p = w = ψ ● χ|excl`, the lender's
`Ks = ψ ● ρᵢ`, with `Pv` of `w` and of a post `Y ⊇ Ks`), for every floor `f` a borrowed stop may
choose, the lender's stop may choose a floor `f'` with every world its entry allows at `f'` at `Ks`
one the borrowed entry allows at `f` at `ρ_k`, and one where `Inv` holds. -/
def OpTabK.RebTwin (Inv : ι → Prop) (lo lo' : Life) (Ti To : OpTabK ι) (β : Life)
    (ρi χ R : WRes) (Pv : WRes → WRes → Prop) : Prop :=
  ∀ m i en, Ti m i = some en → ∃ en', To m i = some en' ∧ en'.q = en.q ∧
    en'.abort = en.abort ∧ en'.PA = en.PA ∧ en'.PB = en.PB ∧ en'.wc = en.wc ∧
    (en.abort = false → ∀ (ρk ρp w ψ Ks : WRes), ResU.CompS ρk ρp w →
      ResU.CompS ψ (χ.restrictDom R.exclPart) w → ψ.InStratum β → ResU.CompS ψ ρi Ks →
      (∃ ρo Y, ResU.CompS ρo Ks Y ∧ Pv w Y) →
      ∀ f, f ≤ lo → ∃ f', f' ≤ lo' ∧ ∀ y, en'.wk f' y Ks → en.wk f y ρk ∧ Inv y)

theorem OpTabK.RebTwin.twin {Inv : ι → Prop} {lo lo' : Life} {Ti To : OpTabK ι} {β : Life}
    {ρi χ R : WRes} {Pv : WRes → WRes → Prop} (h : Ti.RebTwin Inv lo lo' To β ρi χ R Pv) :
    Ti.Twin To := by
  intro m i en hTe
  obtain ⟨en', h₁, h₂, h₃, h₄, h₅, h₆, -⟩ := h m i en hTe
  exact ⟨en', h₁, h₂, h₃, h₄, h₅, h₆⟩

/-- **The reborrow frame builds no stop outside `Sched`**: when the borrowed table's resuming
entries are at names in `Sched` (the restriction's (S1)), `RebTwin` holds of the part of the
lender's table at those names and its raises (`OpTabK.schedPart`). -/
theorem OpTabK.RebTwin.schedPart {Inv : ι → Prop} {lo lo' : Life} {Ti To : OpTabK ι} {β : Life}
    {ρi χ R : WRes} {Pv : WRes → WRes → Prop} (h : Ti.RebTwin Inv lo lo' To β ρi χ R Pv)
    {Sched : UInt32 → Prop} (hS : ∀ m i en, Ti m i = some en → en.abort = false → Sched m) :
    Ti.RebTwin Inv lo lo' (To.schedPart Sched) β ρi χ R Pv := by
  classical
  intro m i en hTe
  obtain ⟨en', hTe', h₁, h₂, h₃, h₄, h₅, h₆⟩ := h m i en hTe
  refine ⟨en', ?_, h₁, h₂, h₃, h₄, h₅, h₆⟩
  unfold OpTabK.schedPart
  rw [hTe']
  simp only
  rw [if_neg]
  rintro ⟨ha, hn⟩
  exact hn (hS m i en hTe (h₂ ▸ ha))

/-- **The cancel obligations across the reborrow's fold**: a cancellable stop's, the borrowed
run's at `ρ_k`, is the lender's at `ψ ● ρᵢ`, at every resumption world. -/
def RebCanK (Inv : ι → Prop) (Ti To : ι → OpTabK ι) (β : Life) (ρi χ R : WRes)
    (Ok : List SRec → Prop) : Prop :=
  ∀ x, Inv x → ∀ m i en en', Ti x m i = some en → To x m i = some en' → en.abort = false →
    en.q ≠ .lin → ∀ y k ls (K : Kont) (ρk ρp w ψ Ks : WRes), NoOwn ρp → ResU.CompS ρk ρp w →
      ResU.CompS ψ (χ.restrictDom R.exclPart) w → ψ.InStratum β → ResU.CompS ψ ρi Ks → Ok ls →
      cancelOKK en y k ls K ρk → cancelOKK en' y k ls K Ks

theorem rebCanK_of_lin {Inv : ι → Prop} {Ti To : ι → OpTabK ι} {β : Life} {ρi χ R : WRes}
    {Ok : List SRec → Prop}
    (hlin : ∀ x m i en, Ti x m i = some en → en.abort = false → en.q = .lin) :
    RebCanK Inv Ti To β ρi χ R Ok := by
  intro x _ m i en _ hT _ ha hq
  exact absurd (hlin x m i en hT ha) hq

/-- **A raise across the reborrow**: a raise of the borrowed run at `RI` is a raise of the lender
at `RO`, everything but the payload owning nothing. -/
def RebRaiseFold (β : Life) (ρi χ R : WRes) (RI RO : TableK ι) : Prop :=
  ∀ k ls t (Ψ Ψ' : ContK ι) (ρ' : WRes), RI k ls t Ψ ρ' →
    ∃ ρo ρk, ResU.CompS ρo ρk ρ' ∧ ρo.InStratum β ∧
      ∀ (ρp w ψ Yo Y : WRes), NoOwn ρp → ResU.CompS ρk ρp w →
        ResU.SubKeep w (χ.restrictDom R.exclPart) ψ →
        ResU.CompS ψ (χ.restrictDom R.exclPart) w → ψ.InStratum β →
        ResU.CompS ρo ψ Yo → ResU.CompS Yo ρi Y →
        ∃ ρ'L ρpL, ResU.CompS ρ'L ρpL Y ∧ NoOwn ρpL ∧ RO k ls t Ψ' ρ'L

theorem rebRaise_absurd {β : Life} {ρi χ R : WRes} {T : OpTabK ι}
    (hab : ∀ m i en, T m i = some en → en.abort = false) (RO : TableK ι) :
    RebRaiseFold β ρi χ R (raiseStopK T) RO := by
  intro k ls t Ψ Ψ' ρ' hr
  obtain ⟨K, m, i, v₀, en, hp⟩ := hr
  obtain ⟨⟨-, -, hTe, ha⟩, -⟩ := pure_sep_iff.mp hp
  exact absurd ha (by rw [hab m i en hTe]; simp)

/-- **A `raise`: the lender raises with the same payload** (`erwp_rebGen`'s case). -/
theorem rebRaise_same {β : Life} {le : Loc} {s : LSet} {v : Val} {R : WRes}
    {hs : R.InStratum s.join} {χ : WRes} {Ti To : OpTabK ι} (hTw : Ti.Twin To)
    (hpa : ∀ m i en, Ti m i = some en → ∀ k ls v (ρ : WRes), en.PA k ls v ρ → ρ.InStratum β) :
    RebRaiseFold β (ResU.single le (CellU.immOf s v R hs)) χ R (raiseStopK Ti) (raiseStopK To) := by
  intro k ls t Ψ Ψ' ρ' hr
  obtain ⟨K, m, i, v₀, en, hp⟩ := hr
  obtain ⟨⟨rfl, hK, hTe, ha⟩, ρa, ρn, hcan', ⟨hPA, hnA⟩, hnn⟩ := pure_sep_iff.mp hp
  obtain ⟨en', hTe', -, hab', hPA', -, -⟩ := hTw m i en hTe
  refine ⟨ρa, ρn, hcan', hpa m i en hTe _ _ _ _ hPA, ?_⟩
  intro ρp w' ψ Yo Y hnp hkw hsubK hsplit hψβ hYo hY
  obtain ⟨Ks, hKs, haKs⟩ := compS_reassoc hYo hY
  have hnKs : NoOwn Ks := noOwn_compS hKs (noOwn_subKeep hsubK (noOwn_compS hkw hnn hnp))
    (noOwn_single_imm _ _ _ _ _)
  exact ⟨Y, PMap.empty, ResU.comp_empty_right _, noOwn_empty,
    ⟨K, m, i, v₀, en', pure_sep_mk ⟨rfl, hK, hTe', hab'.trans ha⟩
      ⟨ρa, Ks, haKs, ⟨hPA' ▸ hPA, hnA⟩, hnKs⟩⟩⟩

/-- **A cancel's `raise`: the error payload kept, everything else owning nothing**
(`erwp_rebGen_cancelRun`'s case). -/
theorem rebCancel_same {β : Life} {le : Loc} {s : LSet} {v : Val} {R : WRes}
    {hs : R.InStratum s.join} {χ : WRes} {Ti To : OpTabK ι} (hTw : Ti.Twin To)
    (hpa : ∀ m i en, Ti m i = some en → ∀ k ls v (ρ : WRes), en.PA k ls v ρ → ρ.InStratum β) :
    RebRaiseFold β (ResU.single le (CellU.immOf s v R hs)) χ R (cancelRaiseK Ti)
      (cancelRaiseK To) := by
  intro k ls t Ψ Ψ' ρ' hr
  obtain ⟨K, err, hp⟩ := hr
  obtain ⟨⟨rfl, hK⟩, τa, τb, hcab, herr, hnb⟩ := pure_sep_iff.mp hp
  have hτaβ : τa.InStratum β := by
    cases err with
    | none => obtain rfl : τa = PMap.empty := herr.1; exact ResU.inStratum_empty β
    | some E =>
        obtain ⟨m, j', w', en, he⟩ := herr
        obtain ⟨⟨-, hTe, -⟩, hPA, -⟩ := pure_sep_iff.mp he
        exact hpa _ _ en hTe _ _ _ _ hPA
  refine ⟨τa, τb, hcab, hτaβ, ?_⟩
  intro ρp w' ψ Yo Y hnp hkw hsubK hsplit hψβ hYo hY
  obtain ⟨Ks, hKs, haKs⟩ := compS_reassoc hYo hY
  have hnKs : NoOwn Ks := noOwn_compS hKs (noOwn_subKeep hsubK (noOwn_compS hkw hnb hnp))
    (noOwn_single_imm _ _ _ _ _)
  exact ⟨Y, PMap.empty, ResU.comp_empty_right _, noOwn_empty,
    ⟨K, err, pure_sep_mk ⟨rfl, hK⟩ ⟨τa, Ks, haKs, errOkK_twin hTw herr, hnKs⟩⟩⟩

/-! ### The frame -/

/-- **`[TR]` 6.150 across Kripke stops, over any raise tables.** The lender holds the cell
`ρᵢ = ℓ ↦ imm(s, v, R)` and `ρ_b ∈ Res_β`; the borrowed computation, handed `ρ_b ● χ`, is in
`erwpK` with postcondition `[β]Q̂` and may stop at the borrowed table (`Ti`'s stops at the floor
bound `flI`, raises at `RI`) with the reborrow live: the computation is in `erwpK`, its stops at
`To`'s at the floor bound `flO`, its raises at `RO`.

At a return, 6.150's exit, the post at the world the borrowed run chose. At a stop, the reborrow
folded into `ψ ● ρᵢ`; `RebTwin` gives the lender's floor, and at every world `y` the lender's entry
allows there the borrowed continuation at `y` and `Inv y`; the frame is re-entered at the image at
`y`, at the index the resume is at. A cancellable stop's cancel obligation is the lender's by
`hcan`, read at `y`. A raise is `hR`. -/
theorem erwpK_rebGenK {V : ι → ι → Prop} {Φ : ι → LocFam} {Inv : ι → Prop} {β : Life}
    {le : Loc} {s : LSet} {v : Val} {R : WRes} {hs : R.InStratum s.join} {χ : WRes}
    {Ok : List SRec → Prop} {Pv : WRes → WRes → Prop}
    (hE : ∀ x, Inv x →
      RebEntryGP (ℍ := ℍ) (Φ x) β (ResU.single le (CellU.immOf s v R hs)) χ R Ok Pv)
    (hreb : ResU.Reb β R χ)
    (hOk : ∀ (ls ls'' lsO : List SRec) (ψ Ks : WRes), Ok ls → (∀ y, y ∈ ls'' ↔ y ∈ ls) →
      ResU.CompS ψ (ResU.single le (CellU.immOf s v R hs)) Ks → extF ls'' lsO Ks → Ok lsO)
    {flI flO : ι → Life} {Ti To : ι → OpTabK ι} {RI RO : ι → TableK ι}
    (hT : ∀ x, (Ti x).RebOKR β)
    (hTT : ∀ x, Inv x → (Ti x).RebTwin Inv (flI x) (flO x) (To x) β
      (ResU.single le (CellU.immOf s v R hs)) χ R Pv)
    (hcan : RebCanK Inv Ti To β (ResU.single le (CellU.immOf s v R hs)) χ R Ok)
    (hR : ∀ x, Inv x → RebRaiseFold β (ResU.single le (CellU.immOf s v R hs)) χ R (RI x) (RO x))
    {Q : ι → PostN} :
    ∀ n (x : ι), Inv x → ∀ ls e (ρb ρ : WRes),
      ResU.CompS (ResU.single le (CellU.immOf s v R hs)) ρb ρ → ρb.InStratum β → Ok ls →
      (∀ Bχ, ResU.CompS ρb χ Bχ →
        erwpK (ℍ := ℍ) V Φ
          (fun y k ls t Ψ => BoLo.or (performStopK (flI y) (Ti y) k ls t Ψ) (RI y k ls t Ψ))
          (fun y => RebPost β (Q y)) x n ls e Bχ) →
      erwpK (ℍ := ℍ) V Φ
        (fun y k ls t Ψ => BoLo.or (performStopK (flO y) (To y) k ls t Ψ) (RO y k ls t Ψ))
        Q x n ls e ρ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x hx ls e ρb ρ hc hb hr hA
  have hχsplit := ResU.restrictDom_split hreb
  have hχimm : NoOwn (χ.restrictDom (R.restrict Kind.imm)) :=
    noOwn_of_imm fun m ψ e => ResU.reb_imm_image hreb (ResU.restrictDom_get_inv e)
  rw [erwpK_eq]
  refine hE x hx _ _ n ls e ρb ρ hc hb hr ?_ (fun Bχ hBχ => by
    have h := hA Bχ hBχ
    rw [erwpK_eq] at h
    exact h)
  intro k hk ls'' t ρ' hQin hls''
  rcases hQin with ⟨w, rfl, y₀, hy₀, hQ, hρ'β⟩ | ⟨K, m, i, v₀, en, hp⟩ | hr'
  · -- a return: 6.150's exit, the post at the world the borrowed run chose
    refine ⟨ρ', PMap.empty, ResU.comp_empty_right _, hρ'β, ?_⟩
    intro ρp w' ψ Yo Y hnp hkw hsubK hsplit hψβ hYo hY _
    obtain rfl : w' = ρp := ResU.CompS.functional hkw (ResU.comp_empty_left _)
    obtain ⟨g, hg, hρ'g⟩ := compS_reassoc hYo hY
    exact ⟨ρ', g, hρ'g, noOwn_compS hg (noOwn_subKeep hsubK hnp) (noOwn_single_imm _ _ _ _ _),
      Or.inl ⟨w, rfl, y₀, hy₀, hQ⟩⟩
  · -- a stop: the fold, owed at every world the lender allows
    obtain ⟨⟨rfl, hK, hTe, ha⟩, ρa, ρk, hcak, hPA, -, f, hf, hcont⟩ := pure_sep_iff.mp hp
    obtain ⟨hq, hwc⟩ := (hT x).entry m i en hTe ha
    obtain ⟨en', hTe', hq', hab', hPA', hPB', hwc', hwk⟩ := hTT x hx m i en hTe
    refine ⟨ρa, ρk, hcak, (hT x).pa m i en hTe _ _ _ _ hPA, ?_⟩
    intro ρp w' ψ Yo Y hnp hkw hsubK hsplit hψβ hYo hY hPv
    obtain ⟨Ks, hKs, haKs⟩ := compS_reassoc hYo hY
    obtain ⟨f', hf', hwk'⟩ := hwk ha ρk ρp w' ψ Ks hkw hsplit hψβ hKs ⟨ρa, Y, haKs, hPv⟩ f hf
    have hwcl : ∀ lsO, en'.wc ls'' lsO Ks → extF ls'' lsO Ks := by
      intro lsO he; rw [hwc', hwc] at he; exact he
    refine ⟨Y, PMap.empty, ResU.comp_empty_right _, noOwn_empty, Or.inr (Or.inl
      ⟨K, m, i, v₀, en', pure_sep_mk ⟨rfl, hK, hTe', hab'.trans ha⟩ ⟨ρa, Ks, haKs, hPA' ▸ hPA,
        fun hu' => absurd (hq'.symm.trans hu') hq, f', hf', fun y hy lsO he =>
          ⟨fun k' hk' w σB XB hB hXB => ?_, fun hql => ?_⟩⟩⟩)⟩
    · -- the world the lender's continuation is resumed at, read at the borrowed share
      obtain ⟨hyi, hyInv⟩ := hwk' y hy
      simp only [erwpCK, show k' < n by omega, if_true]
      have he' := hwcl lsO he
      rw [hPB'] at hB
      have hσBβ : σB.InStratum β := (hT x).pb m i en hTe _ _ _ _ _ hB
      obtain ⟨ρb', hψσ, hXB'⟩ := compS_reassoc (ResU.CompS.comm hKs) hXB
      refine ih k' (by omega) y hyInv lsO _ ρb' XB hXB' (inStratum_compS hψσ hψβ hσBβ)
        (hOk ls ls'' lsO ψ Ks hr hls'' hKs he') (fun Bχ hBχ => ?_)
      obtain ⟨Xk, g, hXk, hXkg, hg⟩ :=
        rebReentry_split hψσ hBχ hχsplit hsplit hkw hnp hχimm
      have hwc'' : en.wc ls'' lsO ρk := by rw [hwc]; exact extF_reb hkw hsplit hreb hKs he'
      have hc := (hcont y hyi lsO hwc'').1 k' hk' w σB Xk hB hXk
      simp only [erwpCK, show k' < n by omega, if_true] at hc
      exact erwpK_garbage hXkg hg hc
    · -- a cancellable stop: the cancel obligation is the lender's, at the resumption world
      obtain ⟨hyi, -⟩ := hwk' y hy
      have he' := hwcl lsO he
      have hwc'' : en.wc ls'' lsO ρk := by rw [hwc]; exact extF_reb hkw hsplit hreb hKs he'
      have hql' : en.q ≠ .lin := hq' ▸ hql
      exact hcan x hx m i en en' hTe hTe' ha hql' y k lsO K ρk ρp w' ψ Ks hnp hkw hsplit hψβ hKs
        (hOk ls ls'' lsO ψ Ks hr hls'' hKs he') ((hcont y hyi lsO hwc'').2 hql')
  · -- a raise: no continuation is owed
    obtain ⟨ρo, ρk, h1, h2, h3⟩ := hR x hx k ls'' t _ (erwpCK (ℍ := ℍ) V Φ
      (fun y k ls t Ψ => BoLo.or (performStopK (flO y) (To y) k ls t Ψ) (RO y k ls t Ψ)) Q n) ρ' hr'
    refine ⟨ρo, ρk, h1, h2, fun ρp w ψ Yo Y a b c d e f g _ => ?_⟩
    obtain ⟨ρ'L, ρpL, h4, h5, h6⟩ := h3 ρp w ψ Yo Y a b c d e f g
    exact ⟨ρ'L, ρpL, h4, h5, Or.inr (Or.inr h6)⟩

/-! ### The constant world -/

/-- **`RebTwin` at one world**: a twin of the lifted table, every world allowed. -/
theorem rebTwin_lift {T T' : OpTabN} (hTw : T.Twin T') (lo : Life) (β : Life) (ρi χ R : WRes)
    (Pv : WRes → WRes → Prop) :
    (liftTabK T).RebTwin (fun _ => True) lo lo (liftTabK T') β ρi χ R Pv := by
  intro m i en hT
  obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some hT
  obtain ⟨en₀', h₀', hq, ha, hPA, hPB, hwc⟩ := hTw m i en₀ h₀
  refine ⟨liftEntK en₀', liftTabK_of_some h₀', hq, ha, hPA, ?_, hwc,
    fun _ _ _ _ _ _ _ _ _ _ _ f hf => ⟨f, hf, fun _ _ => ⟨trivial, trivial⟩⟩⟩
  show (fun _ => en₀'.PB) = fun _ => en₀.PB
  rw [hPB]

/-- `OpTabN.RebOKR` at the lifted table. -/
theorem OpTabN.RebOKR.liftK {T : OpTabN} {β : Life} (h : T.RebOKR β) :
    (liftTabK T).RebOKR β where
  entry m i en hT ha := by
    obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some hT
    exact h.entry m i en₀ h₀ ha
  pa m i en hT := by
    obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some hT
    exact h.pa m i en₀ h₀
  pb m i en hT _ := by
    obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some hT
    exact h.pb m i en₀ h₀

theorem OpTabN.RebOK.toR {T : OpTabN} {β : Life} (h : T.RebOK β) : T.RebOKR β :=
  ⟨fun m i en hT _ => ⟨by rw [(h.entry m i en hT).2.1]; decide, (h.entry m i en hT).2.2⟩,
    h.pa, h.pb⟩

theorem OpTabN.RebOKC.toR {T : OpTabN} {β : Life} (h : T.RebOKC β) : T.RebOKR β :=
  ⟨fun m i en hT _ => (h.entry m i en hT).2, h.pa, h.pb⟩

/-- `erwp_rebGen`'s `hcan` at one world: what holds of the share with the image holds of the share
with the cell. -/
theorem rebCanK_lift {β : Life} {le : Loc} {s : LSet} {v : Val} {R : WRes}
    {hs : R.InStratum s.join} {χ : WRes} {Ok : List SRec → Prop} (hreb : ResU.Reb β R χ)
    {T : OpTabN} (hcan : RebClosed β (ResU.single le (CellU.immOf s v R hs)) χ Ok T) :
    RebCanK (fun _ : Unit => True) (fun _ => liftTabK T) (fun _ => liftTabK T) β
      (ResU.single le (CellU.immOf s v R hs)) χ R Ok := by
  have hχsplit := ResU.restrictDom_split hreb
  have hχimm : NoOwn (χ.restrictDom (R.restrict Kind.imm)) :=
    noOwn_of_imm fun m ψ e => ResU.reb_imm_image hreb (ResU.restrictDom_get_inv e)
  intro _ _ m i en en' hT hT' ha hq _ k ls K ρk ρp w ψ Ks hnp hkw hsplit hψβ hKs hOk hin
  obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some hT
  obtain ⟨en₀', h₀', rfl⟩ := liftTabK_some hT'
  rw [h₀] at h₀'
  cases Option.some.inj h₀'
  refine (cancelOKK_liftEntK en₀ k ls K Ks).mpr fun P hP => ?_
  have hin' := (cancelOKK_liftEntK en₀ k ls K ρk).mp hin P hP
  obtain ⟨hcl, hgar⟩ := hcan m i en₀ h₀ ha hq P hP
  refine hcl k ls _ ψ Ks (ResU.CompS.comm hKs) hψβ hOk (fun Bχ hBχ => ?_)
  obtain ⟨Xk, g, hXk, hXkg, hg⟩ :=
    rebReentry_split (σB := PMap.empty) (ResU.comp_empty_right ψ) hBχ hχsplit hsplit hkw hnp
      hχimm
  obtain rfl := ResU.CompS.functional hXk (ResU.comp_empty_right ρk)
  exact hgar _ _ _ _ _ _ hXkg hg hin'

/-! ### The typed world -/

/-- **Every cell of a reborrow's image is at `β` or longer-lived**: an `own` or `mut` cell's image
is at `{β}`, an `imm` cell's at a subset of its lifetimes, all longer-lived than `β`. -/
theorem reb_at_ge {β : Life} {σ c : WRes} (hr : ResU.Reb β σ c) {m : Loc} {ψ : CellU Loc Val}
    (e : c.get m = some ψ) : β ≤ ψ.at := by
  obtain ⟨hσ, π, b, hdom, hbig, hle, hbody⟩ := hr
  obtain ⟨⟨l₀, q⟩, hpm, hpl⟩ := List.mem_map.mp ((hdom.2 m).mpr ⟨_, e⟩)
  simp only at hpl
  subst hpl
  have hq := hbody l₀ q hpm
  have hmem : q ∈ π.map Prod.snd := List.mem_map.mpr ⟨_, hpm, rfl⟩
  obtain ⟨b', hb', hle'⟩ := BigComp.leS_of_sublist (List.singleton_sublist.mpr hmem) hbig
  rw [(BigComp.singleton_iff ResU.compLawsS).mp hb'] at hle'
  have hqσ : ResU.Le q σ := hle'.trans hle
  obtain ⟨ζq, hζq⟩ := hq.1
  obtain ⟨τ, hτ⟩ := hqσ
  obtain ⟨ζ, hζ⟩ := comp_some hτ hζq
  rcases CellU.rep ζ with ⟨u, rfl⟩ | ⟨s, u, χ, hs, rfl⟩ | ⟨b₀, u, χ, hb₀, P, hw, rfl⟩
  · obtain ⟨hh, he⟩ := hq.2.1 u hζ
    rw [e] at he; cases Option.some.inj he
    exact le_rfl
  · obtain ⟨⟨t, ht, hts, he⟩, -⟩ := hq.2.2.2 s u χ hs hζ
    rw [e] at he; cases Option.some.inj he
    have h1 : β < s.meet := hσ l₀ _ hζ
    exact le_trans (le_of_lt h1) (s.meet_least _ (hts _ t.meet_mem))
  · obtain ⟨⟨hh, he⟩, -⟩ := hq.2.2.1 b₀ u χ hb₀ P hw hζ
    rw [e] at he; cases Option.some.inj he
    exact le_rfl

/-- **The borrowed share is dominated below `β` by the lender's**: a borrow cell of
`ρ_k ⊆ ψ ● χ|excl` shorter-lived than `β` is `ψ`'s, a part of `ψ ● ρᵢ`. -/
theorem reb_cellIn {β : Life} {R χ D ρk ρp w ψ Ks ρi : WRes} (hreb : ResU.Reb β R χ)
    (hkw : ResU.CompS ρk ρp w) (hsplit : ResU.CompS ψ (χ.restrictDom D) w)
    (hKs : ResU.CompS ψ ρi Ks) : ∀ a, a < β → CellIn ρk a → CellIn Ks a := by
  intro a ha hca
  rcases CellIn.split hsplit (CellIn.of_left hkw hca) with h | ⟨m, φ, e, -, hle⟩
  · exact CellIn.of_left hKs h
  · exact absurd (lt_of_le_of_lt (le_trans (reb_at_ge hreb (ResU.restrictDom_get_inv e)) hle) ha)
      (lt_irrefl _)

/-- **The view is consistent with the borrowed share** when it is with the lender's, the run's
resource and the lender's share valid: the image's cells are `imm`. -/
theorem consistentX_reb {c : Loc → Option Life} {β : Life} {R χ D ρk ρp w ψ Ks ρi : WRes}
    (hreb : ResU.Reb β R χ) (hkw : ResU.CompS ρk ρp w)
    (hsplit : ResU.CompS ψ (χ.restrictDom D) w) (hKs : ResU.CompS ψ ρi Ks) (hvw : ResU.Valid w)
    (hvK : ResU.Valid Ks) (hc : ConsistentX c Ks) : ConsistentX c ρk := by
  have hcχ : ConsistentX c (χ.restrictDom D) := by
    intro e he x ψ' hg _
    obtain rfl : e = PMap.empty := ExS.functional he (ExW.empty_of_all_imm fun m ψ e =>
      (reb_cell hreb (ResU.restrictDom_get_inv e)).1)
    cases hg
  exact consistentX_left hkw (consistentX_compS hsplit (consistentX_left hKs hc hvK) hcχ) hvw

/-- **The typed reborrow across a Kripke stop.** The lender's stop at `x`, at a floor `f′ ≤ f`
below `β`, owes its continuation at `y` at `ψ ● ρᵢ`. Then `y` is owed at the floor `f` at the
borrowed share. -/
theorem kw_owed_reb {x y : KW} {f f' β : Life} (hf' : f' ≤ f) (hfβ : f' < β)
    {R χ D ρk ρp w ψ Ks ρi : WRes} (hreb : ResU.Reb β R χ) (hkw : ResU.CompS ρk ρp w)
    (hsplit : ResU.CompS ψ (χ.restrictDom D) w) (hKs : ResU.CompS ψ ρi Ks) (hvw : ResU.Valid w)
    (hvK : ResU.Valid Ks) (hy : x.Owed f' y Ks) : x.Owed f y ρk :=
  ⟨(hy.1.share fun a ha hca => reb_cellIn hreb hkw hsplit hKs a (lt_of_le_of_lt ha hfβ) hca).mono
    hf', hy.2.1, consistentX_reb hreb hkw hsplit hKs hvw hvK hy.2.2.1, hy.2.2.2.1,
    fun g hg h => hy.2.2.2.2 g (le_trans hf' hg) h⟩

/-- **`RebTwin` at the typed world.** The borrowed entries and the lender's owe along `KW.Owed` at
the same world `x`; a borrowed stop at the floor `f` is the lender's at `min f (↓β)`, below the
reborrow. -/
theorem rebTwin_owed {x : KW} {lo β : Life} {ρi χ R : WRes} (hreb : ResU.Reb β R χ)
    {Ti To : OpTabK KW}
    (hTw : ∀ m i en, Ti m i = some en → ∃ en', To m i = some en' ∧ en'.q = en.q ∧
      en'.abort = en.abort ∧ en'.PA = en.PA ∧ en'.PB = en.PB ∧ en'.wc = en.wc ∧
      (en.abort = false →
        (∀ f z ρ, x.Owed f z ρ → en.wk f z ρ) ∧ (∀ f z ρ, en'.wk f z ρ → x.Owed f z ρ))) :
    Ti.RebTwin (fun _ => True) lo lo To β ρi χ R (fun w Y => ResU.Valid w ∧ ResU.Valid Y) := by
  intro m i en hTe
  obtain ⟨en', hTe', h₁, h₂, h₃, h₄, h₅, hwk⟩ := hTw m i en hTe
  refine ⟨en', hTe', h₁, h₂, h₃, h₄, h₅, fun ha ρk ρp w ψ Ks hkw hsplit _ hKs hPv f hf =>
    ⟨min f (↓β), le_trans (min_le_left _ _) hf, fun y hy => ?_⟩⟩
  obtain ⟨hin, hout⟩ := hwk ha
  obtain ⟨ρo, Y, haKs, hvw, hvY⟩ := hPv
  have hvK : ResU.Valid Ks := (ResU.Valid.split haKs hvY).2
  exact ⟨hin _ _ _ (kw_owed_reb (min_le_left _ _)
    (lt_of_le_of_lt (min_le_right _ _) (Life.down_sqsubset β)) hreb hkw hsplit hKs hvw hvK
    (hout _ _ _ hy)), trivial⟩

end BoCa.Fig16.LogRel.Core.Chain.SI

end
