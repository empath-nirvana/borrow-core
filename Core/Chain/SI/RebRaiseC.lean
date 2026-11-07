import Core.Chain.SI.RebStopD
import Core.Chain.SI.RebCancelC

/-!
# A reborrow live across raises and layered cancel runs

**Not a transcription.** `erwp_reborrowT` (`SI/RebCancelC.lean`) at a table with abortive entries
and with cancel obligations that are cancel runs stopping at cancellable entries of their own.
The lemmas are stated once for both entries of 6.150's run, the record's cell (`rwpG_rebG`) and
a chain view (`rwpG_rebDeepG`): `RebEntryG` is their common shape.

* **At a raise:** the borrowed run raises with a payload in `PA` owning nothing, beside a part
  owning nothing; the lender raises with the same payload, its share `ψ` (6.52's `SubKeep` of a
  part owning nothing) and the cell `ρᵢ` (an `imm` cell) owning nothing.
* **At a cancellable stop:** the lender's cancel obligation at its folded share `ψ ● ρᵢ` is the
  borrowed continuation's at `ψ ● χ`, through the premise `hcan`: the obligation is closed under
  the reborrow. For a cancel run that premise is `erwp_rebGen_cancelRun` one level down
  (`Withload791N.tab_rebClosed`, by induction on how deep cancel rows nest).

* `RebEntryG`, `rebEntryG_top`, `rebEntryG_deep`;
* `OpTabN.RebOKR`: `RebOKC` with abortive entries allowed, unrestricted ones included;
* `erwp_rebGen_cancelRun`, `erwp_rebGen`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Kont performE raiseE cancelVal opPayload)
open BoCa.Lifetime (LSub LifeVar)

/-- **The entry of 6.150's run at a cell `ρᵢ` with image `χ` of its witness `R`**: the shape of
`rwpG_rebG` and `rwpG_rebDeepG`. `Ok` is what the entry asks of the list (the record on it). -/
def RebEntryG (Φ : LocFam) (β : Life) (ρi χ R : WRes) (Ok : List SRec → Prop) : Prop :=
  ∀ (Qin Qout : PostG) (n : Nat) (ls : List SRec) (e : Expr) (ρb ρ : WRes),
    ResU.CompS ρi ρb ρ → ρb.InStratum β → Ok ls →
    (∀ k, k ≤ n → ∀ ls'' t (ρ' : WRes), Qin k ls'' t ρ' → (∀ y, y ∈ ls'' ↔ y ∈ ls) →
      ∃ ρo ρk, ResU.CompS ρo ρk ρ' ∧ ρo.InStratum β ∧
        ∀ (ρp w ψ Yo Y : WRes), NoOwn ρp → ResU.CompS ρk ρp w →
          ResU.SubKeep w (χ.restrictDom R.exclPart) ψ →
          ResU.CompS ψ (χ.restrictDom R.exclPart) w → ψ.InStratum β →
          ResU.CompS ρo ψ Yo → ResU.CompS Yo ρi Y →
          ∃ ρ'L ρpL, ResU.CompS ρ'L ρpL Y ∧ NoOwn ρpL ∧ Qout k ls'' t ρ'L) →
    (∀ Bχ, ResU.CompS ρb χ Bχ → rwpG (ℍ := ℍ) Φ Qin n ls e Bχ) →
    rwpG (ℍ := ℍ) Φ Qout n ls e ρ

/-- `rwpG_rebG` is a `RebEntryG` at the record's cell. -/
theorem rebEntryG_top {Φ : LocFam} (r : FrameRec) (x : LifeVar) (hx : ¬ VFree x r.T)
    {β : Life} {s : LSet} {hs : r.R.InStratum s.join} (hS : TmplSpec r (tmpl r))
    (hRβ : r.R.InStratum β)
    (hshape : vShape (r.T.immReborrow (.var x)) (r.δ.extend x β) r.v (canon r β))
    (hβs : ∀ y, s.mem y → β ⊑ y) :
    RebEntryG (ℍ := ℍ) Φ β (ResU.single r.le (CellU.immOf s r.v r.R hs)) (canon r β) r.R
      (fun ls => r ∈ rsOf ls) :=
  fun _ _ _ _ _ _ _ hc hb hr hpost hA => rwpG_rebG r x hx hS hRβ hshape hc hb hr hβs hpost hA

/-- `rwpG_rebDeepG` is a `RebEntryG` at a chain view. -/
theorem rebEntryG_deep {Φ : LocFam} (r : FrameRec) {p₀ : Option Loc} {l₀ : Loc} {S₀ : VTy}
    {u₀ : Val} (hch₀ : Chain r.R r.T r.v p₀ l₀ S₀ u₀) {w₀ : WRes} (x : LifeVar)
    (hx : ¬ VFree x S₀) {β : Life} {s : LSet} {hs : w₀.InStratum s.join}
    (hS : TmplSpecD r S₀ u₀ w₀ (tmplD r S₀ u₀ w₀)) (hRβ : w₀.InStratum β)
    (hβc : (CellU.immOf s u₀ w₀ hs).InStratum β)
    (hshape : vShape (S₀.immReborrow (.var x)) (r.δ.extend x β) u₀ (canonD r S₀ u₀ w₀ β)) :
    RebEntryG (ℍ := ℍ) Φ β (ResU.single l₀ (CellU.immOf s u₀ w₀ hs)) (canonD r S₀ u₀ w₀ β) w₀
      (fun ls => r ∈ rsOf ls) :=
  fun _ _ _ _ _ _ _ hc hb hr hpost hA =>
    rwpG_rebDeepG r hch₀ x hx hS hRβ hβc hshape hc hb hr hpost hA

/-- **A table whose stops may be taken under a live reborrow at `β`, raises and cancellable
entries included**: no resumable entry unrestricted, every one resumed under `extF`, payloads and
answers in `Res_β`. An abortive entry may be unrestricted: its stop is a `raise`, which never
resumes, so the reborrow is never re-entered through it. -/
structure OpTabN.RebOKR (T : OpTabN) (β : Life) : Prop where
  entry : ∀ m i en, T m i = some en → en.abort = false → en.q ≠ .unr ∧ en.wc = extF
  pa : ∀ m i en, T m i = some en → ∀ k ls v (ρ : WRes), en.PA k ls v ρ → ρ.InStratum β
  pb : ∀ m i en, T m i = some en → ∀ k ls w (ρ : WRes), en.PB k ls w ρ → ρ.InStratum β

/-- **A cancel obligation closed under the reborrow at `ρᵢ`, `χ`**: what holds of the share with
the image holds of the share with the cell, and it is closed under garbage. -/
def RebClosed (β : Life) (ρi χ : WRes) (Ok : List SRec → Prop) (T : OpTabN) : Prop :=
  ∀ m i en, T m i = some en → en.abort = false → en.q ≠ .lin → ∀ P, en.fin = some P →
    (∀ k ls e (ρb ρ : WRes), ResU.CompS ρi ρb ρ → ρb.InStratum β → Ok ls →
      (∀ Bχ, ResU.CompS ρb χ Bχ → P k ls e Bχ) → P k ls e ρ) ∧
    (∀ k ls e (ρ g ρg : WRes), ResU.CompS ρ g ρg → NoOwn g → P k ls e ρ → P k ls e ρg)

/-- The record is kept across a resume, at either entry: the lender's share holds the cell. -/
theorem okKept_top {r : FrameRec} {s : LSet} {hs : r.R.InStratum s.join} :
    ∀ (ls ls'' lsO : List SRec) (ψ Ks : WRes), r ∈ rsOf ls → (∀ y, y ∈ ls'' ↔ y ∈ ls) →
      ResU.CompS ψ (ResU.single r.le (CellU.immOf s r.v r.R hs)) Ks → extF ls'' lsO Ks →
      r ∈ rsOf lsO :=
  fun _ _ _ _ _ hr hls hKs he => rec_kept hr hls hKs he

theorem okKept_deep {r : FrameRec} {p₀ : Option Loc} {l₀ : Loc} {S₀ : VTy} {u₀ : Val}
    (hch₀ : Chain r.R r.T r.v p₀ l₀ S₀ u₀) {w₀ : WRes} {s : LSet} {hs : w₀.InStratum s.join} :
    ∀ (ls ls'' lsO : List SRec) (ψ Ks : WRes), r ∈ rsOf ls → (∀ y, y ∈ ls'' ↔ y ∈ ls) →
      ResU.CompS ψ (ResU.single l₀ (CellU.immOf s u₀ w₀ hs)) Ks → extF ls'' lsO Ks →
      r ∈ rsOf lsO := by
  intro _ _ _ _ _ hr hls'' hKs he'
  obtain ⟨t', ht⟩ := mem_rsOf.mp hr
  exact he' r (mem_rsOf.mpr ⟨t', (hls'' _).mpr ht⟩)
    ⟨l₀, Frz.of_compS_right hKs (Frz.imm (ResU.single_get_self _ _) (by simp)),
      Or.inr ⟨p₀, S₀, u₀, hch₀⟩⟩

/-- **6.150 over a cancel run, its stops cancellable and its final raise carrying an error.** The
lender's cancel run is the borrowed one with the reborrow folded at every stop, re-entered at the
image at the resume, its cancel obligations closed under the reborrow (`hcan`); at the final
raise everything the lender holds besides the error payload owns nothing. -/
theorem erwp_rebGen_cancelRun {Φ : LocFam} {β : Life} {le : Loc} {s : LSet} {v : Val}
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
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ls e ρb ρ hc hb hr hA
  have hχsplit := ResU.restrictDom_split hreb
  have hχimm : NoOwn (χ.restrictDom (R.restrict Kind.imm)) :=
    noOwn_of_imm fun m ψ e => ResU.reb_imm_image hreb (ResU.restrictDom_get_inv e)
  rw [erwp_eq]
  refine hE _ _ n ls e ρb ρ hc hb hr ?_ (fun Bχ hBχ => by
    have h := hA Bχ hBχ
    rw [erwp_eq] at h
    exact h)
  intro k hk ls'' t ρ' hQin hls''
  rcases hQin with ⟨w, -, hf⟩ | ⟨K, err, hp⟩ | ⟨K, m, i, v₀, en, hp⟩
  · exact hf.elim
  · -- the cancel's `raise`: the error payload kept, everything else owns nothing
    obtain ⟨⟨rfl, hK⟩, τa, τb, hcab, herr, hnb⟩ := pure_sep_iff.mp hp
    have hτaβ : τa.InStratum β := by
      cases err with
      | none => obtain rfl : τa = PMap.empty := herr.1; exact ResU.inStratum_empty β
      | some E =>
          obtain ⟨m, j', w', en, he⟩ := herr
          obtain ⟨⟨-, hTe, -⟩, hPA, -⟩ := pure_sep_iff.mp he
          exact hT₁.pa _ _ en hTe _ _ _ _ hPA
    refine ⟨τa, τb, hcab, hτaβ, ?_⟩
    intro ρp w' ψ Yo Y hnp hkw hsubK hsplit hψβ hYo hY
    obtain ⟨Ks, hKs, haKs⟩ := compS_reassoc hYo hY
    have hnKs : NoOwn Ks := noOwn_compS hKs (noOwn_subKeep hsubK (noOwn_compS hkw hnb hnp))
      (noOwn_single_imm _ _ _ _ _)
    exact ⟨Y, PMap.empty, ResU.comp_empty_right _, noOwn_empty, Or.inr (Or.inl
      ⟨K, err, pure_sep_mk ⟨rfl, hK⟩ ⟨τa, Ks, haKs, herr, hnKs⟩⟩)⟩
  · -- a stop of the cancel run: the fold
    obtain ⟨⟨rfl, hK, hTe, ha⟩, ρa, ρk, hcak, hPA, hu, hcont⟩ := pure_sep_iff.mp hp
    obtain ⟨hq, hwc⟩ := hT₁.entry m i en hTe ha
    refine ⟨ρa, ρk, hcak, hT₁.pa m i en hTe _ _ _ _ hPA, ?_⟩
    intro ρp w' ψ Yo Y hnp hkw hsubK hsplit hψβ hYo hY
    obtain ⟨Ks, hKs, haKs⟩ := compS_reassoc hYo hY
    refine ⟨Y, PMap.empty, ResU.comp_empty_right _, noOwn_empty, Or.inr (Or.inr
      ⟨K, m, i, v₀, en, pure_sep_mk ⟨rfl, hK, hTe, ha⟩ ⟨ρa, Ks, haKs, hPA,
        fun hu' => absurd hu' hq, fun lsO he =>
          ⟨fun k' hk' w σB XB hB hXB => ?_, fun hql P hP => ?_⟩⟩⟩)⟩
    · simp only [erwpC, show k' < n by omega, if_true]
      have he' : extF ls'' lsO Ks := by rw [hwc] at he; exact he
      have hσBβ : σB.InStratum β := hT₁.pb m i en hTe _ _ _ _ hB
      obtain ⟨ρb', hψσ, hXB'⟩ := compS_reassoc (ResU.CompS.comm hKs) hXB
      refine ih k' (by omega) lsO _ ρb' XB hXB' (inStratum_compS hψσ hψβ hσBβ)
        (hOk ls ls'' lsO ψ Ks hr hls'' hKs he') (fun Bχ hBχ => ?_)
      obtain ⟨Xk, g, hXk, hXkg, hg⟩ :=
        rebReentry_split hψσ hBχ hχsplit hsplit hkw hnp hχimm
      have hwc' : en.wc ls'' lsO ρk := by rw [hwc]; exact extF_reb hkw hsplit hreb hKs he'
      have hc := (hcont lsO hwc').1 k' hk' w σB Xk hB hXk
      simp only [erwpC, show k' < n by omega, if_true] at hc
      exact erwp_garbage hXkg hg hc
    · -- a nested cancel obligation, closed under the reborrow
      have he' : extF ls'' lsO Ks := by rw [hwc] at he; exact he
      have hwc' : en.wc ls'' lsO ρk := by rw [hwc]; exact extF_reb hkw hsplit hreb hKs he'
      have hin := (hcont lsO hwc').2 hql P hP
      obtain ⟨hcl, hgar⟩ := hcan m i en hTe ha hql P hP
      refine hcl k lsO _ ψ Ks (ResU.CompS.comm hKs) hψβ (hOk ls ls'' lsO ψ Ks hr hls'' hKs he')
        (fun Bχ hBχ => ?_)
      obtain ⟨Xk, g, hXk, hXkg, hg⟩ :=
        rebReentry_split (σB := PMap.empty) (ResU.comp_empty_right ψ) hBχ hχsplit hsplit hkw hnp
          hχimm
      obtain rfl := ResU.CompS.functional hXk (ResU.comp_empty_right ρk)
      exact hgar _ _ _ _ _ _ hXkg hg hin

/-- **`[TR]` 6.150 at `erwp` across stops, raises and layered cancel runs.** `erwp_reborrowT` at a
table with abortive entries and cancellable entries whose cancel obligations are closed under the
reborrow (`hcan`), at either entry (`RebEntryG`). -/
theorem erwp_rebGen {Φ : LocFam} {β : Life} {le : Loc} {s : LSet} {v : Val}
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
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ls e ρb ρ hc hb hr hA
  have hχsplit := ResU.restrictDom_split hreb
  have hχimm : NoOwn (χ.restrictDom (R.restrict Kind.imm)) :=
    noOwn_of_imm fun m ψ e => ResU.reb_imm_image hreb (ResU.restrictDom_get_inv e)
  rw [erwp_eq]
  refine hE _ _ n ls e ρb ρ hc hb hr ?_ (fun Bχ hBχ => by
    have h := hA Bχ hBχ
    rw [erwp_eq] at h
    exact h)
  intro k hk ls'' t ρ' hQin hls''
  rcases hQin with ⟨w, rfl, hbox⟩ | ⟨K, m, i, v₀, en, hp⟩ | ⟨K, m, i, v₀, en, hp⟩
  · -- a return: 6.150's exit as printed
    obtain ⟨hQ, hρ'β⟩ := hbox
    refine ⟨ρ', PMap.empty, ResU.comp_empty_right _, hρ'β, ?_⟩
    intro ρp w' ψ Yo Y hnp hkw hsubK hsplit hψβ hYo hY
    obtain rfl : w' = ρp := ResU.CompS.functional hkw (ResU.comp_empty_left _)
    obtain ⟨g, hg, hρ'g⟩ := compS_reassoc hYo hY
    exact ⟨ρ', g, hρ'g, noOwn_compS hg (noOwn_subKeep hsubK hnp) (noOwn_single_imm _ _ _ _ _),
      Or.inl ⟨w, rfl, hQ⟩⟩
  · -- a stop: the fold
    obtain ⟨⟨rfl, hK, hTe, ha⟩, ρa, ρk, hcak, hPA, -, hcont⟩ := pure_sep_iff.mp hp
    obtain ⟨hq, hwc⟩ := hT.entry m i en hTe ha
    refine ⟨ρa, ρk, hcak, hT.pa m i en hTe _ _ _ _ hPA, ?_⟩
    intro ρp w' ψ Yo Y hnp hkw hsubK hsplit hψβ hYo hY
    obtain ⟨Ks, hKs, haKs⟩ := compS_reassoc hYo hY
    refine ⟨Y, PMap.empty, ResU.comp_empty_right _, noOwn_empty, Or.inr (Or.inl
      ⟨K, m, i, v₀, en, pure_sep_mk ⟨rfl, hK, hTe, ha⟩ ⟨ρa, Ks, haKs, hPA,
        fun hu' => absurd hu' hq, fun lsO he =>
          ⟨fun k' hk' w σB XB hB hXB => ?_, fun hql P hP => ?_⟩⟩⟩)⟩
    · simp only [erwpC, show k' < n by omega, if_true]
      have he' : extF ls'' lsO Ks := by rw [hwc] at he; exact he
      have hσBβ : σB.InStratum β := hT.pb m i en hTe _ _ _ _ hB
      obtain ⟨ρb', hψσ, hXB'⟩ := compS_reassoc (ResU.CompS.comm hKs) hXB
      refine ih k' (by omega) lsO _ ρb' XB hXB' (inStratum_compS hψσ hψβ hσBβ)
        (hOk ls ls'' lsO ψ Ks hr hls'' hKs he') (fun Bχ hBχ => ?_)
      obtain ⟨Xk, g, hXk, hXkg, hg⟩ :=
        rebReentry_split hψσ hBχ hχsplit hsplit hkw hnp hχimm
      have hwc' : en.wc ls'' lsO ρk := by rw [hwc]; exact extF_reb hkw hsplit hreb hKs he'
      have hc := (hcont lsO hwc').1 k' hk' w σB Xk hB hXk
      simp only [erwpC, show k' < n by omega, if_true] at hc
      exact erwp_garbage hXkg hg hc
    · -- the cancel obligation at the folded share: the borrowed continuation's, re-entered
      have he' : extF ls'' lsO Ks := by rw [hwc] at he; exact he
      have hwc' : en.wc ls'' lsO ρk := by rw [hwc]; exact extF_reb hkw hsplit hreb hKs he'
      have hin := (hcont lsO hwc').2 hql P hP
      obtain ⟨hcl, hgar⟩ := hcan m i en hTe ha hql P hP
      refine hcl k lsO _ ψ Ks (ResU.CompS.comm hKs) hψβ (hOk ls ls'' lsO ψ Ks hr hls'' hKs he')
        (fun Bχ hBχ => ?_)
      obtain ⟨Xk, g, hXk, hXkg, hg⟩ :=
        rebReentry_split (σB := PMap.empty) (ResU.comp_empty_right ψ) hBχ hχsplit hsplit hkw hnp
          hχimm
      obtain rfl := ResU.CompS.functional hXk (ResU.comp_empty_right ρk)
      exact hgar _ _ _ _ _ _ hXkg hg hin
  · -- a raise: the lender raises with the same payload, the rest owning nothing
    obtain ⟨⟨rfl, hK, hTe, ha⟩, ρa, ρn, hcan', ⟨hPA, hnA⟩, hnn⟩ := pure_sep_iff.mp hp
    refine ⟨ρa, ρn, hcan', hT.pa m i en hTe _ _ _ _ hPA, ?_⟩
    intro ρp w' ψ Yo Y hnp hkw hsubK hsplit hψβ hYo hY
    obtain ⟨Ks, hKs, haKs⟩ := compS_reassoc hYo hY
    have hnKs : NoOwn Ks := noOwn_compS hKs (noOwn_subKeep hsubK (noOwn_compS hkw hnn hnp))
      (noOwn_single_imm _ _ _ _ _)
    exact ⟨Y, PMap.empty, ResU.comp_empty_right _, noOwn_empty, Or.inr (Or.inr
      ⟨K, m, i, v₀, en, pure_sep_mk ⟨rfl, hK, hTe, ha⟩ ⟨ρa, Ks, haKs, ⟨hPA, hnA⟩, hnKs⟩⟩)⟩

end BoCa.Fig16.LogRel.Core.Chain.SI

end
