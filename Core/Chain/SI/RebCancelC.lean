import Core.Chain.SI.RebAcrossC
import Core.Chain.SI.IStopCancelN

/-!
# A reborrow live across a cancellable stop

**Not a transcription.** `SI/IStopCancelN.lean`'s design at 6.150. A reborrow returns nothing
owned to the lender beyond what the borrowed run held: the image is `imm` cells, and the lender's
cell `ρᵢ` is an `imm` cell. So a cancel run through a live reborrow needs no claim: the lender's
cancel run, from its folded share `ψ ● ρᵢ`, re-enters the reborrow at the canonical image and runs
the borrowed continuation's cancel run; at the cancel's `raise` everything the lender holds is
garbage (`ψ` by 6.52's `SubKeep`, `ρᵢ` an `imm` cell). The lender's stops are at the same table
as the borrowed run's.

* `erwp_reborrow_cancelRun`: 6.150 over a cancel run (`cancelTabN T₁` inside and outside).
* `erwp_reborrowT`: `erwp_reborrow` at a table with cancellable entries, whose cancel obligation
  is a cancel run at `T₁`; the lender meets it from the borrowed continuation's by
  `erwp_reborrow_cancelRun` at the folded share.
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

/-- The re-entry's resources: from the lender's share `ψ ● σ_B` with the image added, the
borrowed continuation's `ρₖ ● σ_B` and garbage. -/
theorem rebReentry_split {ψ σB ρb' χ Bχ w' ρk ρp χi χe : WRes}
    (hψσ : ResU.CompS ψ σB ρb') (hBχ : ResU.CompS ρb' χ Bχ) (hχsplit : ResU.CompS χi χe χ)
    (hsplit : ResU.CompS ψ χe w') (hkw : ResU.CompS ρk ρp w') (hnp : NoOwn ρp)
    (hχimm : NoOwn χi) :
    ∃ Xk g, ResU.CompS ρk σB Xk ∧ ResU.CompS Xk g Bχ ∧ NoOwn g := by
  obtain ⟨ψχ, hψχ, hψχσ⟩ := compS_exch hψσ hBχ
  obtain ⟨w₁, hw₁, hw₁χ⟩ := compS_reassoc' (ResU.CompS.comm hχsplit) hψχ
  obtain rfl : w₁ = w' := ResU.CompS.functional hw₁ hsplit
  obtain ⟨g, hg, hkg⟩ := compS_reassoc hkw hw₁χ
  obtain ⟨Xk, hXk, hXkg⟩ := compS_exch hkg hψχσ
  exact ⟨Xk, g, hXk, hXkg, noOwn_compS hg hnp hχimm⟩

/-- **6.150 over a cancel run.** The lender's cancel run is the borrowed one with the reborrow
folded at every finaliser's stop and re-entered at the canonical image at the resume; at the
cancel's `raise` it owns nothing. -/
theorem erwp_reborrow_cancelRun {Φ : LocFam} (r : FrameRec) (x : LifeVar) (hx : ¬ VFree x r.T)
    {β : Life} {s : LSet} {hs : r.R.InStratum s.join} (hS : TmplSpec r (tmpl r))
    (hRβ : r.R.InStratum β)
    (hshape : vShape (r.T.immReborrow (.var x)) (r.δ.extend x β) r.v (canon r β))
    (hβs : ∀ y, s.mem y → β ⊑ y) {T₁ : OpTabN} (hT : T₁.RebOK β) :
    ∀ n ls e (ρb ρ : WRes),
      ResU.CompS (ResU.single r.le (CellU.immOf s r.v r.R hs)) ρb ρ → ρb.InStratum β →
      r ∈ rsOf ls →
      (∀ Bχ, ResU.CompS ρb (canon r β) Bχ →
        erwp (ℍ := ℍ) Φ (cancelTabN T₁) (fun _ _ _ _ => False) n ls e Bχ) →
      erwp (ℍ := ℍ) Φ (cancelTabN T₁) (fun _ _ _ _ => False) n ls e ρ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ls e ρb ρ hc hb hr hA
  have hreb : ResU.Reb β r.R (canon r β) := canon_reb hS hRβ
  have hχsplit := ResU.restrictDom_split hreb
  have hχimm : NoOwn ((canon r β).restrictDom (r.R.restrict Kind.imm)) :=
    noOwn_of_imm fun m ψ e => ResU.reb_imm_image hreb (ResU.restrictDom_get_inv e)
  rw [erwp_eq]
  refine rwpG_rebG r x hx hS hRβ hshape hc hb hr hβs ?_ (fun Bχ hBχ => by
    have h := hA Bχ hBχ
    rw [erwp_eq] at h
    exact h)
  intro k hk ls'' t ρ' hQin hls''
  rcases hQin with ⟨w, -, hf⟩ | ⟨K, err, hp⟩ | ⟨K, m, i, v₀, en, hp⟩
  · exact hf.elim
  · -- the cancel's `raise`: everything the lender holds is garbage
    obtain ⟨⟨rfl, hK⟩, τa, τb, hcab, herr, hnb⟩ := pure_sep_iff.mp hp
    cases err with
    | some E =>
        obtain ⟨m, j', w', en, he⟩ := herr
        obtain ⟨⟨-, hTe, ha⟩, -⟩ := pure_sep_iff.mp he
        exact absurd ha (by rw [(hT.entry _ _ en hTe).1]; simp)
    | none =>
    obtain rfl : τa = PMap.empty := herr.1
    obtain rfl := eq_of_compS_empty_left hcab
    refine ⟨PMap.empty, _, compS_empty_left _, ResU.inStratum_empty β, ?_⟩
    intro ρp w' ψ Yo Y hnp hkw hsubK hsplit hψβ hYo hY
    obtain rfl := eq_of_compS_empty_left hYo
    have hnY : NoOwn Y := noOwn_compS hY (noOwn_subKeep hsubK (noOwn_compS hkw hnb hnp))
      (noOwn_single_imm _ _ _ _ _)
    exact ⟨Y, PMap.empty, ResU.comp_empty_right _, noOwn_empty, Or.inr (Or.inl
      ⟨K, none, pure_sep_mk ⟨rfl, hK⟩ ⟨PMap.empty, Y, compS_empty_left _, emp_empty, hnY⟩⟩)⟩
  · -- a finaliser's stop: the fold, as in `erwp_reborrow`
    obtain ⟨⟨rfl, hK, hTe, ha⟩, ρa, ρk, hcak, hPA, -, hcont⟩ := pure_sep_iff.mp hp
    obtain ⟨-, hq, hwc⟩ := hT.entry m i en hTe
    refine ⟨ρa, ρk, hcak, hT.pa m i en hTe _ _ _ _ hPA, ?_⟩
    intro ρp w' ψ Yo Y hnp hkw hsubK hsplit hψβ hYo hY
    obtain ⟨Ks, hKs, haKs⟩ := compS_reassoc hYo hY
    refine ⟨Y, PMap.empty, ResU.comp_empty_right _, noOwn_empty, Or.inr (Or.inr
      ⟨K, m, i, v₀, en, pure_sep_mk ⟨rfl, hK, hTe, ha⟩ ⟨ρa, Ks, haKs, hPA,
        fun hu' => absurd (hq.symm.trans hu') (by simp), fun lsO he =>
          ⟨fun k' hk' w σB XB hB hXB => ?_, fun hq' => absurd hq hq'⟩⟩⟩)⟩
    simp only [erwpC, show k' < n by omega, if_true]
    have he' : extF ls'' lsO Ks := by rw [hwc] at he; exact he
    have hσBβ : σB.InStratum β := hT.pb m i en hTe _ _ _ _ hB
    obtain ⟨ρb', hψσ, hXB'⟩ := compS_reassoc (ResU.CompS.comm hKs) hXB
    have hr' : r ∈ rsOf lsO := rec_kept hr hls'' hKs he'
    refine ih k' (by omega) lsO _ ρb' XB hXB' (inStratum_compS hψσ hψβ hσBβ) hr'
      (fun Bχ hBχ => ?_)
    obtain ⟨Xk, g, hXk, hXkg, hg⟩ :=
      rebReentry_split hψσ hBχ hχsplit hsplit hkw hnp hχimm
    have hwc' : en.wc ls'' lsO ρk := by rw [hwc]; exact extF_reb hkw hsplit hreb hKs he'
    have hc := (hcont lsO hwc').1 k' hk' w σB Xk hB hXk
    simp only [erwpC, show k' < n by omega, if_true] at hc
    exact erwp_garbage hXkg hg hc

/-- **A table whose stops may be taken under a live reborrow at `β`, cancellable entries
included.** -/
structure OpTabN.RebOKC (T : OpTabN) (β : Life) : Prop where
  entry : ∀ m i en, T m i = some en → en.abort = false ∧ en.q ≠ .unr ∧ en.wc = extF
  pa : ∀ m i en, T m i = some en → ∀ k ls v (ρ : WRes), en.PA k ls v ρ → ρ.InStratum β
  pb : ∀ m i en, T m i = some en → ∀ k ls w (ρ : WRes), en.PB k ls w ρ → ρ.InStratum β

/-- **`[TR]` 6.150 at `erwp` across stops, cancellable ones included.** As `erwp_reborrow`, at a
table whose cancellable entries owe a cancel run at `T₁`: the lender's stops are at the same
table, and its cancel obligation at the folded share is the borrowed continuation's, re-entered
at the canonical image (`erwp_reborrow_cancelRun`). -/
theorem erwp_reborrowT {Φ : LocFam} (r : FrameRec) (x : LifeVar) (hx : ¬ VFree x r.T)
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
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ls e ρb ρ hc hb hr hA
  set χ : WRes := canon r β with hχdef
  have hreb : ResU.Reb β r.R χ := canon_reb hS hRβ
  have hχsplit := ResU.restrictDom_split hreb
  have hχimm : NoOwn (χ.restrictDom (r.R.restrict Kind.imm)) :=
    noOwn_of_imm fun m ψ e => ResU.reb_imm_image hreb (ResU.restrictDom_get_inv e)
  rw [erwp_eq]
  refine rwpG_rebG r x hx hS hRβ hshape hc hb hr hβs ?_ (fun Bχ hBχ => by
    have h := hA Bχ hBχ
    rw [erwp_eq] at h
    exact h)
  intro k hk ls'' t ρ' hQin hls''
  rcases hQin with ⟨w, rfl, hbox⟩ | ⟨K, m, i, v₀, en, hp⟩ | ⟨K, m, i, v₀, en, hp⟩
  · obtain ⟨hQ, hρ'β⟩ := hbox
    refine ⟨ρ', PMap.empty, ResU.comp_empty_right _, hρ'β, ?_⟩
    intro ρp w' ψ Yo Y hnp hkw hsubK hsplit hψβ hYo hY
    obtain rfl : w' = ρp := ResU.CompS.functional hkw (ResU.comp_empty_left _)
    obtain ⟨g, hg, hρ'g⟩ := compS_reassoc hYo hY
    exact ⟨ρ', g, hρ'g, noOwn_compS hg (noOwn_subKeep hsubK hnp) (noOwn_single_imm _ _ _ _ _),
      Or.inl ⟨w, rfl, hQ⟩⟩
  · obtain ⟨⟨rfl, hK, hTe, ha⟩, ρa, ρk, hcak, hPA, -, hcont⟩ := pure_sep_iff.mp hp
    obtain ⟨-, hq, hwc⟩ := hT.entry m i en hTe
    refine ⟨ρa, ρk, hcak, hT.pa m i en hTe _ _ _ _ hPA, ?_⟩
    intro ρp w' ψ Yo Y hnp hkw hsubK hsplit hψβ hYo hY
    obtain ⟨Ks, hKs, haKs⟩ := compS_reassoc hYo hY
    refine ⟨Y, PMap.empty, ResU.comp_empty_right _, noOwn_empty, Or.inr (Or.inl
      ⟨K, m, i, v₀, en, pure_sep_mk ⟨rfl, hK, hTe, ha⟩ ⟨ρa, Ks, haKs, hPA,
        fun hu' => absurd hu' hq, fun lsO he =>
          ⟨fun k' hk' w σB XB hB hXB => ?_, fun hql => ?_⟩⟩⟩)⟩
    · simp only [erwpC, show k' < n by omega, if_true]
      have he' : extF ls'' lsO Ks := by rw [hwc] at he; exact he
      have hσBβ : σB.InStratum β := hT.pb m i en hTe _ _ _ _ hB
      obtain ⟨ρb', hψσ, hXB'⟩ := compS_reassoc (ResU.CompS.comm hKs) hXB
      have hr' : r ∈ rsOf lsO := rec_kept hr hls'' hKs he'
      refine ih k' (by omega) lsO _ ρb' XB hXB' (inStratum_compS hψσ hψβ hσBβ) hr'
        (fun Bχ hBχ => ?_)
      obtain ⟨Xk, g, hXk, hXkg, hg⟩ :=
        rebReentry_split hψσ hBχ hχsplit hsplit hkw hnp hχimm
      have hwc' : en.wc ls'' lsO ρk := by rw [hwc]; exact extF_reb hkw hsplit hreb hKs he'
      have hc := (hcont lsO hwc').1 k' hk' w σB Xk hB hXk
      simp only [erwpC, show k' < n by omega, if_true] at hc
      exact erwp_garbage hXkg hg hc
    · -- the cancel obligation at the folded share: the borrowed continuation's, re-entered
      have he' : extF ls'' lsO Ks := by rw [hwc] at he; exact he
      have hr' : r ∈ rsOf lsO := rec_kept hr hls'' hKs he'
      have hqc : en.q = .cancel := by cases h : en.q <;> simp_all
      have hwc' : en.wc ls'' lsO ρk := by rw [hwc]; exact extF_reb hkw hsplit hreb hKs he'
      intro P hP
      rw [hfin m i en hTe hqc] at hP
      cases hP
      have hin := (hcont lsO hwc').2 hql _ (hfin m i en hTe hqc)
      refine erwp_reborrow_cancelRun r x hx hS hRβ hshape hβs hT₁ k lsO _ ψ Ks
        (ResU.CompS.comm hKs) hψβ hr' (fun Bχ hBχ => ?_)
      obtain ⟨Xk, g, hXk, hXkg, hg⟩ :=
        rebReentry_split (σB := PMap.empty) (ResU.comp_empty_right ψ) hBχ hχsplit hsplit hkw hnp
          hχimm
      obtain rfl := ResU.CompS.functional hXk (ResU.comp_empty_right ρk)
      exact erwp_garbage hXkg hg hin
  · obtain ⟨⟨-, -, hTe, ha⟩, -⟩ := pure_sep_iff.mp hp
    exact absurd ha (by rw [(hT.entry m i en hTe).1]; simp)

end BoCa.Fig16.LogRel.Core.Chain.SI

end
