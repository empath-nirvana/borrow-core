import DtorUnwind.SI.RebStopC

/-!
# `[TR]` 6.150 across stops, at `erwp`

**Not a transcription.** `erwp_reborrow` carries a reborrow across the stops of the borrowed
computation, as `erwp_I_frame` carries an `imm` lend. The image is the canonical one,
`canon r β` (`SI/TWNC.lean`), fixed with `β` at the first entry.

* **At a return:** `rwpG_rebG` with `ρₒ :=` the returned resource, `ρₖ := ∅`: 6.150's exit as
  printed. The returned resource is in `Res_β` by `[β]Q̂`.
* **At a stop (the fold):** `rwpG_rebG` with `ρₒ :=` the payload, `ρₖ :=` the continuation's share.
  6.52 splits the reborrow's exclusive part off the share and the garbage (`ψ`), and 6.59 gives
  the lender's `↭`. The lender stops with the payload and keeps `ψ ● ρᵢ` as its continuation's
  share: the record's cell and what the borrowed continuation held, without the image's views.
* **At the resume (the re-entry):** the lender is resumed with `σ_B` at a list with the members
  it stopped at (`sameW`), and re-enters by induction on the index at the **same** `β` and the
  same image `canon r β`. Whatever the handler did meanwhile, the image agrees with the resume
  world (`canon_escrowAgree`): this is the step `RebReentryAgreeN` asked for and
  `not_rebReentryAgreeN` refuted at `TWN`. The borrowed continuation is given `ψ ● σ_B ● χ`,
  which is its share and `σ_B` with the garbage and `χ`'s shared part (`imm` cells only) added.

## The conditions (`OpTabN.RebOK`)

As `OpTabN.LendOK`: every entry non-abortive, must-resume, resumed at the same world; what it
passes out (`PA`) and in (`PB`) in `Res_β`, the stratum 6.52 and 6.59 ask of `ρ″` and `ρ_b`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.DtorUnwind.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Kont performE raiseE opPayload)
open BoCa.Lifetime (LSub LifeVar)

/-- A resource of `imm` cells owns nothing. -/
theorem noOwn_of_imm {ρ : WRes} (h : ∀ m ψ, ρ.get m = some ψ → ψ.kind = Kind.imm) : NoOwn ρ := by
  classical
  refine PMap.ext fun x => ?_
  cases hgg : (ρ.restrict Kind.own).get x with
  | none => simp
  | some ψ =>
      exfalso
      obtain ⟨hdd, hk⟩ := ResU.restrict_eq_some.mp hgg
      rw [h x ψ hdd] at hk; cases hk

/-- **A table whose stops may be taken under a live reborrow at `β`.** -/
structure OpTabN.RebOK (T : OpTabN) (β : Life) : Prop where
  entry : ∀ m i en, T m i = some en → en.abort = false ∧ en.q = .lin ∧ en.wc = sameW
  pa : ∀ m i en, T m i = some en → ∀ k ls v (ρ : WRes), en.PA k ls v ρ → ρ.InStratum β
  pb : ∀ m i en, T m i = some en → ∀ k ls w (ρ : WRes), en.PB k ls w ρ → ρ.InStratum β

/-- The borrowed computation's postcondition, `[β]Q̂` as printed. -/
def RebPost (β : Life) (Q : PostN) : PostN := fun k ls w => box β (Q k ls w)

/-- **`[TR]` 6.150 at `erwp`, across stops**, at a lifetime `β` and the canonical image
`canon r β` the first entry chose. The lender holds the record's cell `ρᵢ` and `ρ_b ∈ Res_β`; the
caller's records are longer than `β`; the borrowed computation, handed `ρ_b ● canon r β`, is in
`erwp` with postcondition `[β]Q̂` and may stop at a `RebOK` table with the reborrow live. Then the
computation is in `erwp` at `Q̂`. -/
theorem erwp_reborrow {Φ : LocFam} (r : FrameRec) (x : LifeVar) (hx : ¬ VFree x r.T)
    {β : Life} {s : LSet} {hs : r.R.InStratum s.join} (hS : TmplSpec r (tmpl r))
    (hRβ : r.R.InStratum β)
    (hshape : vShape (r.T.immReborrow (.var x)) (r.δ.extend x β) r.v (canon r β))
    {Tb : OpTabN} (hT : Tb.RebOK β) {Q : PostN} :
    ∀ n ls e (ρb ρ : WRes),
      ResU.CompS (ResU.single r.le (CellU.immOf s r.v r.R hs)) ρb ρ → ρb.InStratum β →
      r ∈ rsOf ls → (∀ y ∈ ls, y.2 ⊐ β) →
      (∀ Bχ, ResU.CompS ρb (canon r β) Bχ →
        erwp (ℍ := ℍ) Φ (opTableN Tb) (RebPost β Q) n ls e Bχ) →
      erwp (ℍ := ℍ) Φ (opTableN Tb) Q n ls e ρ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ls e ρb ρ hc hb hr hβls hA
  set χ : WRes := canon r β with hχdef
  set ρi : WRes := ResU.single r.le (CellU.immOf s r.v r.R hs) with hρidef
  have hreb : ResU.Reb β r.R χ := canon_reb hS hRβ
  -- `χ = χ|imm ● χ|excl`, the first part `imm` cells only
  have hχsplit := ResU.restrictDom_split hreb
  have hχimm : NoOwn (χ.restrictDom (r.R.restrict Kind.imm)) :=
    noOwn_of_imm fun m ψ e => ResU.reb_imm_image hreb (ResU.restrictDom_get_inv e)
  rw [erwp_eq]
  refine rwpG_rebG r x hx hS hRβ hshape hc hb hr hβls ?_ (fun Bχ hBχ => by
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
    obtain ⟨-, hq, hwc⟩ := hT.entry m i en hTe
    refine ⟨ρa, ρk, hcak, hT.pa m i en hTe _ _ _ _ hPA, ?_⟩
    intro ρp w' ψ Yo Y hnp hkw hsubK hsplit hψβ hYo hY
    obtain ⟨Ks, hKs, haKs⟩ := compS_reassoc hYo hY
    refine ⟨Y, PMap.empty, ResU.comp_empty_right _, noOwn_empty, Or.inr (Or.inl
      ⟨K, m, i, v₀, en, pure_sep_mk ⟨rfl, hK, hTe, ha⟩ ⟨ρa, Ks, haKs, hPA,
        fun hu' => absurd (hq.symm.trans hu') (by simp), fun lsO he =>
          ⟨fun k' hk' w σB XB hB hXB => ?_, fun hq' => absurd hq hq'⟩⟩⟩)⟩
    simp only [erwpC, show k' < n by omega, if_true]
    have he' : ∀ y, y ∈ lsO ↔ y ∈ ls'' := by rw [hwc] at he; exact he
    have hσBβ : σB.InStratum β := hT.pb m i en hTe _ _ _ _ hB
    -- the lender's next segment: `ρᵢ ● (ψ ● σ_B)`
    obtain ⟨ρb', hψσ, hXB'⟩ := compS_reassoc (ResU.CompS.comm hKs) hXB
    have hb' : ρb'.InStratum β := inStratum_compS hψσ hψβ hσBβ
    have hmem : ∀ y, y ∈ lsO ↔ y ∈ ls := fun y => (he' y).trans (hls'' y)
    have hr' : r ∈ rsOf lsO := by
      obtain ⟨t', ht⟩ := mem_rsOf.mp hr; exact mem_rsOf.mpr ⟨t', (hmem _).mpr ht⟩
    refine ih k' (by omega) lsO _ ρb' XB hXB' hb' hr'
      (fun y hy => hβls y ((hmem y).mp hy)) (fun Bχ hBχ => ?_)
    -- the borrowed continuation at `ρₖ ● σ_B`, with the garbage `ρ⁺ ● χ|imm`
    obtain ⟨ψχ, hψχ, hψχσ⟩ := compS_exch hψσ hBχ
    obtain ⟨w₁, hw₁, hw₁χ⟩ := compS_reassoc' (ResU.CompS.comm hχsplit) hψχ
    obtain rfl : w₁ = w' := ResU.CompS.functional hw₁ hsplit
    obtain ⟨g, hg, hkg⟩ := compS_reassoc hkw hw₁χ
    obtain ⟨Xk, hXk, hXkg⟩ := compS_exch hkg hψχσ
    have hwc' : en.wc ls'' lsO ρk := by rw [hwc]; exact he'
    have hc := (hcont lsO hwc').1 k' hk' w σB Xk hB hXk
    simp only [erwpC, show k' < n by omega, if_true] at hc
    exact erwp_garbage hXkg (noOwn_compS hg hnp hχimm) hc
  · obtain ⟨⟨-, -, hTe, ha⟩, -⟩ := pure_sep_iff.mp hp
    exact absurd ha (by rw [(hT.entry m i en hTe).1]; simp)

end BoCa.Fig16.LogRel.Core.DtorUnwind.SI

end
