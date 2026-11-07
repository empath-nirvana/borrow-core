import Core.Chain.SI.UbindGN

/-!
# An ordinary `raise` under a live `mut` lend

**Not a transcription.** `SI/StopCancelN.lean`'s shape at an ordinary `raise`. Inside a lend a
`raise` stops owning nothing but the borrow, which is garbage. The lender's resource at the
`raise`, with the borrow folded (6.27, as at every stop of `erwp_M_frame`), holds the lent cell
`ℓ ↦ own(w) ● σ`; `raiseStopN` admits only resource that owns nothing, so the lender's `raise`
carries the lend's claim (`claimR`) beside it: `opTableR T R` is `opTableN T` with the `raise`
carrying `R`. A finaliser frame around the lend consumes the claim at `[finalise]`
(`erwp_ubindRaise`): `ubind (N, D) K[raise p] ↦ D (); raise p`, `D` taking `R`.

* `erwp_M_frameR`: the Mut Frame across stops whose table may have abortive entries, the
  lender's raises at `opTableR T (claimR ℓ A F)`.
* `erwp_ubindRaise`: the finaliser frame around a body at `opTableR T R`.

Soundness: the lender's `raise` is the borrowed run's with the borrow folded, and the claim is
the resource 6.65 returns to the lender at a return, returned at the `raise` instead; at
`[finalise]` the finaliser consumes it before the `raise` goes on, owning nothing.

## Why unrestricted operations stay excluded

An unrestricted continuation's share owns nothing (`contShareN`, `q = unr → ρ = ∅`): it may be
resumed any number of times. The folded share holds `ℓ ↦ own(w)` (`unr_share_no_own`), so a stop
of an unrestricted operation under a live lend has no post-configuration. A continuation resumed
twice would lend `ℓ` twice; resumed never, it would leak `ℓ`. So the exclusion is inherent to
folding the lender's place into the continuation: a lend live across a stop needs a continuation
that runs at most once and whose discarding runs a cancel (`cancel`), or exactly once (`lin`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Head Kont performE raiseE cancelVal opPayload ubindE)

/-- A stop of an unrestricted operation owns nothing in its continuation's share: a share that
holds an `own` cell is not one. -/
theorem unr_share_no_own {en : OpEntN} {k : Nat} {ls : List SRec} {K : Kont} {Ψ : ContN}
    {ρ : WRes} (h : contShareN en k ls K Ψ ρ) (hq : en.q = .unr) {l : Loc} {w : Val} :
    ρ.get l ≠ some (CellU.ownOf w) := by
  rw [h.1 hq]; simp

/-! ### The table whose raises carry a claim -/

/-- An abortive stop carrying `R` beside what owns nothing. -/
def raiseStopR (T : OpTabN) (R : Nat → WProp) : TableN := fun k ls t _ =>
  ex fun (K : Kont) => ex fun (n : UInt32) => ex fun (i : UInt32) => ex fun (v : Val) =>
    ex fun (en : OpEntN) =>
      ⌜t = K.plug (raiseE (.val (opPayload n i v))) ∧ K.Catches n = false ∧
        T n i = some en ∧ en.abort = true⌝ ⋆
        (((fun ρ => en.PA k ls v ρ ∧ NoOwn ρ) ⋆ fun ρ => NoOwn ρ) ⋆ R k)

/-- `opTableN T` with the raises carrying `R`. -/
def opTableR (T : OpTabN) (R : Nat → WProp) : TableN := fun k ls t Ψ =>
  BoLo.or (performStopN T k ls t Ψ) (raiseStopR T R k ls t Ψ)

theorem opTableR_local (T : OpTabN) (R : Nat → WProp) : (opTableR T R).Local := by
  intro k ls t Ψ Ψ' ρ hΨ h
  rcases h with ⟨K, n, i, v, en, h⟩ | h
  · obtain ⟨hp, ρa, ρk, hc, hA, hu, hcont⟩ := pure_sep_iff.mp h
    refine Or.inl ⟨K, n, i, v, en, pure_sep_mk hp ⟨ρa, ρk, hc, hA, hu, fun ls' he =>
      ⟨fun k' hk w σ₁ σ₂ hB hcσ => hΨ k' hk _ _ _ ((hcont ls' he).1 k' hk w σ₁ σ₂ hB hcσ),
        (hcont ls' he).2⟩⟩⟩
  · exact Or.inr h

/-- **A table whose stops may be taken under a live `mut` lend at `A`, raises included.**
`OpTabN.LendOK` with abortive entries admitted; their payload, as every payload, outlives `A`. -/
structure OpTabN.LendOKR (T : OpTabN) (A : Life) : Prop where
  entry : ∀ m i en, T m i = some en → en.abort = false → en.q = .lin ∧ en.wc = extF
  pa : ∀ m i en, T m i = some en → ∀ k ls v (ρ : WRes), en.PA k ls v ρ → ρ.InStratum A
  pb : ∀ m i en, T m i = some en → ∀ k ls w (ρ : WRes), en.PB k ls w ρ → ρ.InStratum (↓A)

/-- **Mut Frame at `erwp` across stops, raises included.** As `erwp_M_frame`; at a `raise` the
borrow is folded and the cell is the claim the `raise` carries. -/
theorem erwp_M_frameR {Φ : LocFam} {l : Loc} {A : Life} {F : Nat → Val → SPropS Loc Val A}
    (hF : DownFam A F) {T : OpTabN} (hT : T.LendOKR A) {Q : PostN} :
    ∀ n j, n ≤ j → ∀ ls e (v : Val) (ρP ρlP ρb ρ : WRes) (houtP : ρP.InStratum A),
      ρb.InStratum (↓A) → ∀ (P : Val → SPropS Loc Val A),
      (∀ u r, SPropS.toU (P u) r → SPropS.toU (F j u) r) → ∀ (hwit : P v ⟨ρP, houtP⟩),
      ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP → ResU.CompS ρlP ρb ρ →
      (∀ BM, ResU.CompS ρb (ResU.single l (CellU.mutOf A v ρP houtP P hwit)) BM →
        erwp (ℍ := ℍ) (Φ.set l A F) (opTableN T) (MFPost l A F Q) n ls e BM) →
      erwp (ℍ := ℍ) Φ (opTableR T (claimR l A F)) Q n ls e ρ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro j hjn ls e v ρP ρlP ρb ρ houtP houtb P hPF hwit hclP hcρ hA
  rw [erwp_eq]
  refine rwpG_M_frameG hF hjn houtP houtb hPF hwit hclP hcρ ?_ (fun BM hBM => by
    have h := hA BM hBM
    rw [erwp_eq] at h
    exact h)
  intro k hk ls' t ρ' ρp X hQin hnoρp h9 hdX v'' χ hχ P'' hw'' hPk hsplit W'' hW'' Y hY
  have hkm'' : (CellU.mutOf A v'' χ hχ P'' hw'').kind ≠ Kind.imm := by
    rw [CellU.kind_mutOf]; exact fun c => Kind.noConfusion c
  have hXl : X.get l = some (CellU.mutOf A v'' χ hχ P'' hw'') :=
    (ResU.CompS.get_left_of_ne_imm (ResU.CompS.comm hsplit) (ResU.single_get_self _ _) hkm'').2
  rcases hQin with ⟨w, rfl, houtρ', hwand⟩ | ⟨K, m, i, v₀, en, hp⟩ | ⟨K, m, i, v₀, en, hp⟩
  · -- a return: 6.65's end
    rcases ResU.CompS.get_split_of_ne_imm h9 hXl hkm'' with ⟨hg, -⟩ | ⟨-, hgp⟩
    · exfalso
      have hcon := houtρ' l _ hg
      rw [CellU.inStratum_mutOf] at hcon
      exact absurd hcon (lt_irrefl _)
    have hpd := ResU.del_compS hgp
    obtain ⟨D, hD, hDm⟩ := (ResU.CompS.assoc ρ' (ρp.del l)
      (ResU.single l (CellU.mutOf A v'' χ hχ P'' hw'')) X).mp ⟨ρp, hpd, h9⟩
    obtain rfl : D = X.del l := compS_single_cancel hkm'' hDm hsplit
    obtain ⟨Z1, hZ1, hρ'Z1⟩ := (ResU.CompS.assoc ρ' (ρp.del l) W'' Y).mpr ⟨_, hD, hY⟩
    obtain ⟨R, hR, hRY⟩ :=
      (ResU.CompS.assoc ρ' W'' (ρp.del l) Y).mp ⟨Z1, ResU.CompS.comm hZ1, hρ'Z1⟩
    obtain ⟨y, hy₁, hy₂⟩ := (ResU.CompS.assoc ρ' (ResU.single l (CellU.ownOf v'')) χ R).mp
      ⟨W'', ResU.CompS.comm hW'', hR⟩
    exact ⟨R, ρp.del l, hRY, noOwn_del hnoρp l,
      Or.inl ⟨w, rfl, hwand v'' y hy₁ χ (hPk v'' χ ⟨hχ, hw''⟩) R hy₂⟩⟩
  · -- a stop: as in `erwp_M_frame`
    obtain ⟨⟨rfl, hK, hTe, ha⟩, ρa, ρk, hcak, hPA, -, hcont⟩ := pure_sep_iff.mp hp
    obtain ⟨hq, hwc⟩ := hT.entry m i en hTe ha
    have hρa := hT.pa m i en hTe _ _ _ _ hPA
    obtain ⟨Z, hZ, haZ⟩ := (ResU.CompS.assoc ρa ρk ρp X).mpr ⟨ρ', hcak, h9⟩
    rcases ResU.CompS.get_split_of_ne_imm haZ hXl hkm'' with ⟨hg, -⟩ | ⟨-, hZl⟩
    · exfalso
      have hcon := hρa l _ hg
      rw [CellU.inStratum_mutOf] at hcon
      exact absurd hcon (lt_irrefl _)
    have hZd := ResU.del_compS hZl
    obtain ⟨D, hD, hDm⟩ := (ResU.CompS.assoc ρa (Z.del l)
      (ResU.single l (CellU.mutOf A v'' χ hχ P'' hw'')) X).mp ⟨Z, hZd, haZ⟩
    obtain rfl : D = X.del l := compS_single_cancel hkm'' hDm hsplit
    obtain ⟨ρkL, hkL, haY⟩ := (ResU.CompS.assoc ρa (Z.del l) W'' Y).mpr ⟨_, hD, hY⟩
    have hdZd : (Z.del l).InStratum (↓A) :=
      ResU.CompS.inStratum_left hZd (ResU.CompS.inStratum_right haZ hdX)
    refine ⟨Y, PMap.empty, ResU.comp_empty_right _, noOwn_empty, Or.inr (Or.inl
      ⟨K, m, i, v₀, en, pure_sep_mk ⟨rfl, hK, hTe, ha⟩ ⟨ρa, ρkL, haY, hPA,
        fun hu' => absurd (hq.symm.trans hu') (by simp), fun ls'' he =>
          ⟨fun k' hk' w σB XB hB hXB => ?_, fun hq' => absurd hq hq'⟩⟩⟩)⟩
    simp only [erwpC, show k' < n by omega, if_true]
    obtain ⟨ρbB, hρbB, hWXB⟩ :=
      (ResU.CompS.assoc W'' (Z.del l) σB XB).mpr ⟨ρkL, ResU.CompS.comm hkL, hXB⟩
    have hdB : ρbB.InStratum (↓A) :=
      inStratum_compS hρbB hdZd (hT.pb m i en hTe _ _ _ _ hB)
    refine ih k' (by omega) k (le_of_lt hk') ls'' _ v'' χ W'' ρbB XB hχ hdB P'' hPk hw''
      (ResU.CompS.comm hW'') hWXB (fun BM' hBM' => ?_)
    have he' : en.wc ls' ls'' ρk := by rw [hwc] at he ⊢; exact extF_fold hZ hZl (CellU.kind_mutOf _ _ _ _ _ _) (CellU.wit_mutOf _ _ _ _ _ _) hW'' hkL he
    obtain ⟨s1, hs1, hZds1⟩ := (ResU.CompS.assoc (Z.del l) σB
      (ResU.single l (CellU.mutOf A v'' χ hχ P'' hw'')) BM').mpr ⟨ρbB, hρbB, hBM'⟩
    obtain ⟨Z', hZ', hZ'σ⟩ := (ResU.CompS.assoc (Z.del l)
      (ResU.single l (CellU.mutOf A v'' χ hχ P'' hw'')) σB BM').mp
        ⟨s1, ResU.CompS.comm hs1, hZds1⟩
    obtain rfl : Z = Z' := ResU.CompS.functional hZd hZ'
    obtain ⟨s2, hs2, hks2⟩ := (ResU.CompS.assoc ρk ρp σB BM').mpr ⟨Z, hZ, hZ'σ⟩
    obtain ⟨Xk, hXk, hXkp⟩ :=
      (ResU.CompS.assoc ρk σB ρp BM').mp ⟨s2, ResU.CompS.comm hs2, hks2⟩
    have hc := (hcont ls'' he').1 k' hk' w σB Xk hB hXk
    simp only [erwpC, show k' < n by omega, if_true] at hc
    exact erwp_garbage hXkp hnoρp hc
  · -- a `raise`: the borrow folded, the cell the claim the `raise` carries
    obtain ⟨⟨rfl, hK, hTe, ha⟩, τa, τn, hcan, ⟨hPA, hnA⟩, hnn⟩ := pure_sep_iff.mp hp
    have hρa := hT.pa m i en hTe _ _ _ _ hPA
    obtain ⟨Z, hZ, haZ⟩ := (ResU.CompS.assoc τa τn ρp X).mpr ⟨ρ', hcan, h9⟩
    rcases ResU.CompS.get_split_of_ne_imm haZ hXl hkm'' with ⟨hg, -⟩ | ⟨-, hZl⟩
    · exfalso
      have hcon := hρa l _ hg
      rw [CellU.inStratum_mutOf] at hcon
      exact absurd hcon (lt_irrefl _)
    have hZd := ResU.del_compS hZl
    obtain ⟨D, hD, hDm⟩ := (ResU.CompS.assoc τa (Z.del l)
      (ResU.single l (CellU.mutOf A v'' χ hχ P'' hw'')) X).mp ⟨Z, hZd, haZ⟩
    obtain rfl : D = X.del l := compS_single_cancel hkm'' hDm hsplit
    have hnoZ : NoOwn Z := noOwn_compS hZ hnn hnoρp
    obtain ⟨hs, hFk⟩ := hPk v'' χ ⟨hχ, hw''⟩
    exact ⟨Y, PMap.empty, ResU.comp_empty_right _, noOwn_empty, Or.inr (Or.inr
      ⟨K, m, i, v₀, en, pure_sep_mk ⟨rfl, hK, hTe, ha⟩ ⟨X.del l, W'', hY,
        ⟨τa, Z.del l, hD, ⟨hPA, hnA⟩, noOwn_del hnoZ l⟩,
        v'', χ, hs, hFk, ResU.CompS.comm hW''⟩⟩)⟩

/-! ### The finaliser frame that consumes the claim at `[finalise]` -/

/-- **The finaliser frame around a body whose raises carry `R`.** `[then]` at a return; a stop
(must-resume) passes the frame; at a `raise`, `[finalise]` runs `D ()`, which consumes `R` and
answers `()`, and the `raise` goes on owning nothing. -/
theorem erwp_ubindRaise {Φ : LocFam} (hΦ : Φ.Down) {T : OpTabN} (hTD : T.Down)
    (hTe : ∀ m i en, T m i = some en → en.abort = false → en.q = .lin)
    (hTr : ∀ m i en, T m i = some en → en.abort = true → m ≠ 0)
    (hPAls : ∀ m i en, T m i = some en → ∀ k ls ls' v ρ, (∀ x, x ∈ ls' ↔ x ∈ ls) →
      en.PA k ls v ρ → en.PA k ls' v ρ)
    {R : Nat → WProp} (N D : Val)
    (hD : ∀ k ls ρ, R k ρ → rwp (ℍ := ℍ) Φ (fun _ _ v ρ' => v = Val.unit ∧ ρ' = PMap.empty) k ls
      (.app (.val D) (.val .unit)) ρ)
    {Qin Qout : PostN} (hQout : Qout.Down)
    (hN : ∀ k ls (v : Val) ρ, Qin k ls v ρ →
      erwp (ℍ := ℍ) Φ (opTableN T) Qout k ls (.app (.val N) (.val v)) ρ) :
    ∀ n ls M ρ, erwp (ℍ := ℍ) Φ (opTableR T R) Qin n ls M ρ →
      erwp (ℍ := ℍ) Φ (opTableN T) Qout n ls (ubindE (.pair N D) M) ρ := by
  have hL := opTableR_local T R
  have hPD := erwpPost_down (opTableN_down hTD) hQout
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ls M ρ h
  rw [← ubK_plug, erwp_eq]
  refine rwpG_bind hΦ (ubK N D) ?_
  refine rwpG_mono_le (fun k hk ls' t σ ht => ?_) (erwp_unfold_at hL le_rfl h)
  rcases ht with ⟨v, rfl, hv⟩ | ⟨K₁, m, i, v, en, hp⟩ | ⟨K₁, m, i, v, en, hp⟩
  · -- `[then]`
    have hstep := fun μ => then_ret (ℍ := ℍ) μ N D v .hole
    simp only [Kont.plug_hole] at hstep
    exact rwpG_det hΦ (hPD _) hstep
      (erwp_unfold_at (opTableN_local T) hk (hN k ls' v σ hv))
  · -- a stop passes the frame
    obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρk, hcak, hA, hu, hcont⟩ := pure_sep_iff.mp hp
    have hKo : ((ubK N D).comp K₁).HasHnd m = false := by simp [hasHnd_comp, hK₁]
    have ht' : (ubK N D).plug (K₁.plug (performE (.val (opPayload m i v)))) =
        ((ubK N D).comp K₁).plug (opE false (opPayload m i v)) := by
      rw [Kont.plug_comp]; rfl
    rw [ht']
    refine rwpG_here (final_opPlug (payloadName_opPayload m i v) hKo) (Or.inr (Or.inl
      ⟨(ubK N D).comp K₁, m, i, v, en, pure_sep_mk ⟨rfl, hKo, hT, ha⟩
        ⟨ρa, ρk, hcak, hA, hu, fun ls'' he => ⟨fun k' hk' w τ₁ τ₂ hB hcτ => ?_,
          fun hql => absurd (hTe m i en hT ha) hql⟩⟩⟩))
    rw [Kont.plug_comp]
    have hc := (hcont ls'' he).1 k' hk' w τ₁ τ₂ hB hcτ
    simp only [erwpC, show k' < n by omega, if_true] at hc ⊢
    exact ih k' (by omega) _ _ _ hc
  · -- `[finalise]`: `D (); raise p`, `D` consuming the claim
    obtain ⟨⟨rfl, hK₁, hT, ha⟩, σ₁, ρR, hcσ, ⟨ρa, ρn, hcan, ⟨hPA, hnA⟩, hnn⟩, hR⟩ :=
      pure_sep_iff.mp hp
    have hm0 := hTr m i en hT ha
    refine rwpG_det hΦ (hPD _)
      (fun μ => (then_fin (ℍ := ℍ) (μ := μ) (i := i) N D v hm0 hK₁ .hole).1) ?_
    rw [Kont.plug_hole]
    refine rwpG_bind hΦ _ ?_
    have hDr := rwpG_frame
      (fun ls₀ τ => (∀ x, x ∈ ls₀ ↔ x ∈ ls') ∧
        ((fun ρ => en.PA k ls' v ρ ∧ NoOwn ρ) ⋆ (fun ρ => NoOwn ρ)) τ)
      (fun _ _ hs _ ⟨h₁, h₂⟩ => ⟨fun x => (hs x).trans (h₁ x), h₂⟩) (ResU.CompS.comm hcσ)
      (rwp_iff_rwpG.mp (hD k ls' ρR hR)) ⟨fun _ => Iff.rfl, ρa, ρn, hcan, ⟨hPA, hnA⟩, hnn⟩
    refine rwpG_mono_le (fun k₂ hk₂ ls₂ t₂ σ₂ ht₂ => ?_) hDr
    obtain ⟨σa, σb, hcσ', ⟨w, rfl, rfl, rfl⟩, hls₂, ⟨τa, τn, hcτ, ⟨hPAτ, hnτ⟩, hnn'⟩⟩ := ht₂
    obtain rfl := eq_of_compS_empty_left hcσ'
    refine rwpG_det hΦ (hPD _)
      (fun μ => (then_fin (ℍ := ℍ) (μ := μ) (i := i) N D v hm0 hK₁ .hole).2.2) ?_
    exact rwpG_here (final_opPlug (K := .hole) (r := true) (payloadName_opPayload m i v)
      (by simp [OpFree, Kont.Catches])) (Or.inr (Or.inr ⟨.hole, m, i, v, en,
        pure_sep_mk ⟨rfl, rfl, hT, ha⟩ ⟨τa, τn, hcτ, ⟨hTD.pa_le hT hk₂
          (hPAls _ _ _ hT _ _ _ _ _ hls₂ hPAτ), hnτ⟩, hnn'⟩⟩))

end BoCa.Fig16.LogRel.Core.Chain.SI

end
