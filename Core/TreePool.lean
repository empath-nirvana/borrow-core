import Core.TreeResume

/-!
# A stored share beside another branch's run: the records it reads are kept  `[spec §62]`

**The guarantee.** A resource `ρ₂` framed beside a run of `e` (`twp_frame_keep`), where neither
holds anything of a lend of the other's records at the start (`NoneAt (recMask O₁) ρ₂`,
`NoneAt (recMask O₂) ρ₁`), ends beside the run with:

* every record of the start list `ls` that `ρ₂` reads (`RelFT`) re-read in the end list
  (`KeepRel`). The run may own records, open lends, and **end lends of its own that were open at
  the start**: a record `ρ₂` reads is in the lineage of a record proper (`TIT`'s closure); it is
  not the run's, because then `ρ₂` would hold part of the run's lend (`relFT_not_fdEsc`); so it is
  the frame's, and `EndT` re-reads the frame's records into the end's (`keep_frameRooted`);
* the separation kept both ways: the framed part holds nothing at the masks of the records the
  run ends with (the start's, re-read, where both sides are masked; `EndT`'s `MaskDiff` where the
  run opened or ended a record), and the run's end holds nothing at the framed records' masks
  (R1, `fdEsc_of_updX`).

So a stored continuation's share held beside the run stays resumable at the run's end list
(`contShareT_resume`, `KapSchedT`'s resume): its resume asks `KeepRel` and nothing about the
records it does not read. This is the step `twp_keepsKap` (`Core/TreeResume.lean`) took for a
runner owning no record; here the runner's own records are free, only kept apart from the share.

The carrier facts (`FrzT.flat`, `relFT_not_fdEsc`, `noneAt_recMask`, `fdEsc_of_noneAt`) are the
pool spike's (`experiments/PoolSpike`, not imported), re-proved here.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.Tree.Wp
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Kont)

/-! ### Frozen locations are in every flattening -/

theorem InDomT.cellAt {K : WCactus} {σ : TRes K} {m : BoCa.Loc} (h : InDomT σ m) :
    ∃ χ, CellAt σ m χ := by
  induction h with
  | top e => exact ⟨_, .top e⟩
  | wit e _ _ ih =>
      obtain ⟨χ, hχ⟩ := ih
      exact ⟨χ, .nest e hχ⟩

/-- A frozen location is an `imm` cell at depth, or beneath one. -/
theorem FrzT.immCell {K : WCactus} {ρ : TRes K} {m : BoCa.Loc} (h : FrzT ρ m) :
    ∃ (y : BoCa.Loc) (ψ₀ : TCell K), CellAt ρ y ψ₀ ∧ ψ₀.kind = Kind.imm ∧
      (m = y ∨ ∃ χ, CellAt ψ₀.wit m χ) := by
  induction h with
  | imm e k => exact ⟨_, _, .top e, k, .inl rfl⟩
  | inImm e k hd =>
      obtain ⟨χ, hχ⟩ := hd.cellAt
      exact ⟨_, _, .top e, k, .inr ⟨χ, hχ⟩⟩
  | inMut e _ _ ih =>
      obtain ⟨y, ψ₀, hc, hk, hm⟩ := ih
      exact ⟨y, ψ₀, .nest e hc, hk, hm⟩

/-- **A frozen location is in every flattening.** -/
theorem FrzT.flat {K : WCactus} {ρ : TRes K} {m : BoCa.Loc} (h : FrzT ρ m) {τ : TRes K}
    (hτ : ResUT.Flat ρ τ) : τ.get m ≠ none := by
  obtain ⟨y, ψ₀, hc, hk, hm⟩ := h.immCell
  obtain ⟨er, ar, -, har, hcr⟩ := hτ
  have : ∃ ζ, ar.get m = some ζ := by
    rcases hm with rfl | ⟨χ, hχ⟩
    · obtain ⟨ζ, e, -⟩ := cellAt_imm_icp hc har hk
      exact ⟨ζ, e⟩
    · exact cellAt_beneath_imm_ag hc hk hχ har
  obtain ⟨ζ, eζ⟩ := this
  obtain ⟨ξ, eξ⟩ := comp_some_r hcr eζ
  rw [eξ]; simp

/-- **A share that a record of `p`'s lineage is relevant to holds part of `p`'s lend.** -/
theorem relFT_not_fdEsc {K : WCactus} {p r : FrameRecT K} (hd : DescRT p r) {ρ : TRes K}
    (hrel : RelFT r ρ) (hv : ResUT.Valid ρ) (hpv : ResUT.Valid p.R) (hF : FdEsc p.le p.R ρ) :
    False := by
  obtain ⟨m, hf, hm⟩ := hrel
  obtain ⟨τ, hτ⟩ := hv
  have hne := hf.flat hτ
  rcases linLoc_of_relAt hd hm with rfl | hl
  · exact hne (hF τ hτ).1
  · obtain ⟨σR, eR, aR, heR, -, -⟩ := hpv
    exact hne ((hF τ hτ).2 eR heR m (hl.exDom.exST heR))

/-! ### `FdEsc` and the masks -/

theorem noneAt_recMask {K : WCactus} {O : List (FrameRecT K)} {ρ : TRes K}
    (hv : ∀ q ∈ O, ResUT.Valid q.R) (h : ∀ q ∈ O, FdEsc q.le q.R ρ) : NoneAt (recMask O) ρ := by
  rintro τ hτ x ⟨q, hq, hx⟩
  rcases hx with rfl | hx
  · exact (h q hq τ hτ).1
  · obtain ⟨σR, eR, aR, heR, -, -⟩ := hv q hq
    exact (h q hq τ hτ).2 eR heR x (hx.exST heR)

/-- `FdEsc` of a typed record proper read off the masks of a list holding it. -/
theorem fdEsc_of_noneAt {K : WCactus} {Θ : CodeTy} {tc : TChoice K} {W : TRes K}
    {ps rs : List (FrameRecT K)} (hT : TWNT K Θ tc W ps rs) {O : List (FrameRecT K)}
    {p : FrameRecT K} (hp : p ∈ O) (hpps : p ∈ ps) {ρ : TRes K} (h : NoneAt (recMask O) ρ) :
    FdEsc p.le p.R ρ := by
  have hTI := hT.inv
  have hprs : p ∈ rs := (hTI.2.2.2.2.2.2.1 p).mpr ⟨p, hpps, [], .nil p⟩
  intro τ hτ
  refine ⟨h τ hτ _ ⟨p, hp, .inl rfl⟩, fun eR heR x hxs => ?_⟩
  obtain ⟨ψx, eψx⟩ := Option.isSome_iff_exists.mp hxs
  obtain ⟨d, hd, ζ, eζ, kζ⟩ := exST_lineage Θ heR p rfl (hTI.1.2.2.2.1 p hprs) x ψx eψx
  exact h τ hτ x ⟨p, hp, .inr (LinLocT.exDom ⟨d, hd, ζ, eζ, kζ⟩)⟩

/-! ### The frame rule that keeps a stored share's records -/

/-- **A resource framed beside a run, apart from it, keeps the records it reads.** As
`twp_frame_w`; with the framed part `ρ₂` and the run's `ρ₁` holding nothing at each other's
record masks at the start (`hesc₁`, `hesc₂`), at every end the framed part is beside the run's
part with: the records of `ls` it reads re-read in the end list (`KeepRel`), and the two still
apart at the masks of the records each ends with. The run may open and end lends of its own,
those open at its start included. -/
theorem twp_frame_keep {F F₁ : TFrame} {P : TPost} {R : TRProp} (hR : R.Mono) {n : Nat}
    {w : TWd} {ls : List (SRecT w.K)} {O₁ O₂ : List (FrameRecT w.K)}
    (hO : ∀ p ∈ O₁, ∀ q ∈ O₂, p.le ≠ q.le) {e : Expr} {ρ₁ ρ₂ ρ : TRes w.K}
    (hcρ : ResUT.CompS ρ₁ ρ₂ ρ) (hcov : CovR (sem w.Θ) w.K ρ) (hv : ResUT.Valid ρ)
    (hesc₁ : NoneAt (recMask O₁) ρ₂) (hesc₂ : NoneAt (recMask O₂) ρ₁)
    (hF : ∀ (w₀ : TWd) (ρf ρ₁₀ ρ₂₀ y fρ : TRes w₀.K) (O₁₀ O₂₀ ps psF : List (FrameRecT w₀.K))
      (ls₀ : List (SRecT w₀.K)) (μ : Heap), w.Ext w₀ ρ₂ → RRw (w := w) (w' := w₀) ρ₂ ρ₂₀ →
      RecsRR w₀.Θ O₁ O₁₀ → RecsRR w₀.Θ O₂ O₂₀ → F w₀ ρf → ResUT.CompS ρf ρ₂₀ y →
      ResUT.CompS y ρ₁₀ fρ → SplitT ps (O₁₀ ++ O₂₀) psF →
      (∀ p ∈ O₁₀, ∀ q ∈ O₂₀, p.le ≠ q.le) → RecInv w₀ fρ ps ls₀ → WInv w₀ fρ μ → F₁ w₀ y)
    (hwp : twp (ℍ := ℍ) F₁ P n w ls O₁ e ρ₁) (hR₂ : R w O₂ ρ₂) :
    twp (ℍ := ℍ) F (fun k w' ls' O' t ρ' => ∃ (O₁' O₂' : List (FrameRecT w'.K)) (a b : TRes w'.K),
      O' = O₁' ++ O₂' ∧ ResUT.CompS a b ρ' ∧ P k w' ls' O₁' t a ∧ R w' O₂' b ∧
        KeepRel w'.Θ ls ls' ρ₂ ∧ NoneAt (recMask O₁') b ∧ NoneAt (recMask O₂') a)
      n w ls (O₁ ++ O₂) e ρ := by
  intro w₀ ρ₀ ρf fρ ls₀ O₀ ps psF μ hE hr hl hOr hFρ hf hc hS hRi hI hfd j μ' e' hj hrun hfin
  obtain ⟨O₁₀, O₂₀, rfl, hO₁, hO₂⟩ := forall₂_append_left hOr
  have hO₀ : ∀ p ∈ O₁₀, ∀ q ∈ O₂₀, p.le ≠ q.le := by
    intro p hp q hq
    obtain ⟨p₁, hp₁, r₁⟩ := forall₂_mem_right hO₁ hp
    obtain ⟨q₂, hq₂, r₂⟩ := forall₂_mem_right hO₂ hq
    rw [r₁.1, r₂.1]
    exact hO p₁ hp₁ q₂ hq₂
  obtain ⟨ρ₁₀, ρ₂₀, h₁₀, h₂₀, hc₀⟩ := RR.split_retype hE.1 hcρ hcov hE.2 hr
  have hE₁ := hE.of_compS_left hcρ
  have hE₂ := hE.of_compS_right hcρ
  obtain ⟨y, hy, hyf⟩ := reassoc_out hc hc₀
  have hS₁ : SplitT ps O₁₀ (O₂₀ ++ psF) := by
    refine ⟨fun p => ?_, fun p hp q hq => ?_⟩
    · rw [hS.1 p, List.mem_append, List.mem_append]; tauto
    · rcases List.mem_append.mp hq with h | h
      · exact hO₀ p hp q h
      · exact hS.2 p (List.mem_append_left _ hp) q h
  obtain ⟨w', y', ρ₁', fρ', psF'', ps', O₁', ls', g₀, g₁, g₂, g₃, g₄, g₅, g₆, g₇, g₈, g₉, g₁₀,
      g₁₁⟩ :=
    hwp w₀ ρ₁₀ y fρ ls₀ O₁₀ ps (O₂₀ ++ psF) μ hE₁ h₁₀ hl hO₁
      (hF w₀ ρf ρ₁₀ ρ₂₀ y fρ O₁₀ O₂₀ ps psF ls₀ μ hE₂ h₂₀ hO₁ hO₂ hFρ hy hyf hS hO₀ hRi hI)
      (hash_of_inv hyf hI) hyf hS₁ hRi hI hfd j μ' e' hj hrun hfin
  obtain ⟨O₂', psF', rfl, hO₂', hpsF'⟩ := forall₂_append_left g₂
  obtain ⟨ρf', ρ₂', hf', h₂', hy'⟩ :=
    RR.split_retype g₀.1 hy (covf_of_comp hyf hI) g₀.2 g₁
  obtain ⟨ρ', hρ', hfρ'⟩ := reassoc_in hy' g₄
  have hR₂₀ : R w₀ O₂₀ ρ₂₀ := hR _ _ _ _ _ _ hE₂ h₂₀ hO₂ hR₂
  have hvy' : ResUT.Valid y' := (ResUT.Valid.split g₄ g₇.valid).1
  have hu : UpdX (sem w'.Θ) (recMask O₁₀) (recMask O₁') ρ₀ ρ' :=
    UpdX.frame g₀.1 g₉ h₂' hc₀ hρ' (cov_valid hc hI) (cov_valid hfρ' g₇)
      (g₁₀.of_compS_right hy' hvy')
  have hmask : ∀ x, MaskDiff (recMask (O₁₀ ++ O₂₀)) (recMask (O₁' ++ O₂')) x →
      MaskDiff (recMask O₁₀) (recMask O₁') x := fun x hx => by
    unfold MaskDiff at hx ⊢
    rw [recMask_append, recMask_append, ← recMask_rr hO₂' x] at hx
    tauto
  -- validity of the parts, at `w` and at `w₀`
  have hv₁ : ResUT.Valid ρ₁ := (ResUT.Valid.split hcρ hv).1
  have hv₂ : ResUT.Valid ρ₂ := (ResUT.Valid.split hcρ hv).2
  have hvy : ResUT.Valid y := (ResUT.Valid.split hyf hI.valid).1
  have hv₂₀ : ResUT.Valid ρ₂₀ := (ResUT.Valid.split hy hvy).2
  have hv₁₀ : ResUT.Valid ρ₁₀ := (ResUT.Valid.split hyf hI.valid).2
  have hvesc : ∀ p ∈ ps, ResUT.Valid p.R := TWNT.esc_valid hRi.1
  -- the separation at `w₀`
  have hesc₁₀ : NoneAt (recMask O₁₀) ρ₂₀ :=
    (hesc₁.rr hE.1 hv₂ h₂₀).mono fun x hx => (recMask_rr hO₁ x).mpr hx
  have hesc₂₀ : NoneAt (recMask O₂₀) ρ₁₀ :=
    (hesc₂.rr hE.1 hv₁ h₁₀).mono fun x hx => (recMask_rr hO₂ x).mpr hx
  -- **the records the framed part reads are kept**
  have hkeep : KeepRel w'.Θ ls ls' ρ₂ := by
    intro r hr₀ hrel
    obtain ⟨r₀, hr₀', e₀⟩ := hl.mem_fwd hr₀
    have hrel₀ : RelFT r₀ ρ₂₀ := (RelFT.rr_iff e₀ h₂₀).mp hrel
    obtain ⟨p₁, hp₁, hd⟩ := (hRi.1.inv.2.2.2.2.2.2.1 r₀).mp hr₀'
    rcases (hS₁.1 p₁).mp hp₁ with hp₁O | hp₁F
    · exact (relFT_not_fdEsc hd hrel₀ hv₂₀ (hvesc p₁ hp₁)
        (fdEsc_of_noneAt hRi.1 hp₁O hp₁ hesc₁₀)).elim
    · obtain ⟨r', hr', e'⟩ := keep_frameRooted g₂ g₅ g₆.1 ⟨p₁, hp₁F, hd⟩
      exact ⟨r', hr', RecRR.trans g₀.1 e₀ e'⟩
  -- **the framed part avoids the masks of the records the run ends with**
  have hb : NoneAt (recMask O₁') ρ₂' := by
    intro τ hτ x hx
    by_cases hx₀ : recMask O₁₀ x
    · exact (hesc₁₀.rr g₀.1 hv₂₀ h₂') τ hτ x hx₀
    · exact (g₁₀.of_compS_right hy' hvy') τ hτ x (Or.inr ⟨hx, hx₀⟩)
  -- **the run's end avoids the masks of the framed records** (R1)
  have ha : NoneAt (recMask O₂') ρ₁' := by
    refine noneAt_recMask (fun q hq => TWNT.esc_valid g₆.1 q (g₅.right q
      (List.mem_append_left _ hq))) fun q' hq' => ?_
    obtain ⟨q, hq, hqq⟩ := forall₂_mem_right hO₂' hq'
    have hq₀ : q ∈ ps := (hS.1 q).mpr (Or.inl (List.mem_append_right _ hq))
    exact fdEsc_of_updX g₀.1 (hvesc q hq₀) (fdEsc_of_noneAt hRi.1 hq hq₀ hesc₂₀) g₆.1 g₄ g₅
      (List.mem_append_left _ hq') hqq g₉
  refine ⟨w', ρf', ρ', fρ', psF', ps', O₁' ++ O₂', ls', g₀.of_compS_left hy, hf', hpsF',
    ResUT.hash_symm (hash_of_inv hfρ' g₇), hfρ', ⟨fun p => ?_, fun p hp q hq => ?_⟩, g₆, g₇,
    ⟨O₁', O₂', ρ₁', ρ₂', rfl, hρ', g₈, hR _ _ _ _ _ _ (g₀.of_compS_right hy) h₂' hO₂' hR₂₀,
      hkeep, hb, ha⟩,
    (hu.widen (recMask O₂₀)).congr (fun l => recMask_append l)
      (fun l => by rw [recMask_append, recMask_rr hO₂' l]),
    (g₁₀.of_compS_left hy' hvy').mono hmask,
    (g₁₁.mono fun l h => (recMask_append l).mpr (Or.inl h)).frame hc₀ (TWNT.mutOne hRi.1)
      (fun _ _ h k => (h.of_compS_right hc₀ (kind_mut_ne_imm k)).of_compS_right hc
        (kind_mut_ne_imm k))
      (AgreeOn.of_compS_right hy g₀.2)⟩
  · rw [g₅.1 p, List.mem_append, List.mem_append]; tauto
  · rcases List.mem_append.mp hp with h | h
    · exact g₅.2 p h q (List.mem_append_right _ hq)
    · obtain ⟨p₀, hp₀, r₀⟩ := forall₂_mem_right hO₂' h
      obtain ⟨q₀, hq₀, s₀⟩ := forall₂_mem_right hpsF' hq
      rw [r₀.1, s₀.1]
      exact hS.2 p₀ (List.mem_append_right _ hp₀) q₀ hq₀

/-! ### A stored continuation beside another branch's run -/

/-- **Another branch's run keeps a stored continuation resumable, the runner owning and ending
lends of its own.** `κ` is held at `w` (`KapAtT`, its share `ρκ` and records `Oκ`) beside a run of
`e` from `ρ₁` owning `Or`; the two hold nothing at each other's record masks. At every end of the
run, at the world `w′` and list `ls′` it ends in, `κ` is held there (`KapAtT.resume` resumes it),
and the two are still apart at the masks of the records each ends with. Nothing is asked of the
records of `κ`'s stop list beyond what `KapAtT` carries: the runner may end any record of its own,
those open at `κ`'s stop included. -/
theorem twp_keepsKap_sep {Qout : TPostV} {M : BoCa.Loc → Prop} {en : OpEntT} {k : Nat}
    {v κ : Val} {F F₁ : TFrame} {P : TPost} {n : Nat} {w : TWd} {ls : List (SRecT w.K)}
    {Or Oκ : List (FrameRecT w.K)} {e : Expr} {ρ₁ ρκ ρ : TRes w.K}
    (hcρ : ResUT.CompS ρ₁ ρκ ρ) (hcov : CovR (sem w.Θ) w.K ρ) (hv : ResUT.Valid ρ)
    (hOκ : ∀ p ∈ Or, ∀ q ∈ Oκ, p.le ≠ q.le)
    (hesc₁ : NoneAt (recMask Or) ρκ) (hesc₂ : NoneAt (recMask Oκ) ρ₁)
    (hF : ∀ (w₀ : TWd) (ρf ρ₁₀ ρ₂₀ y fρ : TRes w₀.K) (O₁₀ O₂₀ ps psF : List (FrameRecT w₀.K))
      (ls₀ : List (SRecT w₀.K)) (μ : Heap), w.Ext w₀ ρκ → RRw (w := w) (w' := w₀) ρκ ρ₂₀ →
      RecsRR w₀.Θ Or O₁₀ → RecsRR w₀.Θ Oκ O₂₀ → F w₀ ρf → ResUT.CompS ρf ρ₂₀ y →
      ResUT.CompS y ρ₁₀ fρ → SplitT ps (O₁₀ ++ O₂₀) psF →
      (∀ p ∈ O₁₀, ∀ q ∈ O₂₀, p.le ≠ q.le) → RecInv w₀ fρ ps ls₀ → WInv w₀ fρ μ → F₁ w₀ y)
    (hwp : twp (ℍ := ℍ) F₁ P n w ls Or e ρ₁) (hκ : KapAtT (ℍ := ℍ) Qout M en k v κ w ls Oκ ρκ) :
    twp (ℍ := ℍ) F (fun k₁ w' ls' O' t ρ' => ∃ (Oa Ob : List (FrameRecT w'.K)) (a b : TRes w'.K),
      O' = Oa ++ Ob ∧ ResUT.CompS a b ρ' ∧ P k₁ w' ls' Oa t a ∧
        KapAtT (ℍ := ℍ) Qout M en k v κ w' ls' Ob b ∧ NoneAt (recMask Oa) b ∧
        NoneAt (recMask Ob) a) n w ls (Or ++ Oκ) e ρ := by
  let R : TRProp := fun w' O ρ' => w.Ext w' ρκ ∧ RRw (w := w) (w' := w') ρκ ρ' ∧ RecsRR w'.Θ Oκ O
  have hRm : R.Mono := fun _ _ _ _ _ _ hE hr hO ⟨a, b, c⟩ =>
    ⟨a.trans b hE, RRw.trans hE.1 b hr, c.trans hE.1 hO⟩
  have hcovκ : CovR (sem w.Θ) w.K ρκ := CovR.of_compS_left (ResUT.CompS.comm hcρ) hcov
  have hOκc : ∀ r ∈ Oκ, CovR (sem w.Θ) w.K r.R := by
    obtain ⟨w₁, ls₁, O₁, ρ₁', hK, hE₁, hr₁, hO₁, -⟩ := hκ
    intro r hr
    obtain ⟨r₁, -, hrr⟩ := forall₂_mem_right hO₁ hr
    exact hrr.2.2.2.cov
  have h := twp_frame_keep (R := R) hRm hOκ hcρ hcov hv hesc₁ hesc₂ hF hwp
    ⟨TWd.Ext.refl _ _, RR.refl hcovκ, RecsRR.refl hOκc⟩
  refine twp_mono (fun k₁ w' ls' O' t ρ' hp => ?_) h
  obtain ⟨Oa, Ob, a, b, hO', hc, hP, ⟨hEb, hrb, hOb⟩, hkeep, hb, ha⟩ := hp
  exact ⟨Oa, Ob, a, b, hO', hc, hP, hκ.kripke hEb hrb hOb hkeep, hb, ha⟩

/-- **One stored task resumed beside another, the other kept resumable.** The scheduler holds
`κB` and `κA` (`KapAtT` at the present world and list). It resumes `κB` at an answer its entry
accepts, under frames avoiding `κB`'s mask history `MB`, with `κA`'s share beside it. At every end
of `κB`'s run, `κA` is held at the end world and list, and the two are apart at the masks of the
records each ends with. The premises are separation: `κA`'s share holds nothing at `MB` (which
holds `κB`'s records' masks), and `κB`'s resumed resource holds nothing at `κA`'s records' masks.
`κB`'s run may end any lend of its own, those open when `κA` stopped included. -/
theorem kapAtT_resume_keep {QB QA : TPostV} {MB MA : BoCa.Loc → Prop} {enB enA : OpEntT}
    {kB kA : Nat} {vB vA κB κA : Val} {w : TWd} {ls : List (SRecT w.K)}
    {OB OA : List (FrameRecT w.K)} {ρB ρA σ σ' ρ : TRes w.K}
    (hκB : KapAtT (ℍ := ℍ) QB MB enB kB vB κB w ls OB ρB)
    (hκA : KapAtT (ℍ := ℍ) QA MA enA kA vA κA w ls OA ρA) {F : TFrame}
    (hFM : ∀ w' ρf, F w' ρf → fdMask MB w' ρf) {k' : Nat} (hk' : k' < kB) {a : Val}
    (hPB : enB.PBv vB k' w ls a σ) (hcσ : ResUT.CompS ρB σ σ') (hcρ : ResUT.CompS σ' ρA ρ)
    (hcov : CovR (sem w.Θ) w.K ρ) (hv : ResUT.Valid ρ) (hap : ∀ p ∈ OB, ∀ q ∈ OA, p.le ≠ q.le)
    (hMA : NoneAt MB ρA) (hOBM : ∀ x, recMask OB x → MB x) (hesc₂ : NoneAt (recMask OA) σ') :
    twp (ℍ := ℍ) F (fun k₁ w' ls' O' t ρ' => ∃ (Oa Ob : List (FrameRecT w'.K)) (a b : TRes w'.K),
      O' = Oa ++ Ob ∧ ResUT.CompS a b ρ' ∧ valPost QB k₁ w' ls' Oa t a ∧
        KapAtT (ℍ := ℍ) QA MA enA kA vA κA w' ls' Ob b ∧ NoneAt (recMask Oa) b ∧
        NoneAt (recMask Ob) a) k' w ls (OB ++ OA)
      (.app (.app κB.1 (.val (Val.inj₁ .unit))) (.val a)) ρ := by
  have h := cerwpTE_iff.mp (hκB.resume hk' hPB hcσ (fdMask_mono MB) (fun _ _ h => h))
  have hvA : ResUT.Valid ρA := (ResUT.Valid.split hcρ hv).2
  refine twp_keepsKap_sep hcρ hcov hv hap (hMA.mono hOBM) hesc₂ ?_ h hκA
  intro w₀ ρf ρ₁₀ ρ₂₀ y fρ O₁₀ O₂₀ ps psF ls₀ μ hE h₂₀ _ _ hFρ hy hyf _ _ _ hI
  have hvy : ResUT.Valid y := (ResUT.Valid.split hyf hI.valid).1
  have hvf := ResUT.Valid.split hy hvy
  exact ⟨hvy, NoneAt.compS hy hvf.1 hvf.2 (hFM w₀ ρf hFρ).2 (NoneAt.rr hE.1 hvA h₂₀ hMA)⟩

end BoCa.Fig16.Tree.Wp

end
