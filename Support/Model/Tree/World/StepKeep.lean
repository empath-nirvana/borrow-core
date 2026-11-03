import Support.Model.Tree.World.EscBeneath

/-!
# What `↭` keeps of a lend a run holds nothing of

`[spec §62]`. A run beside a record proper `p` of its frame, holding nothing at `p`'s lent location
or escrow (`FdEsc`), still holds nothing there at its end, when its start `ρ` and end `ρ′` are
related by `UpdX` masked at the run's own records (`fdEsc_of_updX`). It is read from three things.

* **`↭` at the locations `FdEsc` reads.** `p′`'s lent location and lineage locations are none of
  them (`recMask_apart`): two records proper have different locations (`SplitT`), their lineages
  share no exclusive cell (`ExclUniqueT`, `desc_comparable`), and neither is a sub-record of the
  other, which would put a `mut` cell at a lent location (`NoMutT`). So an `imm` or `mut` cell of
  `⦇ρ′⦈` there is one of `⦇ρ⦈`, which holds nothing there.
* **An `own` cell of the exclusive walk** meets the world's view of the record (`LeInvT`,
  `le_view_cellAt`), which `✓` refuses (`ex_ag_disjoint`).
* **An `own` cell of the aliasable walk** sits at the lent location beneath a borrow, which
  `NoOwnUnderT` refuses, or at a lineage location beneath an innermost view at `p′`'s location or
  a lineage location of `p′` (`innermost_view`). That view is an `imm` cell of `⦇ρ′⦈` at a location
  `FdEsc` reads, so it is accounted for by `↭`, as the cell beneath it: `[TR]` 6.48's account of a
  cell of the aliasable walk by its `imm` ancestor.

The lineage facts read the escrow's exclusive walk off its cells (`ExDom`), and a record's escrow
is valid (`TWNT.esc_valid`), so `ex(p.R)` is defined and its domain is `ExDom p.R`.
-/

noncomputable section

namespace BoCa.Fig16.Tree.Wp
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree

variable {K : WCactus}

/-! ### Escrows -/

/-- **The escrow of a record proper is valid.** -/
theorem TWNT.esc_valid {Θ : CodeTy} {tc : TChoice K} {W : TRes K} {ps rs : List (FrameRecT K)}
    (h : TWNT K Θ tc W ps rs) : ∀ r ∈ ps, ResUT.Valid r.R := by
  induction h with
  | empty => intro r hr; simp at hr
  | alloc _ _ _ _ _ ih => exact ih
  | @immFrame K Θ tc W X Z R W' ps rs ds l v α T hα hW₀ hX hW hden hW' hv hds ih =>
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · exact (ResUT.Valid.split hX (ResUT.Valid.split hW hW₀.valid).1).2
      · exact ih r hr
  | reb _ _ _ _ _ _ _ _ _ _ ih => exact ih
  | rebDeep _ _ _ _ _ _ _ _ _ _ _ _ ih => exact ih
  | mutFold _ _ _ _ _ ih => exact ih
  | mutUnfold _ _ _ _ _ ih => exact ih
  | free _ _ _ ih => exact ih
  | store _ _ _ _ ih => exact ih
  | immEnd r _ _ _ _ _ _ hps _ ih => intro r' hr'; exact ih r' ((hps r').mp hr').1
  | rebEnd _ _ _ _ _ _ _ ih => exact ih
  | rebEndDeep _ _ _ _ _ _ _ _ ih => exact ih
  | reread _ _ _ _ hps _ _ ih =>
      intro r' hr'
      obtain ⟨r, hr, hrr⟩ := forall₂_mem_right hps hr'
      exact WitRel.ResUT.Valid.sim (W := rrRel _ _ _) (ih r hr) hrr.2.2.2.rsim

/-- **`ExDom` is in the domain of `ex(ρ)_●`.** -/
theorem ExDom.exST {ρ : TRes K} {x : BoCa.Loc} (h : ExDom ρ x) :
    ∀ {e : TRes K}, ExST ρ e → (e.get x).isSome := by
  induction h with
  | top e hk =>
      intro ex hex
      rw [ExST.get_of_ne_imm hex e hk]; rfl
  | deep e hk _ ih =>
      intro ex hex
      obtain ⟨ev, z, hev, hz⟩ := ExWT.wit_le hSS ResUT.compLawsS hex e hk
      obtain ⟨ζ, hζ⟩ := Option.isSome_iff_exists.mp (ih hev)
      obtain ⟨ζ', hζ'⟩ := comp_some hz hζ
      rw [hζ']; rfl

/-- A lineage location is a location of the escrow's exclusive part. -/
theorem LinPathT.exDom {r d : FrameRecT K} {q : List BoCa.Loc} (h : LinPathT r q d)
    {x : BoCa.Loc} (hx : ExDom d.R x) : ExDom r.R x := by
  induction h with
  | nil => exact hx
  | cons hs _ ih =>
      obtain ⟨-, ζ, eζ, kζ, -, wζ⟩ := hs
      exact .deep eζ kζ (wζ ▸ ih hx)

theorem LinLocT.exDom {p : FrameRecT K} {x : BoCa.Loc} (h : LinLocT p x) : ExDom p.R x := by
  obtain ⟨d, ⟨q, hq⟩, ζ, eζ, kζ⟩ := h
  exact hq.exDom (.top eζ kζ)

/-- **A location of a typed escrow's exclusive part is a lineage location.** -/
theorem ExDom.linLoc (Θ : CodeTy) {ρ : TRes K} {x : BoCa.Loc} (h : ExDom ρ x) :
    ∀ r : FrameRecT K, r.R = ρ → (r.T.interp Θ).P K r.v r.R → LinLocT r x := by
  induction h with
  | top e hk =>
      intro r hr _
      exact ⟨r, DescRT.refl r, _, hr ▸ e, hk⟩
  | @deep ρ x y ψ e hk _ ih =>
      intro r hr hty
      obtain ⟨S, g, hS⟩ := mut_gposT Θ r.T hty (hr ▸ e) hk
      let d₀ : FrameRecT K := ⟨y, ψ.erase, ψ.wit, S⟩
      have hsub : SubRecT r d₀ := ⟨g, ψ, hr ▸ e, hk, rfl, rfl⟩
      obtain ⟨d, ⟨pa, hpa⟩, hd⟩ := ih d₀ rfl hS
      exact ⟨d, ⟨_, .cons hsub hpa⟩, hd⟩

/-! ### Records proper are apart -/

/-- A record proper is no proper sub-record: its location would hold a `mut` cell at depth. -/
theorem not_desc_proper {Θ : CodeTy} {tc : TChoice K} {W : TRes K}
    {ps rs : List (FrameRecT K)} (hT : TWNT K Θ tc W ps rs) {p : FrameRecT K} (hp : p ∈ ps)
    {r : FrameRecT K} (hr : r ∈ rs) (hd : DescT r p) : False := by
  have hTI := hT.inv
  obtain ⟨q', hq', hpath⟩ := hd
  obtain ⟨r', hr', hsub⟩ := hpath.last hq'
  obtain ⟨-, ζr, eζr, kζr, -⟩ := hsub
  exact hTI.2.2.2.2.2.1.1 p hp
    ((hTI.recs_cellAt hT.valid (hTI.desc_closed r hr r' hr') _ _ eζr).mutAt kζr)

/-- **Two records proper at different locations share no lineage location.** -/
theorem linLoc_apart {Θ : CodeTy} {tc : TChoice K} {W : TRes K} {ps rs : List (FrameRecT K)}
    (hT : TWNT K Θ tc W ps rs) {p q : FrameRecT K} (hp : p ∈ ps) (hq : q ∈ ps)
    (hne : p.le ≠ q.le) {x : BoCa.Loc} (h₁ : LinLocT p x) (h₂ : LinLocT q x) : False := by
  have hTI := hT.inv
  have hU := hT.exclUnique
  have hcl := hTI.desc_closed
  have hprs : p ∈ rs := (hTI.2.2.2.2.2.2.1 p).mpr ⟨p, hp, [], .nil p⟩
  have hqrs : q ∈ rs := (hTI.2.2.2.2.2.2.1 q).mpr ⟨q, hq, [], .nil q⟩
  obtain ⟨d₁, ⟨pa, hpa⟩, ζ₁, e₁, k₁⟩ := h₁
  obtain ⟨d₂, ⟨pb, hpb⟩, ζ₂, e₂, k₂⟩ := h₂
  obtain rfl := hU d₁ (hcl p hprs d₁ ⟨pa, hpa⟩) d₂ (hcl q hqrs d₂ ⟨pb, hpb⟩) x ζ₁ ζ₂ e₁ k₁ e₂ k₂
  rcases desc_comparable hU hcl _ p q d₁ pa pb le_rfl hprs hqrs hpa hpb with h | h
  · rcases h.cases with rfl | h
    · exact hne rfl
    · exact not_desc_proper hT hp hqrs h
  · rcases h.cases with rfl | h
    · exact hne rfl
    · exact not_desc_proper hT hq hprs h

/-- **A lent location is no lineage location of another record proper.** -/
theorem le_not_linLoc {Θ : CodeTy} {tc : TChoice K} {W : TRes K} {ps rs : List (FrameRecT K)}
    (hT : TWNT K Θ tc W ps rs) {p q : FrameRecT K} (hp : p ∈ ps) (hq : q ∈ ps)
    (h : LinLocT p q.le) : False := by
  have hTI := hT.inv
  have hcl := hTI.desc_closed
  have hprs : p ∈ rs := (hTI.2.2.2.2.2.2.1 p).mpr ⟨p, hp, [], .nil p⟩
  have hqrs : q ∈ rs := (hTI.2.2.2.2.2.2.1 q).mpr ⟨q, hq, [], .nil q⟩
  obtain ⟨d, hd, ζ, eζ, kζ⟩ := h
  have hdrs := hcl p hprs d hd
  cases hk : ζ.kind with
  | imm => exact kζ hk
  | own =>
      cases ζ with
      | own u => exact hTI.2.2.2.1 q hqrs d hdrs u eζ
      | imm => cases hk
      | «mut» => cases hk
  | «mut» =>
      exact hTI.2.2.2.2.2.1.1 q hq ((hTI.recs_cellAt hT.valid hdrs _ _ eζ).mutAt hk)

/-- **The locations `FdEsc` reads of a record proper are masked by no other record proper.** -/
theorem recMask_apart {Θ : CodeTy} {tc : TChoice K} {W : TRes K} {ps rs : List (FrameRecT K)}
    (hT : TWNT K Θ tc W ps rs) {p q : FrameRecT K} (hp : p ∈ ps) (hq : q ∈ ps)
    (hne : p.le ≠ q.le) {x : BoCa.Loc} (hx : x = p.le ∨ LinLocT p x) :
    ¬ (x = q.le ∨ ExDom q.R x) := by
  have hTI := hT.inv
  have hqrs : q ∈ rs := (hTI.2.2.2.2.2.2.1 q).mpr ⟨q, hq, [], .nil q⟩
  rintro (rfl | hd)
  · rcases hx with h | h
    · exact hne h.symm
    · exact le_not_linLoc hT hp hq h
  · have hl := hd.linLoc Θ q rfl (hTI.1.2.2.2.1 q hqrs)
    rcases hx with rfl | h
    · exact le_not_linLoc hT hq hp hl
    · exact linLoc_apart hT hp hq hne h hl

/-! ### The frame condition along `↭` -/

/-- **`FdEsc` along `↭`.** A run from `ρ` holding nothing at the lent location and escrow of a
record proper `p` of its frame, ending at `ρ′` beside the re-read frame in a world of the typed
world, `↭`-related to `ρ` across the re-reading and masked at its own records, holds nothing there
either. -/
theorem fdEsc_of_updX {w w' : TWd} (_hE : w.K.Ext w'.K) {ρ : TRes w.K} {O : List (FrameRecT w.K)}
    {p : FrameRecT w.K} (hpv : ResUT.Valid p.R) (h₀ : FdEsc p.le p.R ρ)
    {ρf' ρ' fρ' : TRes w'.K} {ps' O' psF' : List (FrameRecT w'.K)} {rs' : List (FrameRecT w'.K)}
    (hT : TWNT w'.K w'.Θ w'.tc fρ' ps' rs') (hc : ResUT.CompS ρf' ρ' fρ')
    (hS : SplitT ps' O' psF') {p' : FrameRecT w'.K} (hp' : p' ∈ psF') (hpp : RecRR w'.Θ p p')
    (hu : UpdX (sem w'.Θ) (recMask O) (recMask O') ρ ρ') : FdEsc p'.le p'.R ρ' := by
  have hTI := hT.inv
  have hv := hT.valid
  have hp's : p' ∈ ps' := hS.right p' hp'
  have hp'rs : p' ∈ rs' := (hTI.2.2.2.2.2.2.1 p').mpr ⟨p', hp's, [], .nil p'⟩
  obtain ⟨σ, σ', hσ, hσ', hx⟩ := hu
  obtain ⟨σR, eR, aR, heR, -, -⟩ := hpv
  -- no own record of the run masks a location `FdEsc` reads of `p′`
  have hnm : ∀ x, (x = p'.le ∨ LinLocT p' x) → ¬ recMask O' x := by
    rintro x hxp ⟨q, hq, hqx⟩
    exact recMask_apart hT hp's (hS.left q hq) (fun e => hS.2 q hq p' hp' e.symm) hxp hqx
  -- those locations are ones `FdEsc` reads of `p`
  have hstart : ∀ x, (x = p'.le ∨ LinLocT p' x) → σ.get x = none := by
    rintro x (rfl | hl)
    · rw [hpp.1]; exact (h₀ σ hσ).1
    · exact (h₀ σ hσ).2 eR heR x ((hl.exDom.rr_back hpp.2.2.2).exST heR)
  -- an `imm` or `mut` cell there is refused by `↭`
  have hborrow : ∀ x, (x = p'.le ∨ LinLocT p' x) → ∀ ψ, σ'.get x = some ψ →
      ψ.kind ≠ Kind.own → False := by
    intro x hxp ψ e hk
    obtain ⟨-, ψ₀, e₀, -⟩ := (hx x).2 ψ e hk (hnm x hxp)
    rw [hstart x hxp] at e₀; cases e₀
  intro τ hτ
  obtain rfl := ResUT.Flat.functional hτ hσ'
  obtain ⟨aW, haW⟩ := agW_of_valid hv
  obtain ⟨er, ar, her, har, hcr⟩ := hσ'
  obtain ⟨a₁, a₂, ha₁, ha₂, hcW⟩ := (AgWT.split hc).mp haW
  obtain rfl := AgWT.functional har ha₂
  obtain ⟨eW, heW⟩ : ∃ eW, ExST fρ' eW := by
    obtain ⟨σW, eW, aW', heW, -, -⟩ := hv; exact ⟨eW, heW⟩
  obtain ⟨e₁, e₂, -, he₂, hc₁⟩ := (ExST.split hc).mp heW
  obtain rfl := ExST.functional her he₂
  -- an `own` cell at `x` of `⦇ρ′⦈`, given what `ag(W′)` holds there and what lies beneath it
  have hown : ∀ x, (∃ ζ, aW.get x = some ζ) →
      (∀ χ, ar.get x = some χ → χ.kind = Kind.own → False) →
      ∀ ψ, τ.get x = some ψ → ψ.kind = Kind.own → False := by
    intro x hag hbeneath ψ eψ hk
    obtain ⟨ζW, eζW⟩ := hag
    rcases ResUT.Comp.get hcr x with ⟨-, -, f⟩ | ⟨ψ₁, f₁, -, f⟩ | ⟨ψ₁, -, f₂, f⟩ |
        ⟨ψ₁, ψ₂, ψ₃, f₁, -, f, hC⟩
    · rw [eψ] at f; cases f
    · rw [eψ] at f; cases Option.some.inj f
      exact ex_ag_disjoint hv heW haW
        (ResUT.CompS.get_right_of_ne_imm hc₁ f₁ (by rw [hk]; simp)).2 eζW
    · rw [eψ] at f; cases Option.some.inj f
      exact hbeneath _ f₂ hk
    · rw [eψ] at f; cases Option.some.inj f
      obtain ⟨_, _, _, _, _, _, _, h₁, _, _⟩ := hC
      exact ExST.immFree her _ _ f₁ (by rw [h₁]; exact CellUT.kind_immOf _ _ _ _)
  refine ⟨?_, fun eR' heR' x hxs => ?_⟩
  · -- the lent location
    cases hg : τ.get p'.le with
    | none => rfl
    | some ψ =>
    exfalso
    by_cases hk : ψ.kind = Kind.own
    · obtain ⟨ψL, eL, -, -, -⟩ := hTI.2.1 p' hp's aW haW
      refine hown p'.le ⟨ψL, eL⟩ (fun χ f₂ hkχ => ?_) ψ hg hk
      obtain ⟨m, χ', hm, hχ', ψ₀, c₀, k₀, -⟩ :=
        agW_nonimm_beneath har _ χ f₂ (by rw [hkχ]; simp)
      obtain ⟨χ'', e'', k'', c''⟩ := beneath_of_compS_right hc hm hχ' c₀
      exact TWNT.noOwnUnder hT p' hp's ⟨m, χ'', e'', k'', c''.ownAt (k₀.trans hkχ)⟩
    · exact hborrow p'.le (Or.inl rfl) ψ hg hk
  · -- the escrow's exclusive locations
    obtain ⟨ψx, eψx⟩ := Option.isSome_iff_exists.mp hxs
    obtain ⟨d, hd, ζ, eζ, kζ⟩ :=
      exST_lineage w'.Θ heR' p' rfl (hTI.1.2.2.2.1 p' hp'rs) x ψx eψx
    have hlin : LinLocT p' x := ⟨d, hd, ζ, eζ, kζ⟩
    cases hg : τ.get x with
    | none => rfl
    | some ψ =>
    exfalso
    by_cases hk : ψ.kind = Kind.own
    · obtain ⟨pd, hpd⟩ := hd
      have hxR : CellAt p'.R x ζ := hpd.cellAt (fun y φ e => .top e) x ζ eζ
      refine hown x (le_view_cellAt hT hp's hxR haW) (fun χ f₂ hkχ => ?_) ψ hg hk
      obtain ⟨m₁, V, hV, kV, hloc⟩ :=
        innermost_view hT hp's hc ⟨pd, hpd⟩ eζ kζ har f₂ (by rw [hkχ]; simp)
      -- the view is an `imm` cell of `⦇ρ′⦈` at a location `FdEsc` reads
      obtain ⟨ζV, eζV, kζV, -⟩ := cellAt_imm_icp hV har kV
      obtain ⟨ξ, eξ⟩ := comp_some_r hcr eζV
      have hξ : ξ.kind ≠ Kind.own := by
        rcases ResUT.Comp.get hcr m₁ with ⟨-, f, -⟩ | ⟨ψ₁, -, f, -⟩ | ⟨ψ₁, -, f₂, f⟩ |
            ⟨ψ₁, ψ₂, ψ₃, f₁, f₂, f, hC⟩
        · rw [eζV] at f; cases f
        · rw [eζV] at f; cases f
        · rw [eξ] at f; rw [eζV] at f₂; cases Option.some.inj f₂; cases Option.some.inj f
          rw [kζV]; simp
        · rw [eξ] at f; cases Option.some.inj f
          rw [CellUT.CompS.kind hC]; simp
      exact hborrow m₁ hloc ξ eξ hξ
    · exact hborrow x (Or.inr hlin) ψ hg hk

end BoCa.Fig16.Tree.Wp

end
