import ProbeD1.GapCover

/-!
# ProbeD1 — the leaves at every payload type (`GAP.md` §2.3)

With `TyEqInst` at every type (`tyEqInst`), the thaw's borrow leaves lose their `CoreStable`
restriction. Each proof below is `BinderRows.lean`'s with two replacements: `tyEq_inst ι T hT` by
`tyEqInst`, and, at an `Imm` leaf at a bound place, `vC_true_eq_false` by `vO_obs` (the handed
view's full payload gives the slot's observable one). The retained `Mut` leaf
(`vC_mut_retained`) never read `CoreStable` and is reused as it is.

* **Coherence** (`cohE_instK`, `cohEInstOB`): `cohE_inst` at every type, the outermost lend below
  `⊤` kept (`not_cohEInst` refutes the case at `⊤`).
* **The leaves** (`vC_imm_retainedK`, `vC_mut_boundK`, `vC_imm_boundK`, `relendJ_mutK`,
  `relendJ_immK`) and the view slot (`viewSlotInstOB`).
* **The thaw at every `ThawFreeK` slot type** (`relendJ_valueK`, `relendJValueK`): W's formers
  down to `U` as before, `Mut` and `Imm` at every payload type (thunks, `μ` and `fam` inside a
  payload included). `μ` and `fam` *slots* stay outside (R1).
* **The context's thaw and the rows** (`ctxRelendsThawFreeKJ`, `statement0UThawFreeKJ`): the four
  `U` introductions at `binder0` at every `CtxThawFreeK` context. The rows are stated once, from
  the thaw of the row's own context (`thunkF_U_of_thawJ`, `thunkV_U_of_thawJ`), so that a context
  whose thaw is proved by other means reuses them.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace ProbeD1
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open GhostEnd (LEnt LStack LKind extS vwE vwS vis stratS ReLend TabAtS jdgCty)
open BoCa.BoLo (Step1N Head)

/-! ### Coherence at every type -/

/-- **Coherence at an instantiation, at every type**: `cohE_inst` with `tyEqInst` for
`tyEq_inst`. -/
theorem cohE_instK {αs : List Life} {ι : Inst} (hat : InstAt αs ι) (hob : OuterBelowTop αs)
    {ls ls' : List SRec} (hro : RecsOutside αs ls) {T : VTy} {s : LSub}
    {l : BoCa.Loc} {R : WRes} (hR : ∃ ψ, R.get l = some ψ ∧ ψ.kind = Kind.imm)
    (hks : KeepsS (ι.recs ls) ls' R) (h : CohE (rsOf ls) l T s) :
    CohE (rsOf ls') l T (ι.sub s) := by
  obtain ⟨S₀, δ₀, hTy, hCoh⟩ := h
  obtain ⟨ψ, hψ, hk⟩ := hR
  have key : ∀ y ∈ ls, AgreeOn S₀ δ₀ y.1.δ →
      (l = y.1.le ∧ S₀ = y.1.T ∨ ∃ p u, Chain y.1.R y.1.T y.1.v p l S₀ u) →
      CohE (rsOf ls') l T (ι.sub s) := by
    intro y hy hag hpos
    have hrel : Core.Rel y.1 R := by
      refine ⟨l, ψ, hψ, hk, ?_⟩
      rcases hpos with ⟨h1, -⟩ | ⟨p, u, hch⟩
      · exact Or.inl h1
      · exact Or.inr ⟨p, S₀, u, hch⟩
    obtain ⟨x', hx', hup⟩ :=
      hks (ι.rec1 y) (Inst.mem_recs.mpr ⟨y, hy, rfl⟩) ((rel_rec1 ι y R).mpr hrel)
    obtain ⟨hle, hv, hTT, hδ, -, hR'⟩ := hup
    have hδ' : x'.1.δ = ι.sub y.1.δ := hδ.trans (rec1_δ hat hob hro hy)
    have hmem : x'.1 ∈ rsOf ls' := List.mem_map_of_mem hx'
    refine ⟨S₀, x'.1.δ, ?_, ?_⟩
    · rw [hδ']
      exact tyEqInst T S₀ s y.1.δ ι (hTy.trans (TyEq.of_agree S₀ hag))
    · rcases hpos with ⟨h1, h2⟩ | ⟨p, u, hch⟩
      · left
        refine ⟨x'.1, hmem, ?_, ?_, fun _ _ => rfl⟩
        · rw [hle, Inst.rec1_le]; exact h1
        · rw [hTT, Inst.rec1_T]; exact h2
      · right
        refine ⟨x'.1, hmem, p, u, ?_, fun _ _ => rfl⟩
        rw [hTT, Inst.rec1_T, hv, Inst.rec1_v]
        exact Chain.of_own_iff (fun l' u' => by rw [hR' l' u', Inst.rec1_R]) hch
  rcases hCoh with ⟨r, hr, h1, h2, hag⟩ | ⟨r, hr, p, u, hch, hag⟩
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hr
    exact key y hy (h2 ▸ hag) (Or.inl ⟨h1, h2⟩)
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hr
    exact key y hy hag (Or.inr ⟨p, u, hch⟩)

/-- **`CohEInst` at every type, the outermost lend below `⊤`.** -/
theorem cohEInstOB : CohEInstOB :=
  fun _ _ _ _ _ _ _ _ hat hob hro hR hks h => cohE_instK hat hob hro hR hks h

/-! ### The leaves at every payload type -/

/-- **A retained `Imm` leaf at an instantiation, at every payload type.** -/
theorem vC_imm_retainedK {αs : List Life} {ι : Inst} (hat : InstAt αs ι) (hob : OuterBelowTop αs)
    {a : Lifetime.Life} {T : VTy} {ls ls' : List SRec}
    (hro : RecsOutside αs ls) {s : LSub} {v : Val} {ρ : WRes} (hpay : PayExt αs s T)
    (hz : stratS αs ρ) (he : Ext (ι.recs ls) ls' ρ) (hkt : KeepsT (ι.recs ls) ls' ρ)
    (h : vC true (.imm a T) ls s v ρ) : vC true (.imm a T) ls' (ι.sub s) v ρ := by
  obtain ⟨α, hα, ℓ, hsep⟩ := h
  obtain ⟨⟨hv, hcoh⟩, S, u, χ, hχ, ls₀, hρ, hP, hαS, hmem⟩ := pure_sep_iff.mp hsep
  have hg : ρ.get ℓ = some (CellU.immOf S u χ hχ) := by rw [hρ]; simp
  refine ⟨ι.life1 α, ?_, ℓ, pure_sep_mk ⟨hv, ?_⟩ ?_⟩
  · rw [Inst.interp_sub, hα]; rfl
  · exact cohE_instK hat hob hro ⟨_, hg, rfl⟩ (keepsS_of_keepsT hkt) hcoh
  · refine ⟨S, u, χ, hχ, ls₀, hρ, ?_, le_trans (ι.life1_le α) hαS, fun x => ?_⟩
    · show vC false T ls₀ (ι.sub s) u χ
      rw [vC_congr T (agree_of_payExt hat hpay) false ls₀]; exact hP
    · rw [hmem x]
      exact and_congr_left fun hxb =>
        mem_above_cell hat hz he hg (by simp [CellU.immOf, CellU.kind]) x hxb

/-- **A `Mut` leaf at a bound place at an instantiation, at every payload type**: the handed view
stores `𝒱⟦e.T⟧` at the instantiated reading, which is `𝒱⟦T⟧` there by `tyEqInst` and
`vC_tyEq`; its support transfers the same way. -/
theorem vC_mut_boundK (ι : Inst) {a : Lifetime.Life} {T : VTy} {e : LEnt}
    {s : LSub} {ls ls' : List SRec} {l : BoCa.Loc} {αe : Life} {ρ ρv : WRes} (hel : e.l = l)
    (hk : e.k = .mut) (hTy : TyEq T s e.T s) (h : vC true (.mut a T) ls s (.loc l) ρ)
    (hatl : ∀ ψ, ρ.get l = some ψ → ψ.at = αe)
    (hv : vwEW (ι.sub s) e true (ι.life1 αe) ls' ρv) :
    vC true (.mut a T) ls' (ι.sub s) (.loc l) ρv := by
  obtain ⟨el, ex, eT, ek, ecr⟩ := e
  simp only at hel hk hTy
  subst hel hk
  obtain ⟨α, hα, ℓ, hsep⟩ := h
  obtain ⟨hvl, b, u, σ', hσ', Q, hw, ls₀, hαb, hρ, -, -, -⟩ := pure_sep_iff.mp hsep
  cases hvl
  have hb : b = αe := hatl (CellU.mutOf b u σ' hσ' Q hw) (by rw [hρ]; simp)
  obtain ⟨⟨b', u', σ'', hσ'', Q', hw', ls₀', hαb', hρv, hQ', hmem', hsupp'⟩, -⟩ := hv
  have hTy' : TyEq T (ι.sub s) eT (ι.sub s) := tyEqInst T eT s s ι hTy
  have hP : ∀ ls₀, vC true T ls₀ (ι.sub s) = vC true eT ls₀ (ι.sub s) :=
    fun ls₀ => vC_tyEq hTy' true ls₀
  refine ⟨ι.life1 α, ?_, el, pure_sep_mk rfl
    ⟨b', u', σ'', hσ'', Q', hw', ls₀', ?_, hρv, ?_, hmem', ?_⟩⟩
  · rw [Inst.interp_sub, hα]; rfl
  · exact le_trans (ι.life1_le_iff.mpr (hb ▸ hαb)) hαb'
  · show ofS Q' = vC true T ls₀' (ι.sub s)
    rw [hP]; exact hQ'
  · intro ls₂ u₂ σ₂ hP₂
    exact hsupp' ls₂ u₂ σ₂ (by
      show vC true eT ls₂ (ι.sub s) u₂ σ₂; rw [← hP ls₂]; exact hP₂)

/-- **An `Imm` leaf at a bound place at an instantiation, at every payload type**: the handed
view's full payload, re-read up to `TyEq` (`tyEqInst`, `vC_tyEq`), gives the observable one
(`vO_obs`); coherence is moved by `cohE_instK`. -/
theorem vC_imm_boundK {αs : List Life} {ι : Inst} (hat : InstAt αs ι) (hob : OuterBelowTop αs)
    {a : Lifetime.Life} {T : VTy} {e : LEnt} {s : LSub} {ls ls' : List SRec}
    (hro : RecsOutside αs ls) {l : BoCa.Loc} {αe : Life} {ρ ρv : WRes} (hel : e.l = l)
    {u₀ : Val} (hk : e.k = .imm u₀) (hTy : TyEq T s e.T s)
    (h : vC true (.imm a T) ls s (.loc l) ρ) (hatl : ∀ ψ, ρ.get l = some ψ → ψ.at = αe)
    (hks : KeepsS (ι.recs ls) ls' ρ) (hv : vwEW (ι.sub s) e true (ι.life1 αe) ls' ρv) :
    vC true (.imm a T) ls' (ι.sub s) (.loc l) ρv := by
  obtain ⟨el, ex, eT, ek, ecr⟩ := e
  simp only at hel hk hTy
  subst hel hk
  obtain ⟨α, hα, ℓ, hsep⟩ := h
  obtain ⟨⟨hvl, hcoh⟩, S, u, χ, hχ, ls₀, hρ, -, hαS, -⟩ := pure_sep_iff.mp hsep
  cases hvl
  have hg : ρ.get el = some (CellU.immOf S u χ hχ) := by rw [hρ]; simp
  have hS : S.meet = αe := hatl _ hg
  obtain ⟨⟨S', u', χ', hχ', ls₀', hρv, hP', hαS', hmem'⟩, -⟩ := hv
  have hTy' : TyEq T (ι.sub s) eT (ι.sub s) := tyEqInst T eT s s ι hTy
  refine ⟨ι.life1 α, ?_, el, pure_sep_mk ⟨rfl, ?_⟩ ⟨S', u', χ', hχ', ls₀', hρv, ?_, ?_, hmem'⟩⟩
  · rw [Inst.interp_sub, hα]; rfl
  · exact cohE_instK hat hob hro ⟨_, hg, rfl⟩ hks hcoh
  · show vC false T ls₀' (ι.sub s) u' χ'
    refine vO_obs T ?_
    rw [vC_tyEq hTy' true]; exact hP'
  · exact le_trans (ι.life1_le_iff.mpr (hS ▸ hαS)) hαS'

/-- **`ViewSlotInst` at every slot type, the outermost lend below `⊤`**: `viewSlotInstCS`'s proof
at the leaves of every payload type. -/
theorem viewSlotInstOB : ViewSlotInstOB := by
  intro σ αs s ls ls' A l e α ρ ρv ι hob hi hat hro hks hvc hcoh hv
  have hel : e.l = l := (innerAt_mem hi).2
  have hco := hcoh l e α rfl hi
  have hcohI : (∀ ψ, ρv.get l = some ψ → ψ.at = ι.life1 α) →
      CohKind (ι.sub s) e A → CohS σ (ι.life αs) (ι.sub s) A (.loc l) ρv := by
    intro hat' hk' l' e' α' hl' hi'
    cases hl'
    rw [innerAt_inst_some ι hi] at hi'
    obtain ⟨rfl, rfl⟩ : e = e' ∧ ι.life1 α = α' := by simpa using hi'
    exact ⟨hk', hat'⟩
  have hat' : ∀ ψ, ρv.get l = some ψ → ψ.at = ι.life1 α :=
    fun ψ hψ => (hv.2 ψ (by rw [hel]; exact hψ)).1
  cases A with
  | «mut» a T =>
      obtain ⟨hkind, hTy⟩ := hco.1
      have hk : e.k = .mut := by
        cases hek : e.k with
        | «mut» => rfl
        | imm u₀ => rw [hek] at hkind; exact hkind.elim
      exact ⟨vC_mut_boundK ι (T := T) hel hk hTy hvc hco.2 hv,
        hcohI hat' ⟨by rw [hk]; trivial, tyEqInst T e.T s s ι hTy⟩⟩
  | imm a T =>
      obtain ⟨hkind, hTy⟩ := hco.1
      obtain ⟨u₀, hk⟩ : ∃ u₀, e.k = .imm u₀ := by
        cases hek : e.k with
        | «mut» => rw [hek] at hkind; exact hkind.elim
        | imm u₀ => exact ⟨u₀, rfl⟩
      exact ⟨vC_imm_boundK hat hob (T := T) hro hel hk hTy hvc hco.2 hks hv,
        hcohI hat' ⟨by rw [hk]; trivial, tyEqInst T e.T s s ι hTy⟩⟩
  | unit => exact hco.1.elim
  | zero => exact hco.1.elim
  | unk => exact hco.1.elim
  | int _ => exact hco.1.elim
  | opq _ => exact hco.1.elim
  | tvar _ => exact hco.1.elim
  | tensor _ _ => exact hco.1.elim
  | sum _ _ => exact hco.1.elim
  | thunk _ => exact hco.1.elim
  | bang _ => exact hco.1.elim
  | box _ _ => exact hco.1.elim
  | ref _ => exact hco.1.elim
  | mu _ => exact hco.1.elim
  | fam _ => exact hco.1.elim

/-! ### The leaves' thaw at every payload type -/

/-- **The thaw of a `Mut` leaf, at every payload type**: `relendJ_mut` with `vC_mut_boundK` and
`tyEqInst`. -/
theorem relendJ_mutK {a : Lifetime.Life} {T : VTy} {δ : LSub} {σ : LStack}
    {αs : List Life} {ls : List SRec} {v : Val} {ρ : WRes} (hok : StackOK σ αs)
    (ht : TabAtS σ αs ρ) (hpv : PlaceViewsL (extS δ σ αs) σ αs ls ρ)
    (h : vRLJ .binder0 σ δ (.mut a T) αs ls v ρ) :
    RelendJ δ σ (fun δ' αs' ls' => vRLJ .binder0 σ δ' (.mut a T) αs' ls' v) αs ls ρ := by
  rw [vRLJ_mut_eq] at h
  obtain ⟨hvc, hcoh, hpay⟩ := h
  obtain ⟨α, -, ℓ, hsep⟩ := id hvc
  obtain ⟨rfl, b, u, σ', hσ', Q, hw, ls₀, -, hρ, -⟩ := pure_sep_iff.mp hsep
  have hg : ρ.get ℓ = some (CellU.mutOf b u σ' hσ' Q hw) := by rw [hρ]; simp
  cases hi : innerAt σ αs ℓ with
  | none =>
      have hz : stratS αs ρ := stratS_single_unbound hok.1 ht hρ hi
      have hp := hpay ℓ rfl hi
      refine ⟨σ.map fun _ => false, ρ, PMap.empty, ResU.comp_empty_right ρ,
        ⟨vwSW_false hok.1, placeViewsL_empty⟩, hz, fun ι hat ls' he _ _ _ ρv τ hv hcv => ?_⟩
      rw [vwSW_false_inv hv.1] at hcv
      rw [eq_of_compS_empty_left (ResU.CompS.comm hcv)]
      rw [vRLJ_mut_eq, extS_inst]
      refine ⟨vC_mut_retained hat hp hz he hvc, fun l' e' α' hl' hi' => ?_, fun l' hl' _ => ?_⟩
      · cases hl'
        rw [innerAt_inst_none ι hi] at hi'; exact absurd hi' (by simp)
      · cases hl'; exact payExt_inst hat hp
  | some p =>
      obtain ⟨e, αe⟩ := p
      have hview : vwEW (extS δ σ αs) e true αe ls ρ := by
        have := hpv.1 ℓ _ (ExAt.top hg) CellU.kind_mutOf_ne_own e αe hi
        rwa [← hρ] at this
      obtain ⟨hkind, hTy⟩ := (hcoh ℓ e αe rfl hi).1
      have hatl := (hcoh ℓ e αe rfl hi).2
      have hk : e.k = .mut := by
        cases hek : e.k with
        | «mut» => rfl
        | imm u₀ => rw [hek] at hkind; exact hkind.elim
      have hel : e.l = ℓ := (innerAt_mem hi).2
      refine ⟨dsPlace σ ℓ, PMap.empty, ρ, compS_empty_left ρ,
        ⟨vwSW_dsAt hview hok.1 List.not_mem_nil hi, hpv⟩, stratS_empty αs,
        fun ι hat ls' _ _ _ _ ρv τ hv hcv => ?_⟩
      rw [eq_of_compS_empty_left hcv]
      have hv' : vwEW (ι.sub (extS δ σ αs)) e true (ι.life1 αe) ls' ρv := by
        have := vwSW_dsAt_inv List.not_mem_nil (innerAt_inst_some ι hi) hv.1
        rwa [extS_inst] at this
      beta_reduce
      rw [vRLJ_mut_eq, extS_inst]
      refine ⟨vC_mut_boundK ι hel hk hTy hvc hatl hv', fun l' e' α' hl' hi' => ?_,
        fun l' hl' hn => ?_⟩
      · cases hl'
        rw [innerAt_inst_some ι hi] at hi'
        obtain ⟨rfl, rfl⟩ : e = e' ∧ ι.life1 αe = α' := by simpa using hi'
        refine ⟨⟨by rw [hk]; trivial, tyEqInst T e.T _ _ ι hTy⟩, fun ψ hψ => ?_⟩
        exact (hv'.2 ψ (by rw [hel]; exact hψ)).1
      · cases hl'
        rw [innerAt_inst_some ι hi] at hn; exact absurd hn (by simp)

/-- **The thaw of an `Imm` leaf, at every payload type**: `relendJ_imm` with `vC_imm_retainedK`,
`vC_imm_boundK` and `tyEqInst`. -/
theorem relendJ_immK {a : Lifetime.Life} {T : VTy} {δ : LSub} {σ : LStack}
    {αs : List Life} {ls : List SRec} {v : Val} {ρ : WRes} (hok : StackOK σ αs)
    (hob : OuterBelowTop αs) (hro : RecsOutside αs ls) (ht : TabAtS σ αs ρ)
    (hpv : PlaceViewsL (extS δ σ αs) σ αs ls ρ) (h : vRLJ .binder0 σ δ (.imm a T) αs ls v ρ) :
    RelendJ δ σ (fun δ' αs' ls' => vRLJ .binder0 σ δ' (.imm a T) αs' ls' v) αs ls ρ := by
  rw [vRLJ_imm_eq] at h
  obtain ⟨hvc, hcoh, hpay⟩ := h
  obtain ⟨α, -, ℓ, hsep⟩ := id hvc
  obtain ⟨⟨rfl, -⟩, S, u, χ, hχ, ls₀, hρ, -⟩ := pure_sep_iff.mp hsep
  have hg : ρ.get ℓ = some (CellU.immOf S u χ hχ) := by rw [hρ]; simp
  have hko : (CellU.immOf S u χ hχ).kind ≠ Kind.own := by simp [CellU.immOf, CellU.kind]
  cases hi : innerAt σ αs ℓ with
  | none =>
      have hz : stratS αs ρ := stratS_single_unbound hok.1 ht hρ hi
      have hp := hpay ℓ rfl hi
      refine ⟨σ.map fun _ => false, ρ, PMap.empty, ResU.comp_empty_right ρ,
        ⟨vwSW_false hok.1, placeViewsL_empty⟩, hz,
        fun ι hat ls' he hkt _ _ ρv τ hv hcv => ?_⟩
      rw [vwSW_false_inv hv.1] at hcv
      rw [eq_of_compS_empty_left (ResU.CompS.comm hcv)]
      rw [vRLJ_imm_eq, extS_inst]
      refine ⟨vC_imm_retainedK hat hob hro hp hz he hkt hvc, fun l' e' α' hl' hi' => ?_,
        fun l' hl' _ => ?_⟩
      · cases hl'
        rw [innerAt_inst_none ι hi] at hi'; exact absurd hi' (by simp)
      · cases hl'; exact payExt_inst hat hp
  | some p =>
      obtain ⟨e, αe⟩ := p
      have hview : vwEW (extS δ σ αs) e true αe ls ρ := by
        have := hpv.1 ℓ _ (ExAt.top hg) hko e αe hi
        rwa [← hρ] at this
      obtain ⟨hkind, hTy⟩ := (hcoh ℓ e αe rfl hi).1
      have hatl := (hcoh ℓ e αe rfl hi).2
      obtain ⟨u₀, hk⟩ : ∃ u₀, e.k = .imm u₀ := by
        cases hek : e.k with
        | «mut» => rw [hek] at hkind; exact hkind.elim
        | imm u₀ => exact ⟨u₀, rfl⟩
      have hel : e.l = ℓ := (innerAt_mem hi).2
      refine ⟨dsPlace σ ℓ, PMap.empty, ρ, compS_empty_left ρ,
        ⟨vwSW_dsAt hview hok.1 List.not_mem_nil hi, hpv⟩, stratS_empty αs,
        fun ι hat ls' _ _ hks _ ρv τ hv hcv => ?_⟩
      rw [eq_of_compS_empty_left hcv]
      have hv' : vwEW (ι.sub (extS δ σ αs)) e true (ι.life1 αe) ls' ρv := by
        have := vwSW_dsAt_inv List.not_mem_nil (innerAt_inst_some ι hi) hv.1
        rwa [extS_inst] at this
      beta_reduce
      rw [vRLJ_imm_eq, extS_inst]
      refine ⟨vC_imm_boundK hat hob hro hel hk hTy hvc hatl hks hv',
        fun l' e' α' hl' hi' => ?_, fun l' hl' hn => ?_⟩
      · cases hl'
        rw [innerAt_inst_some ι hi] at hi'
        obtain ⟨rfl, rfl⟩ : e = e' ∧ ι.life1 αe = α' := by simpa using hi'
        refine ⟨⟨by rw [hk]; trivial, tyEqInst T e.T _ _ ι hTy⟩, fun ψ hψ => ?_⟩
        exact (hv'.2 ψ (by rw [hel]; exact hψ)).1
      · cases hl'
        rw [innerAt_inst_some ι hi] at hn; exact absurd hn (by simp)

/-! ### The thaw at every `ThawFreeK` slot type -/

/-- **The thaw of a slot, at every type `ThawFreeK` admits**: `relendJ_value`'s recursion, the
borrow leaves at every payload type (`relendJ_mutK`, `relendJ_immK`). -/
theorem relendJ_valueK : ∀ (A : VTy), ThawFreeK A →
    ∀ {δ : LSub} {σ : LStack} {αs : List Life} {ls : List SRec} {v : Val} {ρ : WRes},
    StackOK σ αs → OuterBelowTop αs → RecsOutside αs ls → TabAtS σ αs ρ →
    PlaceViewsL (extS δ σ αs) σ αs ls ρ → vRLJ .binder0 σ δ A αs ls v ρ →
    RelendJ δ σ (fun δ' αs' ls' => vRLJ .binder0 σ δ' A αs' ls' v) αs ls ρ
  | .thunk _, _, _, _, _, _, _, _, _, _, _, ht, hpv, h => relendJ_thunk ht hpv h
  | .tensor A B, hAB, _, _, _, _, _, _, hok, hob, hro, ht, hpv, h => by
      obtain ⟨v₁, v₂, hsep⟩ := h
      obtain ⟨rfl, ρ₁, ρ₂, hc, h₁, h₂⟩ := pure_sep_iff.mp hsep
      have R₁ := relendJ_valueK A hAB.1 hok hob hro (tabAtS_left hc ht)
        (placeViewsL_left hc hpv) h₁
      have R₂ := relendJ_valueK B hAB.2 hok hob hro (tabAtS_right hc ht)
        (placeViewsL_right hc hpv) h₂
      exact relendJ_mono (fun _ _ _ τ hτ => ⟨v₁, v₂, pure_sep_mk rfl hτ⟩)
        (relendJ_sep ⟨ρ₁, ρ₂, hc, R₁, R₂⟩)
  | .sum A B, hAB, _, _, _, _, _, _, hok, hob, hro, ht, hpv, h => by
      rcases h with ⟨v₁, hsep⟩ | ⟨v₂, hsep⟩
      · obtain ⟨rfl, h₁⟩ := pure_sep_iff.mp hsep
        exact relendJ_mono (fun _ _ _ τ hτ => Or.inl ⟨v₁, pure_sep_mk rfl hτ⟩)
          (relendJ_valueK A hAB.1 hok hob hro ht hpv h₁)
      · obtain ⟨rfl, h₂⟩ := pure_sep_iff.mp hsep
        exact relendJ_mono (fun _ _ _ τ hτ => Or.inr ⟨v₂, pure_sep_mk rfl hτ⟩)
          (relendJ_valueK B hAB.2 hok hob hro ht hpv h₂)
  | .bang A, hA, _, _, _, _, _, _, hok, hob, hro, ht, hpv, h => by
      obtain ⟨rfl, h₁⟩ := h
      obtain ⟨ds, ρz, ρn, hc, hn, hz, H⟩ := relendJ_valueK A hA hok hob hro ht hpv h₁
      have hz0 := eq_empty_of_compS_left hc
      have hn0 := eq_empty_of_compS_right hc
      subst hz0 hn0
      refine ⟨ds, PMap.empty, PMap.empty, hc, hn, hz,
        fun ι hat ls' he hkt hks hro' ρv τ hv hcv => ?_⟩
      have hv0 : ρv = PMap.empty := vwSW_eq_empty_inst ι hn.1 hv.1
      subst hv0
      exact ⟨eq_empty_of_compS_empty hcv, H ι hat ls' he hkt hks hro' PMap.empty τ hv hcv⟩
  | .box a A, hA, _, _, _, _, _, _, hok, hob, hro, ht, hpv, h => by
      obtain ⟨α, hα, hv, hout⟩ := h
      obtain ⟨ds, ρz, ρn, hc, hn, hz, H⟩ := relendJ_valueK A hA hok hob hro ht hpv hv
      have hzo := (outlives_comp hc α).mp hout
      refine ⟨ds, ρz, ρn, hc, hn, hz, fun ι hat ls' he hkt hks hro' ρv τ hv' hcv => ?_⟩
      refine ⟨ι.life1 α, ?_, H ι hat ls' he hkt hks hro' ρv τ hv' hcv, ?_⟩
      · rw [extS_inst, Inst.interp_sub, hα]; rfl
      · exact (outlives_comp hcv _).mpr ⟨ResU.InStratum.mono (ι.life1_le α) hzo.1,
          vwSW_outlives_inst ι hn.1 hv'.1 hzo.2⟩
  | .ref A, hA, _, _, _, _, _, _, hok, hob, hro, ht, hpv, h => by
      obtain ⟨ℓ, v', hsep⟩ := h
      obtain ⟨rfl, ρo, ρa, hc, hown, ha⟩ := pure_sep_iff.mp hsep
      obtain ⟨ds, ρz, ρn, hc', hn, hz, H⟩ :=
        relendJ_valueK A hA hok hob hro (tabAtS_right hc ht) (placeViewsL_right hc hpv) ha
      obtain ⟨ρz', hcz, hc''⟩ := compS_reassoc' hc' hc
      refine ⟨ds, ρz', ρn, hc'', hn, fun o ho => (outlives_comp hcz o).mpr
        ⟨by rw [hown]; exact ResU.inStratum_single_own o ℓ v', hz o ho⟩,
        fun ι hat ls' he hkt hks hro' ρv τ hv hcv => ?_⟩
      obtain ⟨τa, hτa, hτ⟩ := compS_reassoc hcz hcv
      exact ⟨ℓ, v', pure_sep_mk rfl ⟨ρo, τa, hτ, hown,
        H ι hat ls' (he.right hcz) (hkt.right hcz) hks hro' ρv τa hv hτa⟩⟩
  | .mut _ T, _, _, _, _, _, _, _, hok, _, _, ht, hpv, h => relendJ_mutK (T := T) hok ht hpv h
  | .imm _ T, _, _, _, _, _, _, _, hok, hob, hro, ht, hpv, h =>
      relendJ_immK (T := T) hok hob hro ht hpv h
  | .unit, _, _, _, _, _, _, _, hok, _, _, _, _, h => by
      obtain ⟨rfl, hv⟩ := h
      exact relendJ_emp hok.1 fun _ _ _ => ⟨rfl, hv⟩
  | .int _, _, _, _, _, _, _, _, hok, _, _, _, _, h => by
      obtain ⟨rfl, hv⟩ := h
      exact relendJ_emp hok.1 fun _ _ _ => ⟨rfl, hv⟩
  | .opq _, _, _, _, _, _, _, _, hok, _, _, _, _, h => by
      obtain ⟨rfl, hv⟩ := h
      exact relendJ_emp hok.1 fun _ _ _ => ⟨rfl, hv⟩
  | .unk, _, _, _, _, _, _, _, hok, _, _, _, _, h => by
      obtain ⟨rfl, hv⟩ := h
      exact relendJ_emp hok.1 fun _ _ _ => ⟨rfl, hv⟩
  | .zero, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | .tvar _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | .mu _, hA, _, _, _, _, _, _, _, _, _, _, _, _ => hA.elim
  | .fam _, hA, _, _, _, _, _, _, _, _, _, _, _, _ => hA.elim

theorem relendJValueK : RelendJValueK :=
  fun A hA _ _ _ _ _ _ hok hob hro ht hpv h => relendJ_valueK A hA hok hob hro ht hpv h

/-- **The thaw of a context's slots, at every `CtxThawFreeK` context.** -/
theorem relendJ_gSepK : ∀ (Γ : Ctx VTy) (γ : List Val), CtxThawFreeK Γ →
    ∀ {δ : LSub} {σ : LStack} {αs : List Life} {ls : List SRec} {ρ : WRes},
    StackOK σ αs → OuterBelowTop αs → RecsOutside αs ls → TabAtS σ αs ρ →
    PlaceViewsL (extS δ σ αs) σ αs ls ρ → gSepRLJ .binder0 σ δ αs ls Γ γ ρ →
    RelendJ δ σ (fun δ' αs' ls' => gSepRLJ .binder0 σ δ' αs' ls' Γ γ) αs ls ρ
  | [], _, _, _, _, _, _, _, hok, _, _, _, _, h => by
      obtain ⟨rfl, -⟩ := h
      exact relendJ_emp hok.1 fun _ _ _ => ⟨rfl, trivial⟩
  | _ :: _, [], _, _, _, _, _, _, hok, _, _, _, _, h => by
      obtain ⟨rfl, -⟩ := h
      exact relendJ_emp hok.1 fun _ _ _ => ⟨rfl, trivial⟩
  | s :: Γ, v :: γ, hTF, _, _, _, _, _, hok, hob, hro, ht, hpv, h => by
      have hTF' : CtxThawFreeK Γ := fun s' hs' hl => hTF s' (List.mem_cons_of_mem _ hs') hl
      by_cases hl : s.live = true
      · simp only [gSepRLJ, hl, if_true] at h ⊢
        obtain ⟨ρ₁, ρ₂, hc, h₁, h₂⟩ := h
        have R₁ := relendJ_valueK s.ty (hTF s List.mem_cons_self hl) hok hob hro
          (tabAtS_left hc ht) (placeViewsL_left hc hpv) h₁
        have R₂ := relendJ_gSepK Γ γ hTF' hok hob hro (tabAtS_right hc ht)
          (placeViewsL_right hc hpv) h₂
        exact relendJ_sep ⟨ρ₁, ρ₂, hc, R₁, R₂⟩
      · simp only [gSepRLJ, hl] at h ⊢
        exact relendJ_gSepK Γ γ hTF' hok hob hro ht hpv h

/-- **`CtxRelendsThawFreeKJ binder0`**: the context's thaw at every `CtxThawFreeK` context. -/
theorem ctxRelendsThawFreeKJ : CtxRelendsThawFreeKJ (ℍ := ℍ) .binder0 := by
  intro Δ Γ hTF δ σ αs ls γ ρ hok hob _ _ hro _ ht hpv hg
  obtain ⟨hlw, hgs⟩ := pure_sep_iff.mp hg
  exact relendJ_mono (fun _ _ _ τ hτ => pure_sep_mk hlw hτ)
    (relendJ_gSepK Γ γ hTF hok hob hro ht hpv hgs)

/-! ### The `U` introductions from the context's thaw -/

/-- **The `U` clause of `thunk M : U (F A)` at `binder0`, from the thaw of the row's own
context**: `thunkF_U_J` with its first step, the context's thaw, taken as a hypothesis. -/
theorem thunkF_U_of_thawJ {Δ : LifeCtx} {Γ : Ctx VTy}
    (hthaw : CtxRelendableAtJ (ℍ := ℍ) .binder0 Δ Γ) {M : Expr} {A : VTy}
    (hM : SemSJ (ℍ := ℍ) .binder0 Δ (⟨.unit, false⟩ :: Γ) M (.comp (.ret A)))
    (hBL : BindersLow (⟨.unit, false⟩ :: Γ) (.ret A))
    (hSc : Scoped Δ (⟨.unit, false⟩ :: Γ) (.ret A))
    {δ : LSub} {σ : LStack} {αs : List Life} {ls : List SRec} {γ : List Val} {ρ : WRes}
    (hok : StackOK σ αs) (hob : OuterBelowTop αs)
    (hJ : StackJ σ αs δ Δ (⟨.unit, false⟩ :: Γ) (.ret A)) (hSD : SubDom δ Δ)
    (hMod : Δ.Models (extS δ σ αs)) (hro : RecsOutside αs ls) (hso : SubOutside σ αs δ)
    (ht : TabAtS σ αs ρ) (hpv : PlaceViewsL (extS δ σ αs) σ αs ls ρ)
    (hg : gRLJ .binder0 σ δ αs ls Γ γ ρ) :
    vRLJ (ℍ := ℍ) .binder0 σ δ (.thunk (.ret A)) αs ls (.lam (Expr.psub 1 γ M)) ρ := by
  rw [vRLJ_thunk0]
  intro _ _
  obtain ⟨ds, ρz, ρn, hc, hn, hz, H⟩ :=
    hthaw δ σ αs ls γ ρ hok hob hSD hMod hro hso ht hpv hg
  refine ⟨ds, ρz, ρn, hc, hn, hz, fun ι hat ls' he hkt hks hro' ρv τ hv hcv => ?_⟩
  obtain ⟨ht', hpv'⟩ := guardInst δ σ ds αs ls ls' ρz ρn ρ ρv τ ι hok hat hz hn hc hpv hv hcv
  have hg' := H ι hat ls' he hkt hks hro' ρv τ hv hcv
  refine wpTS_step (fun μ => Step1N.head (Head.beta μ _ Val.unit) rfl) ls' _ τ ?_
  rw [← GhostEnd.substAll_cons_l]
  exact hM hBL hSc (ι.sub δ) σ (ι.life αs) ls' (Val.unit :: γ) τ (hok.inst ι)
    (outerBelowTop_inst ι hob) (stackJInst σ αs δ Δ _ _ ι hok.1 hJ) (subDom_inst ι hSD)
    (instModels Δ δ σ αs ι hMod) hro' (subOutsideInst σ αs δ ι hso) ht' hpv'
    (gRLJ_dead_cons hg')

/-- **The `U` clause of `thunk V : U C` at `binder0`, from the thaw of the row's own context.** -/
theorem thunkV_U_of_thawJ {Δ : LifeCtx} {Γ : Ctx VTy}
    (hthaw : CtxRelendableAtJ (ℍ := ℍ) .binder0 Δ Γ) {N : Expr} {C : CTy}
    (hC : C.isRet = false) (hN : SemSJ (ℍ := ℍ) .binder0 Δ Γ (.val (.lam N)) (.comp C))
    (hBL : BindersLow Γ C) (hSc : Scoped Δ Γ C)
    {δ : LSub} {σ : LStack} {αs : List Life} {ls : List SRec} {γ : List Val} {ρ : WRes}
    (hok : StackOK σ αs) (hob : OuterBelowTop αs) (hJ : StackJ σ αs δ Δ Γ C)
    (hSD : SubDom δ Δ) (hMod : Δ.Models (extS δ σ αs)) (hro : RecsOutside αs ls)
    (hso : SubOutside σ αs δ) (ht : TabAtS σ αs ρ) (hpv : PlaceViewsL (extS δ σ αs) σ αs ls ρ)
    (hg : gRLJ .binder0 σ δ αs ls Γ γ ρ) :
    vRLJ (ℍ := ℍ) .binder0 σ δ (.thunk C) αs ls (.lam (Expr.psub 1 γ N)) ρ := by
  rw [vRLJ_thunk0]
  intro _ _
  obtain ⟨ds, ρz, ρn, hc, hn, hz, H⟩ :=
    hthaw δ σ αs ls γ ρ hok hob hSD hMod hro hso ht hpv hg
  refine ⟨ds, ρz, ρn, hc, hn, hz, fun ι hat ls' he hkt hks hro' ρv τ hv hcv => ?_⟩
  obtain ⟨ht', hpv'⟩ := guardInst δ σ ds αs ls ls' ρz ρn ρ ρv τ ι hok hat hz hn hc hpv hv hcv
  rw [forceE_of_not_ret hC]
  exact hN hBL hSc (ι.sub δ) σ (ι.life αs) ls' γ τ (hok.inst ι) (outerBelowTop_inst ι hob)
    (stackJInst σ αs δ Δ Γ C ι hok.1 hJ) (subDom_inst ι hSD) (instModels Δ δ σ αs ι hMod) hro'
    (subOutsideInst σ αs δ ι hso) ht' hpv' (H ι hat ls' he hkt hks hro' ρv τ hv hcv)

/-! ### The rows at every `CtxThawFreeK` context -/

/-- **`ThunkFRow` at `binder0`, at every `CtxThawFreeK` context.** -/
theorem thunkFRowKJ : ThunkFRowKJ (ℍ := ℍ) .binder0 := by
  intro Δ Γ M A hTF hM hBL hSc δ σ αs ls γ ρ hok hob hJ hSD hMod hro hso ht hpv hg
  show wpTS ls (.val (.lam (Expr.psub 1 γ M))) _ ρ
  refine wpTS_val _ _ _ _ (thunkF_U_of_thawJ (ctxRelendsThawFreeKJ Δ Γ hTF) hM
    ⟨hBL.1, fun s hs hl => ?_⟩ ⟨hSc.1, fun s hs hl => ?_⟩ hok hob
    (stackJ_body hJ (fun _ _ _ h => by cases h) (fun _ h => h) fun _ => ctxAvoids_dead)
    hSD hMod hro hso ht hpv hg)
  · rcases List.mem_cons.mp hs with rfl | hs
    · simp at hl
    · exact hBL.2 s hs hl
  · rcases List.mem_cons.mp hs with rfl | hs
    · simp at hl
    · exact hSc.2 s hs hl

/-- **`ThunkVRow` at `binder0`, at every `CtxThawFreeK` context.** -/
theorem thunkVRowKJ : ThunkVRowKJ (ℍ := ℍ) .binder0 := by
  intro Δ Γ N C hTF hC _ hN hBL hSc δ σ αs ls γ ρ hok hob hJ hSD hMod hro hso ht hpv hg
  show wpTS ls (.val (.lam (Expr.psub 1 γ N))) _ ρ
  exact wpTS_val _ _ _ _ (thunkV_U_of_thawJ (ctxRelendsThawFreeKJ Δ Γ hTF) hC hN hBL hSc hok
    hob (stackJ_body hJ (fun _ _ _ h => by cases h) (fun _ h => h) fun _ h => h)
    hSD hMod hro hso ht hpv hg)

/-- **`BangThunkFRow` at `binder0`, at every `CtxThawFreeK` context.** -/
theorem bangThunkFRowKJ : BangThunkFRowKJ (ℍ := ℍ) .binder0 := by
  intro Δ Γ M A hTF hP hM hBL hSc δ σ αs ls γ ρ hok hob hJ hSD hMod hro hso ht hpv hg
  have hρ : ρ = PMap.empty := gSepRLJ_persistent Γ γ ρ hP (pure_sep_iff.mp hg).2
  show wpTS ls (.val (.lam (Expr.psub 1 γ M))) _ ρ
  refine wpTS_val _ _ _ _ ⟨hρ, thunkF_U_of_thawJ (ctxRelendsThawFreeKJ Δ Γ hTF) hM
    ⟨hBL.1, fun s hs hl => ?_⟩ ⟨hSc.1, fun s hs hl => ?_⟩ hok hob
    (stackJ_body hJ (fun _ _ _ h => by cases h) (fun _ h => h) fun _ => ctxAvoids_dead)
    hSD hMod hro hso ht hpv hg⟩
  · rcases List.mem_cons.mp hs with rfl | hs
    · simp at hl
    · exact hBL.2 s hs hl
  · rcases List.mem_cons.mp hs with rfl | hs
    · simp at hl
    · exact hSc.2 s hs hl

/-- **`BangThunkVRow` at `binder0`, at every `CtxThawFreeK` context.** -/
theorem bangThunkVRowKJ : BangThunkVRowKJ (ℍ := ℍ) .binder0 := by
  intro Δ Γ N C hTF hP hC _ hN hBL hSc δ σ αs ls γ ρ hok hob hJ hSD hMod hro hso ht hpv hg
  have hρ : ρ = PMap.empty := gSepRLJ_persistent Γ γ ρ hP (pure_sep_iff.mp hg).2
  show wpTS ls (.val (.lam (Expr.psub 1 γ N))) _ ρ
  exact wpTS_val _ _ _ _ ⟨hρ, thunkV_U_of_thawJ (ctxRelendsThawFreeKJ Δ Γ hTF) hC hN hBL hSc
    hok hob (stackJ_body hJ (fun _ _ _ h => by cases h) (fun _ h => h) fun _ h => h)
    hSD hMod hro hso ht hpv hg⟩

/-- **The `U` side of statement 0 at `binder0`, at the revised W, at every `CtxThawFreeK`
context.** -/
theorem statement0UThawFreeKJ : Statement0UThawFreeKJ (ℍ := ℍ) .binder0 :=
  ⟨thawInstJ, ctxRelendsThawFreeKJ, thunkFRowKJ, thunkVRowKJ, bangThunkFRowKJ, bangThunkVRowKJ⟩

/-- `CtxThawFree` is inside `CtxThawFreeK`: the partial result widens. -/
theorem thawFreeK_of_thawFree : ∀ A : VTy, ThawFree A → ThawFreeK A
  | .thunk _, _ => trivial
  | .tensor A B, h => ⟨thawFreeK_of_thawFree A h.1, thawFreeK_of_thawFree B h.2⟩
  | .sum A B, h => ⟨thawFreeK_of_thawFree A h.1, thawFreeK_of_thawFree B h.2⟩
  | .bang A, h => thawFreeK_of_thawFree A h
  | .box _ A, h => thawFreeK_of_thawFree A h
  | .ref A, h => thawFreeK_of_thawFree A h
  | .mu _, h => h.elim
  | .fam _, h => h.elim
  | .unit, _ | .zero, _ | .unk, _ | .int _, _ | .opq _, _ | .tvar _, _ | .imm _ _, _
  | .mut _ _, _ => trivial

theorem ctxThawFreeK_of_ctxThawFree {Γ : Ctx VTy} (h : CtxThawFree Γ) : CtxThawFreeK Γ :=
  fun s hs hl => thawFreeK_of_thawFree s.ty (h s hs hl)

/-- **The widening is strict**: `Mut '0 (U (F 1))`, a `Mut` view of a thunk, is `ThawFreeK` and
not `ThawFree`. -/
theorem thawFreeK_strict :
    ThawFreeK (.mut (.var 0) (.thunk (.ret .unit))) ∧
      ¬ ThawFree (.mut (.var 0) (.thunk (.ret .unit))) :=
  ⟨trivial, fun h => h⟩

end ProbeD1

end
