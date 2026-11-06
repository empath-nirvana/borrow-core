import Core.Chain.Eff835N

/-!
# The frame at a row's table, and a value read off its run  `[spec §19, §27]`

Interface entries E8 and W9 (`scope-831-interface.md`), each Core's proof at `erwp`:

* **E8** (Core's `cancel_frame`, `plain_cancel₀`, `Row.tab_plainCancel`, `cancel_frame_consume`,
  `ent_plain`, `ewp_frame_plain`). A cancel run under a plain context `K` (no handler, catches no
  cancel), beside a frame owning nothing, ends leaving both behind; at a stop both join the
  continuation (`cancelOblN_frame`). A row's table carries its cancel obligations through `K`, by
  Core's recursion on the cancel rows (`tabN_plainCancel`). A frame owning nothing is garbage
  (`cancelOblN_frame_consume`, `entN_plain`). An effectful computation under `K`, beside a frame
  `Fr`, carries `Fr` into every stop's continuation; at an abortive stop `Fr` is left behind
  owning nothing, at an unrestricted one it is empty, and at a cancel it is carried by the
  entry's cancel obligation (`erwp_frame_plain`). Core inducts on `ewpTS`'s least fixed point;
  here the induction is on the index. Core's `ewp_frame_plain_or` has a table beside (a tick at a
  `Div` row); a `Div` row is a row of the chain's table (E13), so there is none.
* **W9** (Core's `wpTS_val_post`): a value's run at `erwp` stops at once, so the postcondition
  holds at the run's own configuration (`erwp_val_post`).

`erwp_frame_plain` asks the world condition of the stop's share to pass to its parts
(`hwl`, `hFe`): the chain's stops are resumed along `wc` (`extF` at a row's entries), where
Core's are resumed along `Ext`, whose `Ext.left`/`Ext.right` are those two premises.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Kont performE raiseE cancelVal opPayload)

/-! ### A cancel run under a plain context -/

/-- The cancel obligations of `T`'s capturable entries carry through a plain context, which holds
no handler and catches no cancel, beside no frame (Core's `OpTab.PlainCancel`). -/
def OpTabN.PlainCancel (T : OpTabN) : Prop :=
  ∀ n i en, T n i = some en → en.abort = false → en.q ≠ .lin →
    ∀ K : Kont, (∀ m, K.HasHnd m = false) → K.Catches 0 = false →
      ∀ k ls K₁ ρ, cancelOKN en k ls K₁ ρ → cancelOKN en k ls (K.comp K₁) ρ

/-- **A cancel run under a plain context** `K`, beside a frame `σ` holding nothing owned, and
nothing at all where the run may stop at an unrestricted operation (Core's `cancel_frame`): the
cancel's end leaves the context and the frame behind; a stop at an operation keeps both in its
continuation, whose own cancel carries through `K` (`hK`). -/
theorem cancelOblN_frame {Φ : LocFam} (hΦ : Φ.Down) {T : OpTabN} (K : Kont)
    (hH : ∀ n, K.HasHnd n = false) (hC : K.Catches 0 = false) {σ : WRes} (hσ : NoOwn σ)
    (hU : ∀ n i en, T n i = some en → en.abort = false → en.q = .unr → σ = PMap.empty)
    (hwl : ∀ n i en, T n i = some en → ∀ ls ls' ρ ρ', ResU.CompS ρ σ ρ' → en.wc ls ls' ρ' →
      en.wc ls ls' ρ)
    (hK : ∀ n i en, T n i = some en → en.abort = false → en.q ≠ .lin →
      ∀ k ls K₁ ρ ρ', cancelOKN en k ls K₁ ρ → ResU.CompS ρ σ ρ' →
        cancelOKN en k ls (K.comp K₁) ρ') :
    ∀ n ls e ρ, cancelOblN (ℍ := ℍ) Φ T n ls e ρ → ∀ ρ', ResU.CompS ρ σ ρ' →
      cancelOblN (ℍ := ℍ) Φ T n ls (K.plug e) ρ' := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ls e ρ h ρ' hc
  have h' : erwp (ℍ := ℍ) Φ (cancelTabN T) (fun _ _ _ _ => False) n ls e ρ := h
  show erwp (ℍ := ℍ) Φ (cancelTabN T) (fun _ _ _ _ => False) n ls (K.plug e) ρ'
  rw [erwp_eq] at h' ⊢
  refine rwpG_bind hΦ K ?_
  refine rwpG_mono_le (fun k hk ls' t τ ⟨τ₁, τ₂, hcτ, hp, hτ₂⟩ => ?_)
    (rwpG_frame (fun _ τ => τ = σ) (fun _ _ _ _ h => h) hc h' rfl)
  subst hτ₂
  rcases hp with ⟨_, _, hv⟩ | ⟨K', err, hs'⟩ | ⟨K₁, m, i, v, en, hp⟩
  · exact hv.elim
  · -- the cancel's end: the context and the frame are left behind
    obtain ⟨⟨rfl, hK'⟩, τa, τb, hcab, he, hnb⟩ := pure_sep_iff.mp hs'
    have hKo : (K.comp K').Catches 0 = false := by rw [catches_comp, hC, hK']; rfl
    have ht' : K.plug (K'.plug (raiseE (.val (cancelVal err)))) =
        (K.comp K').plug (opE true (cancelVal err)) := by
      rw [Kont.plug_comp]; rfl
    rw [ht']
    obtain ⟨z, hz, hcz⟩ := compS_reassoc hcab hcτ
    exact rwpG_here (final_opPlug (payloadName_cancelVal err) hKo) (Or.inr (Or.inl
      ⟨K.comp K', err, pure_sep_mk ⟨rfl, hKo⟩ ⟨τa, z, hcz, he, noOwn_compS hz hnb hσ⟩⟩))
  · -- an operation: the context and the frame join its continuation
    obtain ⟨⟨rfl, hK₁, hT₁, ha⟩, ρa, ρk, hcak, hA, hu, hcont⟩ := pure_sep_iff.mp hp
    obtain ⟨ρk', hk', hcσ'⟩ := compS_reassoc hcak hcτ
    have hKo : (K.comp K₁).HasHnd m = false := by rw [hasHnd_comp, hH, hK₁]; rfl
    have ht' : K.plug (K₁.plug (performE (.val (opPayload m i v)))) =
        (K.comp K₁).plug (opE false (opPayload m i v)) := by
      rw [Kont.plug_comp]; rfl
    rw [ht']
    refine rwpG_here (final_opPlug (payloadName_opPayload m i v) hKo) (Or.inr (Or.inr
      ⟨K.comp K₁, m, i, v, en, pure_sep_mk ⟨rfl, hKo, hT₁, ha⟩ ⟨ρa, ρk', hcσ', hA,
        fun hq => ?_, fun ls'' he => ⟨fun k' hk'' w τa' τb' hB hcτ' => ?_, fun hq P hP => ?_⟩⟩⟩))
    · rw [hu hq, hU m i en hT₁ ha hq] at hk'
      exact eq_of_compS_empty_left hk'
    · obtain ⟨z, hz, hcz⟩ := compS_exch hk' hcτ'
      have h₁ := (hcont ls'' (hwl m i en hT₁ ls' ls'' ρk ρk' hk' he)).1 k' hk'' w τa' z hB hz
      simp only [erwpC, show k' < n by omega, if_true] at h₁ ⊢
      rw [Kont.plug_comp]
      exact ih k' (by omega) ls'' _ z h₁ τb' hcz
    · exact hK m i en hT₁ ha hq k ls'' K₁ ρk ρk'
        (fun P hP => (hcont ls'' (hwl m i en hT₁ ls' ls'' ρk ρk' hk' he)).2 hq P hP) hk' P hP

/-- **A frame left behind by a cancel run under a plain context** (Core's
`cancel_frame_consume`): the frame `σ`, holding nothing owned, is garbage (`erwp_garbage`), and
the run goes on under `K` beside no frame, the nested cancels carried through `K` by
`T.PlainCancel`. -/
theorem cancelOblN_frame_consume {Φ : LocFam} (hΦ : Φ.Down) {T : OpTabN} (K : Kont)
    (hH : ∀ n, K.HasHnd n = false) (hC : K.Catches 0 = false) (hPC : T.PlainCancel)
    {σ : WRes} (hσ : NoOwn σ) {n : Nat} {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : cancelOblN (ℍ := ℍ) Φ T n ls e ρ) {ρ' : WRes} (hc : ResU.CompS ρ σ ρ') :
    cancelOblN (ℍ := ℍ) Φ T n ls (K.plug e) ρ' := by
  refine erwp_garbage hc hσ ?_
  refine cancelOblN_frame hΦ K hH hC noOwn_empty (fun _ _ _ _ _ _ => rfl)
    (fun _ _ _ _ _ _ ρ₁ ρ₁' hc₁ he => by
      rw [ResU.CompS.functional hc₁ (ResU.comp_empty_right ρ₁)] at he; exact he)
    (fun m i en hT ha hq k ls₁ K₁ ρ₁ ρ₁' hcan hc₁ => by
      rw [ResU.CompS.functional hc₁ (ResU.comp_empty_right ρ₁)]
      exact hPC m i en hT ha hq K hH hC k ls₁ K₁ ρ₁ hcan) n ls e ρ h ρ
    (ResU.comp_empty_right ρ)

/-! ### A plain frame around an effectful computation -/

/-- **A plain frame around an effectful computation** (Core's `ewp_frame_plain`). `K` holds no
handler and catches nothing (`M to x. N`'s `(λx. N) [·]`); the frame `Fr` (the context of `N`) is
carried through every stop of the computation in the hole: resumed with it, at an abortive stop
left behind, holding nothing owned (`hW`), and at a cancel carried through `K` by the entry's
cancel obligation (`hK`). At an unrestricted operation the frame is empty (`hU`). -/
theorem erwp_frame_plain {Φ : LocFam} (hΦ : Φ.Down) (T : OpTabN) (K : Kont)
    (hH : ∀ n, K.HasHnd n = false) (hC : ∀ n, K.Catches n = false) (Fr : List SRec → WProp)
    (hFs : ∀ ls ls', (∀ x, x ∈ ls' ↔ x ∈ ls) → ∀ ρ, Fr ls ρ → Fr ls' ρ)
    (hwl : ∀ n i en, T n i = some en → ∀ ls ls' ρ σ ρ', ResU.CompS ρ σ ρ' → en.wc ls ls' ρ' →
      en.wc ls ls' ρ)
    (hFe : ∀ n i en, T n i = some en → ∀ ls ls' ρ σ ρ', ResU.CompS ρ σ ρ' → en.wc ls ls' ρ' →
      Fr ls σ → Fr ls' σ)
    (hW : ∀ n i en, T n i = some en → en.abort = true → ∀ ls ρ, Fr ls ρ → NoOwn ρ)
    (hU : ∀ n i en, T n i = some en → en.q = .unr → ∀ ls ρ, Fr ls ρ → ρ = PMap.empty)
    (hK : ∀ n i en, T n i = some en → en.abort = false → en.q ≠ .lin →
      ∀ k ls K₁ ρ σ ρ', cancelOKN en k ls K₁ ρ → Fr ls σ → ResU.CompS ρ σ ρ' →
        cancelOKN en k ls (K.comp K₁) ρ')
    (Q₁ Q : PostN)
    (hkv : ∀ k ls (v : Val) ρ, (Q₁ k ls v ⋆ Fr ls) ρ →
      erwp (ℍ := ℍ) Φ (opTableN T) Q k ls (K.plug v.1) ρ) :
    ∀ n ls e ρ, erwp (ℍ := ℍ) Φ (opTableN T) Q₁ n ls e ρ →
      ∀ ρ₂ ρ', Fr ls ρ₂ → ResU.CompS ρ ρ₂ ρ' →
        erwp (ℍ := ℍ) Φ (opTableN T) Q n ls (K.plug e) ρ' := by
  have hL := opTableN_local T
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ls e ρ h ρ₂ ρ' hF hc
  rw [erwp_eq] at h ⊢
  refine rwpG_bind hΦ K ?_
  refine rwpG_mono_le (fun k hk ls' t σ ⟨σ₁, σ₂, hcσ, hp, hF'⟩ => ?_)
    (rwpG_frame Fr hFs hc h hF)
  rcases hp with ⟨v, rfl, hv⟩ | ⟨K₁, m, i, v, en, hp⟩ | ⟨K₁, m, i, v, en, hp⟩
  · exact erwp_unfold_at hL hk (hkv k ls' v σ ⟨σ₁, σ₂, hcσ, hv, hF'⟩)
  · -- a `perform`: the frame joins the continuation's share
    obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρk, hcak, hA, hu, hcont⟩ := pure_sep_iff.mp hp
    obtain ⟨ρk', hk', hcσ'⟩ := compS_reassoc hcak hcσ
    have hKo : (K.comp K₁).HasHnd m = false := by rw [hasHnd_comp, hH, hK₁]; rfl
    have ht' : K.plug (K₁.plug (performE (.val (opPayload m i v)))) =
        (K.comp K₁).plug (opE false (opPayload m i v)) := by
      rw [Kont.plug_comp]; rfl
    rw [ht']
    refine rwpG_here (final_opPlug (payloadName_opPayload m i v) hKo) (Or.inr (Or.inl
      ⟨K.comp K₁, m, i, v, en, pure_sep_mk ⟨rfl, hKo, hT, ha⟩ ⟨ρa, ρk', hcσ', hA,
        fun hq => ?_, fun ls'' he => ⟨fun k' hk'' w τ₁ τ₂ hB hcτ => ?_, fun hq P hP => ?_⟩⟩⟩))
    · rw [hu hq, hU m i en hT hq ls' σ₂ hF'] at hk'
      exact eq_of_compS_empty_left hk'
    · obtain ⟨z, hz, hcz⟩ := compS_exch hk' hcτ
      have h₁ := (hcont ls'' (hwl m i en hT ls' ls'' ρk σ₂ ρk' hk' he)).1 k' hk'' w τ₁ z hB hz
      simp only [erwpC, show k' < n by omega, if_true] at h₁ ⊢
      rw [Kont.plug_comp]
      exact ih k' (by omega) ls'' _ z h₁ σ₂ τ₂ (hFe m i en hT ls' ls'' ρk σ₂ ρk' hk' he hF') hcz
    · exact hK m i en hT ha hq k ls'' K₁ ρk σ₂ ρk'
        (fun P hP => (hcont ls'' (hwl m i en hT ls' ls'' ρk σ₂ ρk' hk' he)).2 hq P hP)
        (hFe m i en hT ls' ls'' ρk σ₂ ρk' hk' he hF') hk' P hP
  · -- a `raise`: the frame is left behind
    obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρn, hcan, ⟨hPA, hnA⟩, hn⟩ := pure_sep_iff.mp hp
    obtain ⟨ρn', hn', hcσ'⟩ := compS_reassoc hcan hcσ
    have hKo : (K.comp K₁).Catches m = false := by rw [catches_comp, hC, hK₁]; rfl
    have ht' : K.plug (K₁.plug (raiseE (.val (opPayload m i v)))) =
        (K.comp K₁).plug (opE true (opPayload m i v)) := by
      rw [Kont.plug_comp]; rfl
    rw [ht']
    exact rwpG_here (final_opPlug (payloadName_opPayload m i v) hKo) (Or.inr (Or.inr
      ⟨K.comp K₁, m, i, v, en, pure_sep_mk ⟨rfl, hKo, hT, ha⟩ ⟨ρa, ρn', hcσ', ⟨hPA, hnA⟩,
        noOwn_compS hn' hn (hW m i en hT ha ls' σ₂ hF')⟩⟩))

/-! ### A value read off its run -/

/-- **A value's run stops at once** (Core's `wpTS_val_post`): at a run's configuration, the
postcondition holds at the value, at a list with the same members. -/
theorem erwp_val_post {Φ : LocFam} {T : OpTabN} {Q : PostN} {n : Nat} (hn : 0 < n)
    {ls : List SRec} {v : Val} {ρ ρf fρ : WRes} {ps : List FrameRec} {μ : Heap}
    (h : erwp (ℍ := ℍ) Φ (opTableN T) Q n ls v.1 ρ) (hf : ResU.Hash ρf ρ)
    (hc : ResU.CompS ρf ρ fρ) (hT : TWNC fρ ps (rsOf ls)) (htg : Tagged fρ ps ls)
    (hI : ImmTieL Φ.imm ls) (hl : ResU.Lower fρ μ) (hfd : FinDom μ) :
    ∃ ls' ρ', (∀ x, x ∈ ls' ↔ x ∈ ls) ∧ Q n ls' v ρ' := by
  rw [erwp_eq] at h
  obtain ⟨ρ', -, -, -, -, -, ls', -, -, -, -, -, -, -, -, -, -, -, hls, hq⟩ :=
    h ρf fρ ps μ hf hc hT htg hI hl hfd 0 μ v.1 hn (.refl _ _) (final_val μ v)
  rcases hq with ⟨w, hw, hq⟩ | ⟨K, m, i, u, en, hp⟩ | ⟨K, m, i, u, en, hp⟩
  · obtain rfl : w = v := Subtype.ext hw.symm
    exact ⟨ls', ρ', hls, hq⟩
  · have ht := (pure_sep_iff.mp hp).1.1
    have hval : IsVal (K.plug (performE (.val (opPayload m i u)))) := ht ▸ v.2
    exact absurd (K.isVal_of_plug hval) (by simp [performE])
  · have ht := (pure_sep_iff.mp hp).1.1
    have hval : IsVal (K.plug (raiseE (.val (opPayload m i u)))) := ht ▸ v.2
    exact absurd (K.isVal_of_plug hval) (by simp [raiseE])

end BoCa.Fig16.LogRel.Core.Chain.SI

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Kont performE raiseE cancelVal opPayload)

/-- **A cancel run under a plain context, at a cancel row's table, beside no frame** (Core's
`plain_cancel₀`): `cancelOblN_frame`, the nested cancels carried through the context by Core's
recursion on the cancel row. -/
theorem cancelOblN_plain₀ {δ : LSub} {Θ : LocTy} {c : Loc → Option Life}
    (hΦ : (Θ.view c).Down) (K : Kont) (hH : ∀ n, K.HasHnd n = false) (hC : K.Catches 0 = false)
    (G : CTy) :
    ∀ {n : Nat} {ls : List SRec} {e : Expr} {ρ : WRes},
      cancelOblN (ℍ := ℍ) (Θ.view c) (tabN (ℍ := ℍ) G δ Θ c) n ls e ρ →
      cancelOblN (ℍ := ℍ) (Θ.view c) (tabN (ℍ := ℍ) G δ Θ c) n ls (K.plug e) ρ := by
  intro n ls e ρ h
  refine cancelOblN_frame hΦ K hH hC noOwn_empty (fun _ _ _ _ _ _ => rfl)
    (fun _ _ _ _ _ _ ρ₁ ρ₁' hc₁ he => by
      rw [ResU.CompS.functional hc₁ (ResU.comp_empty_right ρ₁)] at he; exact he)
    ?_ n ls e ρ h ρ (ResU.comp_empty_right ρ)
  intro m i en hT ha hq k ls₁ K₁ ρ₁ ρ₁' hcan hc₁ P hP
  rw [ResU.CompS.functional hc₁ (ResU.comp_empty_right ρ₁)]
  rw [tabN_rowOf] at hT
  obtain ⟨o, hf, rfl⟩ := tabN_effOf_some_find hT
  have hP' := hP
  simp only [entN] at hP'
  split at hP'
  · rw [finN_eq_ite] at hP'
    split at hP'
    · cases hP'
    · cases hP'
      show cancelOblN (ℍ := ℍ) _ _ k ls₁ ((K.comp K₁).dead.plug _) ρ₁
      rw [dead_comp, dead_plain K hH hC, Kont.plug_comp]
      exact cancelOblN_plain₀ hΦ K hH hC o.fin (hcan _ hP)
  · cases hP'
termination_by sizeOf G
decreasing_by exact rowOf_fin_lt G (Row.find_mem hf).1

/-- **A row's table carries its cancel obligations through a plain context with no frame**
(Core's `Row.tab_plainCancel`). -/
theorem tabN_plainCancel {δ : LSub} {Θ : LocTy} {c : Loc → Option Life} (hΦ : (Θ.view c).Down)
    (G : CTy) : (tabN (ℍ := ℍ) G δ Θ c).PlainCancel := by
  intro m i en hT _ _ K hH hC k ls K₁ ρ hcan P hP
  rw [tabN_rowOf] at hT
  obtain ⟨o, -, rfl⟩ := tabN_effOf_some_find hT
  have hP' := hP
  simp only [entN] at hP'
  split at hP'
  · rw [finN_eq_ite] at hP'
    split at hP'
    · cases hP'
    · cases hP'
      show cancelOblN (ℍ := ℍ) _ _ k ls ((K.comp K₁).dead.plug _) ρ
      rw [dead_comp, dead_plain K hH hC, Kont.plug_comp]
      exact cancelOblN_plain₀ hΦ K hH hC o.fin (hcan _ hP)
  · cases hP'

/-- **An entry's cancel obligation under a plain context, beside a frame holding nothing owned**
(Core's `ent_plain`): the frame is left behind (`cancelOblN_frame_consume`). -/
theorem entN_plain {δ : LSub} {Θ : LocTy} {c : Loc → Option Life} (hΦ : (Θ.view c).Down)
    (K : Kont) (hH : ∀ n, K.HasHnd n = false) (hC : K.Catches 0 = false) {σ : WRes}
    (hσ : NoOwn σ) (o : OpSig) {k : Nat} {ls : List SRec} {K₁ : Kont} {ρ ρ' : WRes}
    (hcan : cancelOKN (entN o.q o.B (fun k v ρ => vN (ℍ := ℍ) o.A δ Θ k v ρ)
      (fun k v ρ => vN (ℍ := ℍ) o.B δ Θ k v ρ) (finN (ℍ := ℍ) o.fin δ Θ c)) k ls K₁ ρ)
    (hc : ResU.CompS ρ σ ρ') :
    cancelOKN (entN o.q o.B (fun k v ρ => vN (ℍ := ℍ) o.A δ Θ k v ρ)
      (fun k v ρ => vN (ℍ := ℍ) o.B δ Θ k v ρ) (finN (ℍ := ℍ) o.fin δ Θ c)) k ls (K.comp K₁) ρ' := by
  intro P hP
  have hP' := hP
  simp only [entN] at hP'
  split at hP'
  · rw [finN_eq_ite] at hP'
    split at hP'
    · cases hP'
    · cases hP'
      show cancelOblN (ℍ := ℍ) _ _ k ls ((K.comp K₁).dead.plug _) ρ'
      rw [dead_comp, dead_plain K hH hC, Kont.plug_comp]
      exact cancelOblN_frame_consume hΦ K hH hC (tabN_plainCancel hΦ o.fin) hσ (hcan _ hP) hc
  · cases hP'

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
