import DivEffect.Handle

/-!
# DivEffect — `[then]` at a row holding `Div`  (§4.1, unknown 1, item 1)

`M then x. N unwind D`, `M` and `N` at a row holding `Div`, the finaliser `D` at its own row
without it.  The finaliser frame `ubind (N, D) [·]` is carried through each segment by
`ewp_frame_then_or`, which is Core's `ewp_frame_then` (`Core/EffFin.lean`) at `opTable T ∨ Π`:
its proof verbatim, with one more case, a stop of `Π` (the tick), which the frame joins.  `tick`
is linear, so a tick's continuation has no cancel, and the frame is only resumed with it.

`Closing`'s half is Core's `ewp_frame_then` itself, at the rows with the closing tick in front
(`closing_row`).  `cwp_then` is by coinduction up to `cwp`, the candidate the frame around a
computation of `cwp`, as `cwp_bind`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.DivEffect
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont Step1N performE raiseE opPayload hndE hndVal
  kappaC kappaCell kappaAt clauseAt capTag freeE)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- **`ewp_frame_then` at `opTable T ∨ Π`**: Core's proof, and a stop of `Π`, which the frame
joins (`hPx`). -/
theorem ewp_frame_then_or (δ : LSub) (S SM SD : Row) (hNZ : S.NZ) (hMS : RowLe SM S)
    (hDS : RowLe SD S)
    (hfin : ∀ n i o o', Row.find SM n i = some o → Row.find S n i = some o' →
      capB o.q o.B = true → ThenLe o.fin SD o'.fin)
    (hP : SD.UnrD → SM.PendPers) (Nv Dv : Val) (Fr : List SRec → WProp)
    (hFs : ∀ ls ls', (∀ x, x ∈ ls' ↔ x ∈ ls) → Entails (Fr ls) (Fr ls'))
    (hFe : ∀ ls ls' ρ, Ext ls ls' ρ → Fr ls ρ → Fr ls' ρ)
    (hU : S.UnrD → ∀ ls ρ, Fr ls ρ → ρ = PMap.empty)
    {Qd : List SRec → Val → WProp} (hQd : ∀ ls v ρ, Qd ls v ρ → v = .unit ∧ NoOwn ρ)
    (hD : ∀ ls, Entails (Fr ls)
      (ewpTS ls (.app (.val Dv) (.val .unit)) (opTable (Row.tab SD δ)) Qd))
    (Px Px' : Table) (hPx' : Table.Mono Px')
    (hPx : ∀ ls t Φ Φ' σ₁ σ₂ σ, Px ls t Φ σ₁ → Fr ls σ₂ → ResU.CompS σ₁ σ₂ σ →
      Px' ls ((ubindK Nv Dv).plug t) Φ' σ)
    (Q₁ Q : List SRec → Val → WProp)
    (hk : ∀ ls v, Entails (Q₁ ls v ⋆ Fr ls)
      (ewpTS ls ((ubindK Nv Dv).plug (.val v)) (orTab (opTable (Row.tab S δ)) Px') Q)) :
    ∀ {ls : List SRec} {e : Expr} {ρ : WRes}, ewpTS ls e (orTab (opTable (Row.tab SM δ)) Px) Q₁ ρ →
      ∀ {ρ₂ ρ' : WRes}, Fr ls ρ₂ → ResU.CompS ρ ρ₂ ρ' →
        ewpTS ls ((ubindK Nv Dv).plug e) (orTab (opTable (Row.tab S δ)) Px') Q ρ' := by
  have hM' := orTab_mono (opTable_mono (Row.tab S δ)) hPx'
  have hNZD : ∀ n i o, Row.find SD n i = some o → o.n ≠ 0 := by
    intro n i o hf
    obtain ⟨o', hf', hle⟩ := hDS n i o hf
    rw [hle.1.1]; exact hNZ o' (Row.find_mem hf').1
  intro ls e ρ h
  refine ewp_ind (fun ls e ρ => ∀ {ρ₂ ρ' : WRes}, Fr ls ρ₂ → ResU.CompS ρ ρ₂ ρ' →
    ewpTS ls ((ubindK Nv Dv).plug e) (orTab (opTable (Row.tab S δ)) Px') Q ρ') ?_ h
  intro ls e ρ hs ρ₂ ρ' hF hc
  refine ewp_fold hM' (wpG_bind (ubindK Nv Dv) e ls _ ρ' ?_)
  have h₁ := wpG_frame (e := e) Fr (hFs ls) ρ' ⟨ρ, ρ₂, hc, hs, hF⟩
  refine wpG_mono (fun ls' t σ ht => ?_) h₁
  obtain ⟨σ₁, σ₂, hcσ, hp, hF'⟩ := ht
  rcases hp with ⟨v, rfl, hv⟩ | hp | hp
  · exact ewp_unfold hM' (hk ls' v σ ⟨σ₁, σ₂, hcσ, hv, hF'⟩)
  swap
  · -- a stop of the extra table: the frame joins it
    exact wpG_here _ _ _ σ (Or.inr (Or.inr (hPx ls' t _ _ σ₁ σ₂ σ hp hF' hcσ)))
  rcases hp with ⟨K₁, n, i, v, en, hp⟩ | ⟨K₁, n, i, v, en, hp⟩
  · -- a `perform`: the frame joins the continuation's share; its cancel fires `D`
    refine wpG_here _ _ _ σ (Or.inr (Or.inl ?_))
    obtain ⟨⟨rfl, hK₁, hTn, ha⟩, ρa, ρk, hcak, hA, hu, hcont⟩ := pure_sep_iff.mp hp
    obtain ⟨o, hf, rfl⟩ := Row.tab_some hTn
    obtain ⟨o', hf', hle⟩ := hMS n i o hf
    obtain ⟨ρk', hk', hcσ'⟩ := compS_reassoc hcak hcσ
    refine Or.inl ⟨(ubindK Nv Dv).comp K₁, n, i, v, o'.ent δ,
      pure_sep_mk ⟨(Kont.plug_comp _ _ _).symm, ?_, Row.tab_find hf',
        (show o'.abort = false by rw [← hle.1.abort_eq]; exact ha)⟩
      ⟨ρa, ρk', hcσ', by simpa only [OpSig.ent, hle.1.2.2.2.1] using hA, ?_,
        fun ls'' he => ⟨?_, fun hq => ?_⟩⟩⟩
    · rw [hasHnd_comp, hK₁]; simp [Kont.HasHnd, Expr.val, Val.pair]
    · intro hq
      have hq' : o.q = .unr := by rw [hle.1.2.2.1]; exact hq
      rw [hu hq', hU ⟨o', (Row.find_mem hf').1, Or.inl hq⟩ ls' σ₂ hF'] at hk'
      exact eq_of_compS_empty_left hk'
    · intro w τ₁ τ₂ hB hcτ
      obtain ⟨z, hz, hcz⟩ := compS_exch hk' hcτ
      rw [Kont.plug_comp]
      have hB' : (o.ent δ).PB ls'' w τ₁ := by simpa only [OpSig.ent, hle.1.2.2.2.2] using hB
      exact (hcont ls'' (he.left hk')).1 w τ₁ z hB' hz (hFe ls' ls'' σ₂ (he.right hk') hF') hcz
    · intro Q' hQ'
      obtain ⟨hcap', hnT, rfl⟩ := ent_fin_some hQ'
      have hcap : capB o.q o.B = true := hle.1.capB_eq ▸ hcap'
      have hth := hfin n i o o' hf hf' hcap
      have hoT : o.fin.isTop = false := by
        rw [ThenLe, hnT] at hth
        exact (hth.resolve_left (by simp)).1
      have hcan := (hcont ls'' (he.left hk')).2 (not_lin_of_capB hcap)
        (cancelObl (Row.tab o.fin.rowOf δ)) (by rw [OpSig.ent_fin, if_pos hcap, finObl_eq, hoT]; rfl)
      show cancelObl _ ls'' (((ubindK Nv Dv).comp K₁).dead.plug _) ρk'
      rw [dead_comp, dead_ubindK, Kont.plug_comp]
      exact then_cancel δ SD hNZD Nv Dv Fr hFs hFe (fun _ _ _ h => (hQd _ _ _ h).2) hD o.fin hth hnT
        (fun hu₁ => hU ⟨o', (Row.find_mem hf').1, Or.inr ⟨hcap', hu₁⟩⟩)
        (fun hu₁ => ((hP hu₁) o (Row.find_mem hf).1).2 hcap) hcan
        (hFe ls' ls'' σ₂ (he.right hk') hF') hk'
  · -- a `raise`: the finaliser runs, then the `raise` goes on
    obtain ⟨⟨rfl, hK₁, hTn, ha⟩, ρa, ρn, hcan, ⟨hPA, hnA⟩, hn⟩ := pure_sep_iff.mp hp
    obtain ⟨o, hf, rfl⟩ := Row.tab_some hTn
    obtain ⟨o', hf', hle⟩ := hMS n i o hf
    have hn0 : n ≠ 0 := by
      rw [← (Row.find_mem hf).2.1, hle.1.1]; exact hNZ o' (Row.find_mem hf').1
    refine wpG_head (fun μ => Head.ufin μ Nv Dv n i v K₁ hn0 hK₁) rfl _ _ σ (ewp_unfold
      hM' (ewp_mono hM' (fun _ _ _ _ h => Or.inl h) (fun _ _ _ h => h) ?_))
    obtain ⟨z, hz, hcz⟩ := compS_reassoc hcan hcσ
    obtain ⟨y, hy, hcy⟩ := compS_lcomm hz hcz
    refine ewp_absorb (opTable_mono _) ?_ hn (ResU.CompS.comm hcy)
    have hPA' : (o'.ent δ).PA ls' v ρa := by simpa only [OpSig.ent, hle.1.2.2.2.1] using hPA
    exact seq_raise_run δ S SD hDS (Row.tab_find hf')
      (show o'.abort = true by rw [← hle.1.abort_eq]; exact ha) hQd (hD ls' σ₂ hF') ⟨hPA', hnA⟩
      (fun hu => vP_empty_of_persistent (((hP hu) o (Row.find_mem hf).1).1 ha) hPA)
      (ResU.CompS.comm hy)

/-! ### Compatibility of `[sub]`, `[perform]`, `[raise]`, `[let]` and `[then]` -/


/-! ### Rows with the closing tick in front -/

theorem find_close (d : UInt32) (S : Row) (n i : UInt32) :
    Row.find (closeSig d :: S) n i = if n = d ∧ i = 0 then some (closeSig d) else Row.find S n i := by
  by_cases h : n = d ∧ i = 0
  · rw [if_pos h]; simp [Row.find, List.find?, closeSig, h]
  · rw [if_neg h]
    have : decide (n = (closeSig d).n ∧ i = (closeSig d).i) = false := by
      simp only [closeSig]; exact decide_eq_false h
    simp [Row.find, List.find?, this]

theorem find_without {S : Row} {d : UInt32} (hS : Row.Without S d) {n i : UInt32} {o : OpSig}
    (h : Row.find S n i = some o) : n ≠ d := by
  obtain ⟨hm, rfl, -⟩ := Row.find_mem h
  exact hS o hm

theorem rowLe_close {S S' : Row} {d : UInt32} (hS : Row.Without S d) (h : RowLe S S') :
    RowLe (closeSig d :: S) (closeSig d :: S') := by
  intro n i o hf
  rw [find_close] at hf ⊢
  by_cases hn : n = d ∧ i = 0
  · rw [if_pos hn] at hf ⊢; cases hf; exact ⟨_, rfl, OpSig.LeF.refl _⟩
  · rw [if_neg hn] at hf ⊢; exact h n i o hf

theorem rowLe_close_right {S S' : Row} {d : UInt32} (hS : Row.Without S d) (h : RowLe S S') :
    RowLe S (closeSig d :: S') := by
  intro n i o hf
  rw [find_close, if_neg (fun hn => find_without hS hf hn.1)]
  exact h n i o hf

theorem without_of_le {S S' : Row} {d : UInt32} (hS' : Row.Without S' d) (h : RowLe S S') :
    Row.Without S d := by
  intro o ho hd
  have hf : ∃ o₀, Row.find S o.n o.i = some o₀ := by
    cases hf : Row.find S o.n o.i with
    | some o₀ => exact ⟨o₀, rfl⟩
    | none =>
        exfalso
        simp only [Row.find, List.find?_eq_none] at hf
        exact hf o ho (by simp)
  obtain ⟨o₀, hf⟩ := hf
  obtain ⟨o', hf', -⟩ := h _ _ _ hf
  exact find_without hS' hf' hd

/-! ### `[then]` at `cwp` -/

section
variable {δ : LSub} {d : UInt32} {S SM SD : Row} (hSd : Row.Without S d) (hd0 : d ≠ 0)
  (hNZ : S.NZ) (hMS : RowLe SM S) (hDS : RowLe SD S)
  (hfin : ∀ n i o o', Row.find SM n i = some o → Row.find S n i = some o' →
    capB o.q o.B = true → ThenLe o.fin SD o'.fin)
  (hP : SD.UnrD → SM.PendPers) (Nv Dv : Val) (Fr : List SRec → WProp)
  (hFs : ∀ ls ls', (∀ x, x ∈ ls' ↔ x ∈ ls) → Entails (Fr ls) (Fr ls'))
  (hFe : ∀ ls ls' ρ, Ext ls ls' ρ → Fr ls ρ → Fr ls' ρ)
  (hU : S.UnrD → ∀ ls ρ, Fr ls ρ → ρ = PMap.empty)
  {Qd : List SRec → Val → WProp} (hQd : ∀ ls v ρ, Qd ls v ρ → v = .unit ∧ NoOwn ρ)
  (hD : ∀ ls, Entails (Fr ls)
    (ewpTS ls (.app (.val Dv) (.val .unit)) (opTable (Row.tab SD δ)) Qd))
  (Q₁ Q : List SRec → Val → WProp)

include hSd hd0 hNZ hMS hDS hfin hP hFs hFe hU hQd hD in
/-- **`Closing` under the finaliser frame**: Core's `ewp_frame_then` at the closing rows. -/
theorem closing_then
    (hk : ∀ ls v, Entails (Q₁ ls v ⋆ Fr ls) (Closing δ d (Row.tab S δ) Q ls ((ubindK Nv Dv).plug (.val v))))
    {ls : List SRec} {e : Expr} {ρ : WRes} (h : Closing δ d (Row.tab SM δ) Q₁ ls e ρ)
    {ρ₂ ρ' : WRes} (hF : Fr ls ρ₂) (hc : ResU.CompS ρ ρ₂ ρ') :
    Closing δ d (Row.tab S δ) Q ls ((ubindK Nv Dv).plug e) ρ' := by
  have hSMd := without_of_le hSd hMS
  unfold Closing at h hk ⊢
  rw [closing_row] at h hk ⊢
  refine ewp_frame_then δ (closeSig d :: S) (closeSig d :: SM) SD ?_ (rowLe_close hSMd hMS)
    (rowLe_close_right (without_of_le hSd hDS) hDS) ?_ ?_ Nv Dv Fr hFs hFe ?_ hQd hD Q₁ Q hk h hF hc
  · intro o ho
    simp only [List.mem_cons] at ho
    rcases ho with rfl | ho
    · exact hd0
    · exact hNZ o ho
  · intro n i o o' hf hf' hcap
    rw [find_close] at hf hf'
    by_cases hn : n = d ∧ i = 0
    · rw [if_pos hn] at hf; cases hf; exact absurd hcap (by simp [closeSig, capB, OpSig.abort])
    · rw [if_neg hn] at hf hf'; exact hfin n i o o' hf hf' hcap
  · intro hu o ho
    simp only [List.mem_cons] at ho
    rcases ho with rfl | ho
    · exact ⟨fun h => absurd h (by simp [closeSig, capB, OpSig.abort]), fun h => absurd h (by simp [closeSig, capB, OpSig.abort])⟩
    · exact hP hu o ho
  · rintro ⟨o, ho, hu⟩
    simp only [List.mem_cons] at ho
    rcases ho with rfl | ho
    · rcases hu with hu | ⟨hcap, -⟩
      · cases hu
      · exact absurd hcap (by simp [closeSig, capB, OpSig.abort])
    · exact hU ⟨o, ho, hu⟩

include hSd hd0 hNZ hMS hDS hfin hP hFs hFe hU hQd hD in
/-- **`[then]` at `cwp`**, by coinduction up to `cwp`: each segment is `ewp_frame_then_or`; a
tick inside the frame owes the frame around its continuation, in the candidate and, by
`closing_then`, in `Closing`. -/
theorem cwp_then
    (hk : ∀ ls v, Entails (Q₁ ls v ⋆ Fr ls) (cwp δ d (Row.tab S δ) Q ls ((ubindK Nv Dv).plug (.val v))))
    {ls : List SRec} {e : Expr} {ρ : WRes} (h : cwp δ d (Row.tab SM δ) Q₁ ls e ρ)
    {ρ₂ ρ' : WRes} (hF : Fr ls ρ₂) (hc : ResU.CompS ρ ρ₂ ρ') :
    cwp δ d (Row.tab S δ) Q ls ((ubindK Nv Dv).plug e) ρ' := by
  have hTd := Row.tab_without hSd δ 0
  have hcl := fun {ls e ρ} (h : Closing δ d (Row.tab SM δ) Q₁ ls e ρ) {ρ₂ ρ'} (hF : Fr ls ρ₂)
      (hc : ResU.CompS ρ ρ₂ ρ') =>
    closing_then hSd hd0 hNZ hMS hDS hfin hP Nv Dv Fr hFs hFe hU hQd hD Q₁ Q
      (fun ls v σ hσ => closing_of_cwp hTd (hk ls v σ hσ)) h hF hc
  let W : CPred := fun ls x ρ' => ∃ e ρ ρ₂, x = (ubindK Nv Dv).plug e ∧
    cwp δ d (Row.tab SM δ) Q₁ ls e ρ ∧ Fr ls ρ₂ ∧ ResU.CompS ρ ρ₂ ρ'
  have hW' : W.Le (cwpF δ d (Row.tab S δ) Q (fun ls e ρ => W ls e ρ ∨ cwp δ d (Row.tab S δ) Q ls e ρ)) := by
    rintro ls x ρ' ⟨e, ρ, ρ₂, rfl, he, hF, hc⟩
    refine ewp_frame_then_or δ S SM SD hNZ hMS hDS hfin hP Nv Dv Fr hFs hFe hU hQd hD _ _
      (Table.Const.mono (tickStop_const δ d _)) ?_ Q₁ Q
      (fun ls v σ hσ => cwpF_mono (fun _ _ _ h => Or.inr h) _ _ σ (cwp_out _ _ σ (hk ls v σ hσ)))
      (cwp_out ls e ρ he) hF hc
    intro ls' t Φ Φ' σ₁ σ₂ σ hp hF' hcσ
    obtain ⟨K₁, n, i, v, en, hp⟩ := hp
    obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρk, hcak, hA, hu, hcont⟩ := pure_sep_iff.mp hp
    obtain ⟨ρk', hk', hcσ'⟩ := compS_reassoc hcak hcσ
    obtain ⟨rfl, rfl, rfl⟩ := tickT_some hT
    refine ⟨(ubindK Nv Dv).comp K₁, n, 0, v, tickEnt δ n,
      pure_sep_mk ⟨(Kont.plug_comp _ _ _).symm, ?_, hT, ha⟩
      ⟨ρa, ρk', hcσ', hA, And.intro (fun h => nomatch h) (fun ls'' he => And.intro
        (fun w τ₁ τ₂ hB hcτ => ?_) (fun h => absurd rfl h))⟩⟩
    · rw [hasHnd_comp, hK₁]; simp [Kont.HasHnd, Expr.val, Val.pair]
    · obtain ⟨z, hz, hcz⟩ := compS_exch hk' hcτ
      have ho := (hcont ls'' (he.left hk')).1 w τ₁ z hB hz
      have hF'' := hFe ls' ls'' σ₂ (he.right hk') hF'
      rw [Kont.plug_comp]
      exact ⟨Or.inl ⟨_, z, σ₂, rfl, ho.1, hF'', hcz⟩, hcl ho.2 hF'' hcz⟩
  exact cwp_coind_up hW' ls _ ρ' ⟨e, ρ, ρ₂, rfl, h, hF, hc⟩

end

/-- **`[then]`** at a row holding `Div`: `then_compatC`'s premises, `M` and `N` at `SemD`, the
finaliser at its own row without `Div`. -/
theorem then_compatD {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {M N D : Expr} {A B : VTy} {d : UInt32}
    {S SM SD : Row} (hSd : Row.Without S d) (hd0 : d ≠ 0)
    (hsp : Ctx.SplitP Γ Γ₁ Γ₂) (hNZ : S.NZ) (hU : S.UnrD → Persistent Γ₂)
    (hMS : RowLe SM S) (hDS : RowLe SD S)
    (hfin : ∀ n i o o', Row.find SM n i = some o → Row.find S n i = some o' →
      capB o.q o.B = true → ThenLe o.fin SD o'.fin)
    (hP : SD.UnrD → SM.PendPers)
    (hM : SemD Δ Γ₁ M d SM A) (hN : SemD Δ (⟨A, true⟩ :: Γ₂) N d S B)
    (hD : SemC Δ (⟨.unit, false⟩ :: Γ₂) D (CTy.effOf SD .unit)) :
    SemD Δ Γ (thenE N D M) d S B := by
  intro δ γ ls ρ hδ hg
  obtain ⟨ρ₁, ρ₂, hc, hg₁, hg₂⟩ := gDenC_split hsp hg
  change cwp δ d _ _ ls ((ubindK (Val.lam (Expr.psub 1 γ N)) (Val.lam (Expr.psub 1 γ D))).plug
    (substAll γ M)) ρ
  refine cwp_then hSd hd0 hNZ hMS hDS hfin hP _ _
    (fun ls => gDenC ls δ Γ₂ γ) (fun _ _ hs σ h => gDenC_same hs h)
    (fun _ _ _ he h => gDenC_local he h)
    (fun hu _ _ h => gDenC_persistent (hU hu) h) (Qd := fun ls v => vC true .unit ls δ v) ?_ ?_
    (fun ls v => vC true A ls δ v) _ ?_ (hM δ γ ls ρ₁ hδ hg₁) hg₂ hc
  · intro ls' v σ h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, noOwn_empty⟩
  · intro ls' σ h
    refine ewp_step (opTable_mono _)
      (fun μ => Step1N.head (Head.beta μ (Expr.psub 1 γ D) Val.unit) rfl) ls' _ σ ?_
    rw [← substAll_cons_psub]
    exact (cC_effOf SD .unit ls' δ _ σ).mp
      (hD δ (Val.unit :: γ) ls' σ hδ (gDenC_dead_cons .unit Val.unit h))
  · rintro ls' v σ ⟨σ₁, σ₂, hcσ, hv, hg₂'⟩
    obtain ⟨hlen, hgs⟩ := gDenC_iff.mp hg₂'
    refine cwp_roll _ _ _ (ewp_step (divTab_mono δ _ _ _ _)
      (fun μ => Step1N.head (Head.uthen μ _ _ v) rfl) ls' _ σ ?_)
    refine ewp_step (divTab_mono δ _ _ _ _)
      (fun μ => Step1N.head (Head.beta μ (Expr.psub 1 γ N) v) rfl) ls' _ σ ?_
    rw [← substAll_cons_psub]
    exact cwp_out _ _ _
      (hN δ (v :: γ) ls' σ hδ (gDenC_mk (by simpa using hlen) ⟨σ₁, σ₂, hcσ, hv, hgs⟩))

end BoCa.Fig16.LogRel.Core.DivEffect

end
