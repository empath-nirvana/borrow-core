import DivEffect.Defs

/-!
# DivEffect — a frame around a segment, and bind at `cwp`  (§4.1, unknown 1, item 1: `[let]`)

`ewp_frame_plain` (`Core/EffRules.lean`) carries a plain frame through every stop of a computation
at `opTable T`.  A segment's table has one more kind of stop, the tick, which owes nothing to the
segment's least fixed point (`divTab`).  `ewp_frame_plain_or` is `ewp_frame_plain` at
`opTable T ∨ Px`, for any such extra table `Px`: the frame joins `Px`'s stop as its hypothesis `hPx`
says, and every other case is `ewp_frame_plain`'s.

`cwp_bind` is then bind at the greatest fixed point, by coinduction with the candidate "a frame
around a computation of `cwp`": a tick inside the frame owes the frame around its continuation,
which is in the candidate.  `Closing`'s half is `ewp_frame_plain` itself.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.DivEffect
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont Step1N performE raiseE opPayload hndE hndVal)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- Two tables, either of which may stop the run. -/
def orTab (A B : Table) : Table := fun ls t Φ => BoLo.or (A ls t Φ) (B ls t Φ)

theorem orTab_mono {A B : Table} (hA : A.Mono) (hB : B.Mono) : (orTab A B).Mono := by
  intro ls t Φ Φ' ρ hΦ h
  rcases h with h | h
  · exact Or.inl (hA ls t Φ Φ' ρ hΦ h)
  · exact Or.inr (hB ls t Φ Φ' ρ hΦ h)

/-- A table that owes nothing to the run's least fixed point. -/
def Table.Const (Px : Table) : Prop := ∀ ls t Φ Φ' ρ, Px ls t Φ ρ → Px ls t Φ' ρ

theorem Table.Const.mono {Px : Table} (h : Table.Const Px) : Px.Mono :=
  fun ls t Φ Φ' ρ _ hp => h ls t Φ Φ' ρ hp

/-- The tick's stop, owing `Φ₀`. -/
def tickStop (δ : LSub) (d : UInt32) (Φ₀ : CPred) : Table :=
  fun ls t _ => performStop (tickT δ d) ls t Φ₀

theorem tickStop_const (δ : LSub) (d : UInt32) (Φ₀ : CPred) : Table.Const (tickStop δ d Φ₀) :=
  fun _ _ _ _ _ h => h

theorem divTab_eq (δ : LSub) (d : UInt32) (T : OpTab) (Q : List SRec → Val → WProp) (W : CPred) :
    divTab δ d T Q W = orTab (opTable T) (tickStop δ d (owe δ d T Q W)) := rfl

/-- **`ewp_frame_plain` at `opTable T ∨ Px`.**  The plain frame `K` with `Fr` around a run at
`opTable T ∨ Px` is a run at `opTable T ∨ Px'`, where `Px`'s stops with the frame are `Px'`'s
(`hPx`). -/
theorem ewp_frame_plain_or (T : OpTab) (Px Px' : Table) (hPx' : Table.Mono Px') (K : Kont)
    (hH : ∀ n, K.HasHnd n = false)
    (hC : ∀ n, K.Catches n = false) (Fr : List SRec → WProp)
    (hFs : ∀ ls ls', (∀ x, x ∈ ls' ↔ x ∈ ls) → Entails (Fr ls) (Fr ls'))
    (hFe : ∀ ls ls' ρ, Ext ls ls' ρ → Fr ls ρ → Fr ls' ρ)
    (hW : ∀ n i en, T n i = some en → en.abort = true → ∀ ls ρ, Fr ls ρ → NoOwn ρ)
    (hU : ∀ n i en, T n i = some en → en.q = .unr → ∀ ls ρ, Fr ls ρ → ρ = PMap.empty)
    (hK : ∀ n i en, T n i = some en → en.abort = false → en.q ≠ .lin →
      ∀ ls K₁ ρ σ ρ', cancelOK en ls K₁ ρ → Fr ls σ → ResU.CompS ρ σ ρ' →
        cancelOK en ls (K.comp K₁) ρ')
    (hPx : ∀ ls t Φ Φ' σ₁ σ₂ σ, Px ls t Φ σ₁ → Fr ls σ₂ → ResU.CompS σ₁ σ₂ σ →
      Px' ls (K.plug t) Φ' σ)
    (Q₁ Q : List SRec → Val → WProp)
    (hk : ∀ ls v, Entails (Q₁ ls v ⋆ Fr ls) (ewpTS ls (K.plug (.val v)) (orTab (opTable T) Px') Q)) :
    ∀ {ls : List SRec} {e : Expr} {ρ : WRes}, ewpTS ls e (orTab (opTable T) Px) Q₁ ρ →
      ∀ {ρ₂ ρ' : WRes}, Fr ls ρ₂ → ResU.CompS ρ ρ₂ ρ' →
        ewpTS ls (K.plug e) (orTab (opTable T) Px') Q ρ' := by
  have hM := orTab_mono (opTable_mono T) hPx'
  intro ls e ρ h
  refine ewp_ind (fun ls e ρ => ∀ {ρ₂ ρ' : WRes}, Fr ls ρ₂ → ResU.CompS ρ ρ₂ ρ' →
    ewpTS ls (K.plug e) (orTab (opTable T) Px') Q ρ') ?_ h
  intro ls e ρ hs ρ₂ ρ' hF hc
  refine ewp_fold hM (wpG_bind K e ls _ ρ' ?_)
  have h₁ := wpG_frame (e := e) Fr (hFs ls) ρ' ⟨ρ, ρ₂, hc, hs, hF⟩
  refine wpG_mono (fun ls' t σ ht => ?_) h₁
  obtain ⟨σ₁, σ₂, hcσ, hp, hF'⟩ := ht
  rcases hp with ⟨v, rfl, hv⟩ | hp | hp
  · exact ewp_unfold hM (hk ls' v σ ⟨σ₁, σ₂, hcσ, hv, hF'⟩)
  · refine wpG_here _ _ _ σ (Or.inr (Or.inl ?_))
    rcases hp with ⟨K₁, n, i, v, en, hp⟩ | ⟨K₁, n, i, v, en, hp⟩
    · -- a `perform`: the frame joins the continuation's share
      obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρk, hcak, hA, hu, hcont⟩ := pure_sep_iff.mp hp
      obtain ⟨ρk', hk', hcσ'⟩ := compS_reassoc hcak hcσ
      refine Or.inl ⟨K.comp K₁, n, i, v, en, pure_sep_mk ⟨(Kont.plug_comp _ _ _).symm, ?_, hT, ha⟩
        ⟨ρa, ρk', hcσ', hA, ?_, fun ls'' he => ⟨?_, fun hq => ?_⟩⟩⟩
      · rw [hasHnd_comp, hH, hK₁]; rfl
      · intro hq
        rw [hu hq, hU n i en hT hq ls' σ₂ hF'] at hk'
        exact eq_of_compS_empty_left hk'
      · intro w τ₁ τ₂ hB hcτ
        obtain ⟨z, hz, hcz⟩ := compS_exch hk' hcτ
        rw [Kont.plug_comp]
        exact (hcont ls'' (he.left hk')).1 w τ₁ z hB hz (hFe ls' ls'' σ₂ (he.right hk') hF') hcz
      · exact hK n i en hT ha hq ls'' K₁ ρk σ₂ ρk' ((hcont ls'' (he.left hk')).2 hq)
          (hFe ls' ls'' σ₂ (he.right hk') hF') hk'
    · -- a `raise`: the frame is left behind
      obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρn, hcan, hA, hn⟩ := pure_sep_iff.mp hp
      obtain ⟨ρn', hn', hcσ'⟩ := compS_reassoc hcan hcσ
      refine Or.inr ⟨K.comp K₁, n, i, v, en, pure_sep_mk ⟨(Kont.plug_comp _ _ _).symm, ?_, hT, ha⟩
        ⟨ρa, ρn', hcσ', hA, noOwn_compS hn' hn (hW n i en hT ha ls' σ₂ hF')⟩⟩
      rw [catches_comp, hC, hK₁]; rfl
  · -- a stop of the extra table: the frame joins it
    exact wpG_here _ _ _ σ (Or.inr (Or.inr (hPx ls' t _ _ σ₁ σ₂ σ hp hF' hcσ)))

/-- A lookup in a table extended by one entry. -/
theorem ext_some {d n i : UInt32} {en en' : OpEnt} {T : OpTab}
    (h : OpTab.ext d 0 en T n i = some en') : (n = d ∧ i = 0 ∧ en' = en) ∨ T n i = some en' := by
  unfold OpTab.ext at h
  by_cases hn : n = d ∧ i = 0
  · rw [if_pos hn] at h; exact Or.inl ⟨hn.1, hn.2, (Option.some.inj h).symm⟩
  · rw [if_neg hn] at h; exact Or.inr h

/-- The frame conditions of `ewp_frame_plain` at `T`, carried to `T` with a linear entry. -/
theorem frame_conds_ext {T : OpTab} {d : UInt32} {en₀ : OpEnt} (h₀ : en₀.q = .lin)
    (ha₀ : en₀.abort = false) (K : Kont) (Fr : List SRec → WProp)
    (hW : ∀ n i en, T n i = some en → en.abort = true → ∀ ls ρ, Fr ls ρ → NoOwn ρ)
    (hU : ∀ n i en, T n i = some en → en.q = .unr → ∀ ls ρ, Fr ls ρ → ρ = PMap.empty)
    (hK : ∀ n i en, T n i = some en → en.abort = false → en.q ≠ .lin →
      ∀ ls K₁ ρ σ ρ', cancelOK en ls K₁ ρ → Fr ls σ → ResU.CompS ρ σ ρ' →
        cancelOK en ls (K.comp K₁) ρ') :
    (∀ n i en, OpTab.ext d 0 en₀ T n i = some en → en.abort = true → ∀ ls ρ, Fr ls ρ → NoOwn ρ) ∧
    (∀ n i en, OpTab.ext d 0 en₀ T n i = some en → en.q = .unr → ∀ ls ρ, Fr ls ρ →
      ρ = PMap.empty) ∧
    (∀ n i en, OpTab.ext d 0 en₀ T n i = some en → en.abort = false → en.q ≠ .lin →
      ∀ ls K₁ ρ σ ρ', cancelOK en ls K₁ ρ → Fr ls σ → ResU.CompS ρ σ ρ' →
        cancelOK en ls (K.comp K₁) ρ') := by
  refine ⟨fun n i en h => ?_, fun n i en h => ?_, fun n i en h => ?_⟩
  · rcases ext_some h with ⟨-, -, rfl⟩ | h
    · intro ha; rw [ha₀] at ha; cases ha
    · exact hW n i en h
  · rcases ext_some h with ⟨-, -, rfl⟩ | h
    · intro hq; rw [h₀] at hq; cases hq
    · exact hU n i en h
  · rcases ext_some h with ⟨-, -, rfl⟩ | h
    · intro _ hq; exact absurd h₀ hq
    · exact hK n i en h

/-- **A plain frame around a computation of `cwp`, one segment**, at any target candidate `Y`
that holds the frame around every computation of `cwp` (`hY`): the segment is
`ewp_frame_plain_or`, and a tick inside the frame owes the frame around its continuation, which
is in `Y`, and in `Closing` by `ewp_frame_plain` at the closing table. -/
theorem cwpF_frame {δ : LSub} {d : UInt32} {T : OpTab} (hTd : T d 0 = none) (K : Kont)
    (hH : ∀ n, K.HasHnd n = false)
    (hC : ∀ n, K.Catches n = false) (Fr : List SRec → WProp)
    (hFs : ∀ ls ls', (∀ x, x ∈ ls' ↔ x ∈ ls) → Entails (Fr ls) (Fr ls'))
    (hFe : ∀ ls ls' ρ, Ext ls ls' ρ → Fr ls ρ → Fr ls' ρ)
    (hW : ∀ n i en, T n i = some en → en.abort = true → ∀ ls ρ, Fr ls ρ → NoOwn ρ)
    (hU : ∀ n i en, T n i = some en → en.q = .unr → ∀ ls ρ, Fr ls ρ → ρ = PMap.empty)
    (hK : ∀ n i en, T n i = some en → en.abort = false → en.q ≠ .lin →
      ∀ ls K₁ ρ σ ρ', cancelOK en ls K₁ ρ → Fr ls σ → ResU.CompS ρ σ ρ' →
        cancelOK en ls (K.comp K₁) ρ')
    (Q₁ Q : List SRec → Val → WProp) (Y : CPred)
    (hY : ∀ ls e ρ ρ₂ ρ', cwp δ d T Q₁ ls e ρ → Fr ls ρ₂ → ResU.CompS ρ ρ₂ ρ' →
      Y ls (K.plug e) ρ')
    (hk : ∀ ls v, Entails (Q₁ ls v ⋆ Fr ls) (cwpF δ d T Q Y ls (K.plug (.val v))))
    (hkc : ∀ ls v, Entails (Q₁ ls v ⋆ Fr ls) (Closing δ d T Q ls (K.plug (.val v)))) :
    ∀ {ls : List SRec} {e : Expr} {ρ : WRes}, cwp δ d T Q₁ ls e ρ →
      ∀ {ρ₂ ρ' : WRes}, Fr ls ρ₂ → ResU.CompS ρ ρ₂ ρ' → cwpF δ d T Q Y ls (K.plug e) ρ' := by
  obtain ⟨hWc, hUc, hKc⟩ := frame_conds_ext (en₀ := closeEnt δ d) (d := d) rfl rfl K Fr hW hU hK
  have hcl : ∀ {ls : List SRec} {e : Expr} {ρ : WRes}, Closing δ d T Q₁ ls e ρ →
      ∀ {ρ₂ ρ' : WRes}, Fr ls ρ₂ → ResU.CompS ρ ρ₂ ρ' → Closing δ d T Q ls (K.plug e) ρ' :=
    fun h => ewp_frame_plain _ K hH hC Fr hFs hFe hWc hUc hKc Q₁ Q hkc h
  intro ls e ρ he ρ₂ ρ' hF hc
  refine ewp_frame_plain_or T _ _ (Table.Const.mono (tickStop_const δ d _)) K hH hC Fr hFs hFe
    hW hU hK ?_ Q₁ Q hk (cwp_out ls e ρ he) hF hc
  intro ls' t Φ Φ' σ₁ σ₂ σ hp hF' hcσ
  obtain ⟨K₁, n, i, v, en, hp⟩ := hp
  obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρk, hcak, hA, hu, hcont⟩ := pure_sep_iff.mp hp
  obtain ⟨ρk', hk', hcσ'⟩ := compS_reassoc hcak hcσ
  obtain ⟨rfl, rfl, rfl⟩ := tickT_some hT
  refine ⟨K.comp K₁, n, 0, v, tickEnt δ n, pure_sep_mk ⟨(Kont.plug_comp _ _ _).symm, ?_, hT, ha⟩
    ⟨ρa, ρk', hcσ', hA, And.intro (fun h => nomatch h) (fun ls'' he => And.intro
      (fun w τ₁ τ₂ hB hcτ => ?_) (fun h => absurd rfl h))⟩⟩
  · rw [hasHnd_comp, hH, hK₁]; rfl
  · obtain ⟨z, hz, hcz⟩ := compS_exch hk' hcτ
    have ho := (hcont ls'' (he.left hk')).1 w τ₁ z hB hz
    have hF'' := hFe ls' ls'' σ₂ (he.right hk') hF'
    rw [Kont.plug_comp]
    exact ⟨hY _ _ z σ₂ τ₂ ho.1 hF'' hcz, hcl ho.2 hF'' hcz⟩

/-- **`[let]` and bind at `cwp`.**  A plain frame `K` with `Fr` around a computation of `cwp` at
`Q₁`, every answer of which the frame continues at `cwp` at `Q`, is at `cwp` at `Q`: by
coinduction up to `cwp`, the candidate the frame around a computation of `cwp`, one segment at a
time (`cwpF_frame`).  `[spec §19]` -/
theorem cwp_bind {δ : LSub} {d : UInt32} {T : OpTab} (hTd : T d 0 = none) (K : Kont)
    (hH : ∀ n, K.HasHnd n = false)
    (hC : ∀ n, K.Catches n = false) (Fr : List SRec → WProp)
    (hFs : ∀ ls ls', (∀ x, x ∈ ls' ↔ x ∈ ls) → Entails (Fr ls) (Fr ls'))
    (hFe : ∀ ls ls' ρ, Ext ls ls' ρ → Fr ls ρ → Fr ls' ρ)
    (hW : ∀ n i en, T n i = some en → en.abort = true → ∀ ls ρ, Fr ls ρ → NoOwn ρ)
    (hU : ∀ n i en, T n i = some en → en.q = .unr → ∀ ls ρ, Fr ls ρ → ρ = PMap.empty)
    (hK : ∀ n i en, T n i = some en → en.abort = false → en.q ≠ .lin →
      ∀ ls K₁ ρ σ ρ', cancelOK en ls K₁ ρ → Fr ls σ → ResU.CompS ρ σ ρ' →
        cancelOK en ls (K.comp K₁) ρ')
    (Q₁ Q : List SRec → Val → WProp)
    (hk : ∀ ls v, Entails (Q₁ ls v ⋆ Fr ls) (cwp δ d T Q ls (K.plug (.val v)))) :
    ∀ {ls : List SRec} {e : Expr} {ρ : WRes}, cwp δ d T Q₁ ls e ρ →
      ∀ {ρ₂ ρ' : WRes}, Fr ls ρ₂ → ResU.CompS ρ ρ₂ ρ' → cwp δ d T Q ls (K.plug e) ρ' := by
  let W : CPred := fun ls x ρ' => ∃ e ρ ρ₂, x = K.plug e ∧ cwp δ d T Q₁ ls e ρ ∧ Fr ls ρ₂ ∧
    ResU.CompS ρ ρ₂ ρ'
  have hW' : W.Le (cwpF δ d T Q (fun ls e ρ => W ls e ρ ∨ cwp δ d T Q ls e ρ)) := by
    rintro ls x ρ' ⟨e, ρ, ρ₂, rfl, he, hF, hc⟩
    exact cwpF_frame hTd K hH hC Fr hFs hFe hW hU hK Q₁ Q _
      (fun ls e ρ ρ₂ ρ' he hF hc => Or.inl ⟨e, ρ, ρ₂, rfl, he, hF, hc⟩)
      (fun ls v σ hσ => cwpF_mono (fun _ _ _ h => Or.inr h) _ _ σ (cwp_out _ _ σ (hk ls v σ hσ)))
      (fun ls v σ hσ => closing_of_cwp hTd (hk ls v σ hσ)) he hF hc
  intro ls e ρ he ρ₂ ρ' hF hc
  exact cwp_coind_up hW' ls _ ρ' ⟨e, ρ, ρ₂, rfl, he, hF, hc⟩

end BoCa.Fig16.LogRel.Core.DivEffect

end
