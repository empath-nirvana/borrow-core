import Core.Compat

/-!
# Core — the effect rules' semantics  `[spec §19]`

Rows `Σ` are lists of operations (`OpSig`); `F_Σ R` is `CTy.effOf Σ R`, whose relation is
`ewpTS` at the operation table of `Σ` (`cC_effOf`). This file proves the effectful `wp`'s rules
the typing rules of §19 need:

* `ewp_perform_here`, `ewp_raise_here`: an operation stops at once, owing its continuation;
* `ewp_sub`: a row may grow (`opTable_le`);
* `ewp_let`: `M to x. N` at a row, the frame of `N` carried through every stop of `M`: resumed with
  it, or, at a cancel or an abortive stop, dropped (it holds nothing owned);
* `ewp_then`: the same with a finaliser, which runs at a cancel and at an abortive stop;
* `ewp_handle`: a handler, by induction on the inner computation's least fixed point.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore Step1N performE raiseE opPayload
  cancelVal hndE ubindE ccatchE cfinE hndVal kappa clauseAt errNext)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### Rows -/

/-- A row: the operations a computation may perform.  `[spec §19]` -/
abbrev Row := List OpSig

/-- The operation `i` of the name `n` in a row, first match. -/
def Row.find (S : Row) (n i : UInt32) : Option OpSig :=
  S.find? fun o => decide (n = o.n ∧ i = o.i)

/-- An operation is abortive: answer `0` at a qualifier with weakening. -/
def OpSig.abort (o : OpSig) : Bool := o.B.isZero && o.q != .lin

/-- The entry of an operation at `δ`. -/
def OpSig.ent (δ : LSub) (o : OpSig) : OpEnt :=
  ⟨o.q, o.abort, fun ls v => vC true o.A ls δ v, fun ls v => vC true o.B ls δ v⟩

/-- The operation table of a row at `δ`. -/
def Row.tab (S : Row) (δ : LSub) : OpTab := fun n i => (Row.find S n i).map (OpSig.ent δ)

theorem effTab_effOf (δ : LSub) : ∀ (S : Row) (R : VTy), effTab (CTy.effOf S R) δ = Row.tab S δ
  | [], R => by
      funext n i; simp [CTy.effOf, effTab, OpTab.empty, Row.tab, Row.find]
  | o :: S, R => by
      funext n i
      simp only [CTy.effOf, effTab, OpTab.ext, effTab_effOf δ S R]
      by_cases h : n = o.n ∧ i = o.i
      · simp [h, Row.tab, Row.find, List.find?, OpSig.ent, OpSig.abort]
      · rw [if_neg h]
        simp [Row.tab, Row.find, List.find?, h]

theorem effRet_effOf (δ : LSub) : ∀ (S : Row) (R : VTy),
    effRet (CTy.effOf S R) δ = fun ls v => vC true R ls δ v
  | [], R => by simp [CTy.effOf, effRet]
  | _ :: S, R => by simp only [CTy.effOf, effRet]; exact effRet_effOf δ S R

/-- The empty table's protocol admits nothing. -/
theorem opTable_empty {ls : List SRec} {t : Expr} {Φ : List SRec → Expr → WProp} {ρ : WRes}
    (h : opTable OpTab.empty ls t Φ ρ) : False := by
  rcases h with ⟨_, _, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ <;>
    exact absurd (pure_sep_iff.mp h).1.2.2.1 (by simp [OpTab.empty])

/-- **The relation at a row** is `ewpTS` at the row's table; at the empty row it is `wpTS`
(`ewp_bot`).  `[spec §19]` -/
theorem cC_effOf (S : Row) (R : VTy) (ls : List SRec) (δ : LSub) (e : Expr) (ρ : WRes) :
    cC (CTy.effOf S R) ls δ e ρ ↔
      ewpTS ls e (opTable (Row.tab S δ)) (fun ls v => vC true R ls δ v) ρ := by
  cases S with
  | nil =>
      have hT : Row.tab [] δ = OpTab.empty := by
        funext n i; simp [Row.tab, Row.find, OpTab.empty]
      rw [hT]
      show wpTS ls e _ ρ ↔ _
      constructor
      · intro h; exact ewp_of_wp (opTable_mono _) h
      · intro h
        exact ewp_bot.mp (ewp_mono (fun _ _ _ _ _ _ h => h)
          (fun _ _ _ _ h => (opTable_empty h).elim) (fun _ _ _ h => h) h)
  | cons o S =>
      have h := effTab_effOf δ (o :: S) R
      have hr := effRet_effOf δ (o :: S) R
      simp only [CTy.effOf] at h hr
      simp only [CTy.effOf, cC]
      rw [show OpTab.ext o.n o.i ⟨o.q, o.B.isZero && o.q != .lin, fun ls v => vCE none true o.A ls δ v,
          fun ls v => vCE none true o.B ls δ v⟩ (effTab (CTy.effOf S R) δ) = Row.tab (o :: S) δ from h,
        show effRet (CTy.effOf S R) δ = _ from hr]

/-! ### Stopping at an operation -/

/-- A `perform` stops at once; its continuation (the hole) answers `Q` at every answer in `PB`,
and its cancel run ends at once.  `[spec §19]` -/
theorem ewp_perform_here {T : OpTab} {n i : UInt32} {en : OpEnt} (hT : T n i = some en)
    (ha : en.abort = false) {ls : List SRec} {v : Val} {Q : List SRec → Val → WProp}
    (hQ : ∀ ls' w ρ, en.PB ls' w ρ → Q ls' w ρ) {ρ : WRes} (h : en.PA ls v ρ) :
    ewpTS ls (performE (.val (opPayload n i v))) (opTable T) Q ρ := by
  refine ewp_fold (opTable_mono T) (wpG_here _ _ _ ρ (Or.inr (Or.inl
    ⟨.hole, n, i, v, en, pure_sep_mk ⟨rfl, rfl, hT, ha⟩
      ⟨ρ, PMap.empty, ResU.comp_empty_right ρ, h, ?_⟩⟩)))
  refine ⟨fun _ => rfl, fun ls' _ => ⟨fun w σ₁ σ₂ hB hc => ?_, fun _ N _ _ => ?_⟩⟩
  · rw [eq_of_compS_empty_left hc]
    exact ewp_val (opTable_mono T) (hQ _ _ _ hB)
  · refine (ewp_abortive (cancelTab_abortive T N)).mpr (wpG_here _ _ _ _ (Or.inr ?_))
    exact ⟨.hole, none, pure_sep_mk ⟨rfl, rfl⟩
      ⟨PMap.empty, PMap.empty, ResU.comp_empty_right _, ⟨rfl, trivial⟩, noOwn_empty⟩⟩

/-- A `raise` stops at once, at an argument that holds nothing owned.  `[spec §19]` -/
theorem ewp_raise_here {T : OpTab} {n i : UInt32} {en : OpEnt} (hT : T n i = some en)
    (ha : en.abort = true) {ls : List SRec} {v : Val} {Q : List SRec → Val → WProp} {ρ : WRes}
    (h : en.PA ls v ρ) (hn : NoOwn ρ) :
    ewpTS ls (raiseE (.val (opPayload n i v))) (opTable T) Q ρ :=
  ewp_fold (opTable_mono T) (wpG_here _ _ _ ρ (Or.inr (Or.inr
    ⟨.hole, n, i, v, en, pure_sep_mk ⟨rfl, rfl, hT, ha⟩
      ⟨ρ, PMap.empty, ResU.comp_empty_right ρ, ⟨h, hn⟩, noOwn_empty⟩⟩)))

/-! ### Growing the row -/

/-- `T` is included in `T′`: every entry of `T` is `T′`'s. -/
def OpTab.Le (T T' : OpTab) : Prop := ∀ n i en, T n i = some en → T' n i = some en

theorem errOk_le {T T' : OpTab} (hT : T.Le T') {N : List UInt32} {ls : List SRec} :
    ∀ {err : Option Val} {ρ : WRes}, errOk T N ls err ρ → errOk T' N ls err ρ
  | none, _, h => h
  | some _, _, ⟨m, j, w, en, h⟩ => by
      obtain ⟨⟨h₁, h₂, h₃, h₄⟩, h₅⟩ := pure_sep_iff.mp h
      exact ⟨m, j, w, en, pure_sep_mk ⟨h₁, h₂, hT _ _ _ h₃, h₄⟩ h₅⟩

theorem cancelTab_le {T T' : OpTab} (hT : T.Le T') {N : List UInt32} {ls : List SRec} {t : Expr}
    {Φ Φ' : List SRec → Expr → WProp} {ρ : WRes} (h : cancelTab T N ls t Φ ρ) :
    cancelTab T' N ls t Φ' ρ := by
  obtain ⟨K, err, h⟩ := h
  obtain ⟨hp, ρ₁, ρ₂, hc, he, hn⟩ := pure_sep_iff.mp h
  exact ⟨K, err, pure_sep_mk hp ⟨ρ₁, ρ₂, hc, errOk_le hT he, hn⟩⟩

theorem cancelOwed_le {T T' : OpTab} (hT : T.Le T') {n : UInt32} {ls : List SRec} {K : Kont}
    {ρ : WRes} (h : cancelOwed T n ls K ρ) : cancelOwed T' n ls K ρ :=
  fun N hn hK => ewp_mono (cancelTab_abortive T' N).mono (fun _ _ _ _ h => cancelTab_le hT h)
    (fun _ _ _ h => h) (h N hn hK)

/-- The protocol table grows with the operation table. -/
theorem opTable_le {T T' : OpTab} (hT : T.Le T') {ls : List SRec} {t : Expr}
    {Φ : List SRec → Expr → WProp} {ρ : WRes} (h : opTable T ls t Φ ρ) : opTable T' ls t Φ ρ := by
  rcases h with ⟨K, n, i, v, en, h⟩ | ⟨K, n, i, v, en, h⟩
  · obtain ⟨⟨h₁, h₂, h₃, h₄⟩, ρ₁, ρ₂, hc, hA, hu, hk⟩ := pure_sep_iff.mp h
    exact Or.inl ⟨K, n, i, v, en, pure_sep_mk ⟨h₁, h₂, hT _ _ _ h₃, h₄⟩
      ⟨ρ₁, ρ₂, hc, hA, hu, fun ls' he => ⟨(hk ls' he).1,
        fun hq => cancelOwed_le hT ((hk ls' he).2 hq)⟩⟩⟩
  · obtain ⟨⟨h₁, h₂, h₃, h₄⟩, h₅⟩ := pure_sep_iff.mp h
    exact Or.inr ⟨K, n, i, v, en, pure_sep_mk ⟨h₁, h₂, hT _ _ _ h₃, h₄⟩ h₅⟩

/-- **A row may grow** (`[sub]`).  `[spec §19]` -/
theorem ewp_sub {T T' : OpTab} (hT : T.Le T') {ls : List SRec} {e : Expr}
    {Q : List SRec → Val → WProp} {ρ : WRes} (h : ewpTS ls e (opTable T) Q ρ) :
    ewpTS ls e (opTable T') Q ρ :=
  ewp_mono (opTable_mono T') (fun _ _ _ _ h => opTable_le hT h) (fun _ _ _ h => h) h

/-! ### A frame around a stopped computation -/

/-- A cancel run under a context that catches nothing: the context and a frame holding nothing
owned are left behind at the cancel's end. -/
theorem cancel_frame {T T' : OpTab} {N : List UInt32} (K : Kont) (hK : K.Catches 0 = false)
    (hT : ∀ ls err ρ, errOk T N ls err ρ → errOk T' N ls err ρ)
    {ls : List SRec} {e : Expr} {ρ σ ρ' : WRes}
    (h : ewpTS ls e (cancelTab T N) (fun _ _ _ => False) ρ) (hσ : NoOwn σ)
    (hc : ResU.CompS ρ σ ρ') :
    ewpTS ls (K.plug e) (cancelTab T' N) (fun _ _ _ => False) ρ' := by
  refine (ewp_abortive (cancelTab_abortive T' N)).mpr ?_
  refine wpG_bind K e ls _ ρ' ?_
  have h₁ := wpG_frame (e := e) (Q := ewpPost (cancelTab T N) fun _ _ _ => False)
    (fun _ => fun τ => NoOwn τ) (fun _ _ _ h => h) ρ'
    ⟨ρ, σ, hc, (ewp_abortive (cancelTab_abortive T N)).mp h, hσ⟩
  refine wpG_mono (fun ls' t τ ht => ?_) h₁
  obtain ⟨τ₁, τ₂, hcτ, hp, hn⟩ := ht
  rcases hp with ⟨_, _, hv⟩ | ⟨K', err, hs⟩
  · exact hv.elim
  obtain ⟨⟨rfl, hK'⟩, τa, τb, hcab, he, hnb⟩ := pure_sep_iff.mp hs
  refine wpG_here _ _ _ τ (Or.inr ⟨K.comp K', err, pure_sep_mk ⟨(Kont.plug_comp _ _ _).symm, ?_⟩ ?_⟩)
  · rw [catches_comp, hK, hK']; rfl
  · obtain ⟨z, hz, hcz⟩ := compS_reassoc hcab hcτ
    exact ⟨τa, z, hcz, hT _ _ _ he, noOwn_compS hz hnb hn⟩

/-- **A plain frame around an effectful computation.**  `K` holds no handler and catches nothing
(`M to x. N`'s `(λx. N) [·]`); the frame `Fr` (the context of `N`) is carried through every stop
of the computation in the hole: resumed with it, and, at a cancel or an abortive stop, left
behind, holding nothing owned.  At an unrestricted operation the frame is empty.  `[spec §19]` -/
theorem ewp_frame_plain (T : OpTab) (K : Kont) (hH : ∀ n, K.HasHnd n = false)
    (hC : ∀ n, K.Catches n = false) (hN : K.hndNames = [])
    (Fr : List SRec → WProp)
    (hFs : ∀ ls ls', (∀ x, x ∈ ls' ↔ x ∈ ls) → Entails (Fr ls) (Fr ls'))
    (hFe : ∀ ls ls' ρ, Ext ls ls' ρ → Fr ls ρ → Fr ls' ρ)
    (hW : ∀ n i en, T n i = some en → (en.q ≠ .lin ∨ en.abort = true) →
      ∀ ls ρ, Fr ls ρ → NoOwn ρ)
    (hU : ∀ n i en, T n i = some en → en.q = .unr → ∀ ls ρ, Fr ls ρ → ρ = PMap.empty)
    (Q₁ Q : List SRec → Val → WProp)
    (hk : ∀ ls v, Entails (Q₁ ls v ⋆ Fr ls) (ewpTS ls (K.plug (.val v)) (opTable T) Q)) :
    ∀ {ls : List SRec} {e : Expr} {ρ : WRes}, ewpTS ls e (opTable T) Q₁ ρ →
      ∀ {ρ₂ ρ' : WRes}, Fr ls ρ₂ → ResU.CompS ρ ρ₂ ρ' →
        ewpTS ls (K.plug e) (opTable T) Q ρ' := by
  intro ls e ρ h
  refine ewp_ind (fun ls e ρ => ∀ {ρ₂ ρ' : WRes}, Fr ls ρ₂ → ResU.CompS ρ ρ₂ ρ' →
    ewpTS ls (K.plug e) (opTable T) Q ρ') ?_ h
  intro ls e ρ hs ρ₂ ρ' hF hc
  refine ewp_fold (opTable_mono T) (wpG_bind K e ls _ ρ' ?_)
  have h₁ := wpG_frame (e := e) Fr (hFs ls) ρ' ⟨ρ, ρ₂, hc, hs, hF⟩
  refine wpG_mono (fun ls' t σ ht => ?_) h₁
  obtain ⟨σ₁, σ₂, hcσ, hp, hF'⟩ := ht
  rcases hp with ⟨v, rfl, hv⟩ | hp
  · exact ewp_unfold (opTable_mono T) (hk ls' v σ ⟨σ₁, σ₂, hcσ, hv, hF'⟩)
  refine wpG_here _ _ _ σ (Or.inr ?_)
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
    · intro N hn hNK
      have hc' := (hcont ls'' (he.left hk')).2 hq N hn
        (fun m hm => hNK m (by rw [hndNames_comp, hN]; exact hm))
      rw [Kont.plug_comp]
      exact cancel_frame K (hC 0) (fun _ _ _ h => h) hc'
        (hW n i en hT (Or.inl hq) ls' σ₂ hF') hk'
  · -- a `raise`: the frame is left behind
    obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρn, hcan, hA, hn⟩ := pure_sep_iff.mp hp
    obtain ⟨ρn', hn', hcσ'⟩ := compS_reassoc hcan hcσ
    refine Or.inr ⟨K.comp K₁, n, i, v, en, pure_sep_mk ⟨(Kont.plug_comp _ _ _).symm, ?_, hT, ha⟩
      ⟨ρa, ρn', hcσ', hA, noOwn_compS hn' hn (hW n i en hT (Or.inr ha) ls' σ₂ hF')⟩⟩
    rw [catches_comp, hC, hK₁]; rfl

/-! ### Finalisers -/

/-- Every entry of `T` is abortive. -/
def OpTab.AbortOnly (T : OpTab) : Prop := ∀ n i en, T n i = some en → en.abort = true

/-- The entries' relations are Kripke: carried along `Ext`. -/
def OpTab.Local (T : OpTab) : Prop :=
  ∀ n i en, T n i = some en → ∀ ls ls' v ρ, Ext ls ls' ρ →
    (en.PA ls v ρ → en.PA ls' v ρ) ∧ (en.PB ls v ρ → en.PB ls' v ρ)

/-- At an abortive-only table no `perform` stops, and a `raise` owes nothing. -/
theorem opTable_abortive {T : OpTab} (hA : T.AbortOnly) : (opTable T).Abortive := by
  intro ls t Φ Φ' ρ h
  rcases h with ⟨K, n, i, v, en, h⟩ | h
  · obtain ⟨⟨-, -, hT, ha⟩, -⟩ := pure_sep_iff.mp h
    rw [hA n i en hT] at ha; exact absurd ha (by simp)
  · exact Or.inr h

theorem errOk_local {T : OpTab} (hL : T.Local) {N : List UInt32} {ls ls' : List SRec} {ρ : WRes}
    (he : Ext ls ls' ρ) : ∀ {err : Option Val}, errOk T N ls err ρ → errOk T N ls' err ρ
  | none, h => h
  | some _, ⟨m, j, w, en, h⟩ => by
      obtain ⟨⟨h₁, h₂, h₃, h₄⟩, hA, hn⟩ := pure_sep_iff.mp h
      obtain ⟨hρ, -⟩ := pure_sep_iff.mp h
      exact ⟨m, j, w, en, pure_sep_mk ⟨h₁, h₂, h₃, h₄⟩
        ⟨(hL m j en h₃ ls ls' w ρ he).1 hA, hn⟩⟩

/-- A cancel stop absorbs garbage. -/
theorem cancelTab_absorb {T : OpTab} {N : List UInt32} {ls : List SRec} {t : Expr}
    {Φ : List SRec → Expr → WProp} {ρ₁ ρ₂ ρ : WRes} (h : cancelTab T N ls t Φ ρ₁) (hn : NoOwn ρ₂)
    (hc : ResU.CompS ρ₁ ρ₂ ρ) : cancelTab T N ls t Φ ρ := by
  obtain ⟨K, err, h⟩ := h
  obtain ⟨hp, τa, τb, hcab, he, hnb⟩ := pure_sep_iff.mp h
  obtain ⟨z, hz, hcz⟩ := compS_reassoc hcab hc
  exact ⟨K, err, pure_sep_mk hp ⟨τa, z, hcz, he, noOwn_compS hz hnb hn⟩⟩

/-- **A finaliser under a cancel** (`cfin`).  `D ()` runs at an abortive-only row inside the
cancel's row; its answer holds nothing owned.  Its first error of a name outside the region is
kept in the cancel's state and the others are suppressed; then the cancel goes on.
`[spec §19]` -/
theorem ewp_cfin {T Ta : OpTab} (hA : Ta.AbortOnly) (hle : Ta.Le T) (hL : T.Local)
    {N : List UInt32} {err : Option Val} {ls : List SRec} {d : Expr}
    {Qd : List SRec → Val → WProp} (hQd : ∀ ls v ρ, Qd ls v ρ → NoOwn ρ) {ρd ρe ρ : WRes}
    (hD : ewpTS ls d (opTable Ta) Qd ρd) (he : errOk T N ls err ρe) (hc : ResU.CompS ρd ρe ρ) :
    ewpTS ls (cfinE (cancelVal N err) d) (cancelTab T N) (fun _ _ _ => False) ρ := by
  refine (ewp_abortive (cancelTab_abortive T N)).mpr ?_
  refine wpG_bind (.appR (.app (.val (.prim .cfin)) (.val (cancelVal N err))) .hole) d ls _ ρ ?_
  have h₁ := wpG_frame (e := d) (fun ls => errOk T N ls err)
    (fun ls' hs τ h => errOk_local hL (ext_of_same hs τ) h) ρ
    ⟨ρd, ρe, hc, (ewp_abortive (opTable_abortive hA)).mp hD, he⟩
  refine wpG_mono (fun ls' t σ ht => ?_) h₁
  obtain ⟨σ₁, σ₂, hcσ, hp, he'⟩ := ht
  rcases hp with ⟨w, rfl, hw⟩ | hp
  · -- the finaliser finished: the cancel goes on with its state
    refine wpG_head (fun μ => Head.cfret μ N err w) rfl _ _ σ ?_
    refine wpG_here _ _ _ σ (Or.inr ⟨.hole, err, pure_sep_mk ⟨rfl, rfl⟩
      ⟨σ₂, σ₁, ResU.CompS.comm hcσ, he', hQd _ _ _ hw⟩⟩)
  rcases hp with ⟨K, n, i, v, en, hp⟩ | ⟨K, m, j, w, en, hp⟩
  · obtain ⟨⟨-, -, hT, ha⟩, -⟩ := pure_sep_iff.mp hp
    rw [hA n i en hT] at ha; exact absurd ha (by simp)
  -- the finaliser raised: keep the error or suppress it
  obtain ⟨⟨rfl, hK, hT, ha⟩, τa, τb, hcab, ⟨hPA, hnA⟩, hnb⟩ := pure_sep_iff.mp hp
  refine wpG_head (fun μ => Head.cferr μ N err m j w K hK) rfl _ _ σ ?_
  refine wpG_here _ _ _ σ (Or.inr ⟨.hole, errNext N err m j w, pure_sep_mk ⟨rfl, rfl⟩ ?_⟩)
  have hnσ₁ : NoOwn σ₁ := noOwn_compS hcab hnA hnb
  cases err with
  | some E =>
      exact ⟨σ₂, σ₁, ResU.CompS.comm hcσ, he', hnσ₁⟩
  | none =>
      have he'' : σ₂ = PMap.empty := he'.1
      subst he''
      have hσ : σ = σ₁ := eq_of_compS_empty_left (ResU.CompS.comm hcσ)
      subst hσ
      by_cases hm : m ∈ N
      · simp only [errNext, if_pos hm]
        exact ⟨PMap.empty, σ, compS_empty_left σ, ⟨rfl, trivial⟩, hnσ₁⟩
      · simp only [errNext, if_neg hm]
        exact ⟨τa, τb, hcab, ⟨m, j, w, en, pure_sep_mk ⟨rfl, hm, hle _ _ _ hT, ha⟩ ⟨hPA, hnA⟩⟩,
          hnb⟩

/-- A cancel run's `ewpTS` absorbs garbage. -/
theorem ewp_cancel_absorb {T : OpTab} {N : List UInt32} {ls : List SRec} {e : Expr}
    {ρ₁ ρ₂ ρ : WRes} (h : ewpTS ls e (cancelTab T N) (fun _ _ _ => False) ρ₁) (hn : NoOwn ρ₂)
    (hc : ResU.CompS ρ₁ ρ₂ ρ) : ewpTS ls e (cancelTab T N) (fun _ _ _ => False) ρ := by
  refine (ewp_abortive (cancelTab_abortive T N)).mpr ?_
  have h₁ := wpG_frame (e := e) (fun _ => fun τ => NoOwn τ) (fun _ _ _ h => h) ρ
    ⟨ρ₁, ρ₂, hc, (ewp_abortive (cancelTab_abortive T N)).mp h, hn⟩
  refine wpG_mono (fun ls' t σ ht => ?_) h₁
  obtain ⟨σ₁, σ₂, hcσ, hp, hn'⟩ := ht
  rcases hp with ⟨_, _, hv⟩ | hp
  · exact hv.elim
  · exact Or.inr (cancelTab_absorb hp hn' hcσ)

/-- The finaliser frame `ubind (N, D) [·]`. -/
abbrev ubindK (Nv Dv : Val) : Kont :=
  .appR (.app (.val (.prim .ubind)) (.val (Val.pair Nv Dv))) .hole

/-- A cancel run through a finaliser frame: the finaliser runs under `cfin` with the frame. -/
theorem cancel_then {T Ta : OpTab} (hA : Ta.AbortOnly) (hle : Ta.Le T) (hL : T.Local)
    {N : List UInt32} (Nv Dv : Val) (Fr : List SRec → WProp)
    (hFs : ∀ ls ls', (∀ x, x ∈ ls' ↔ x ∈ ls) → Entails (Fr ls) (Fr ls'))
    {Qd : List SRec → Val → WProp} (hQd : ∀ ls v ρ, Qd ls v ρ → NoOwn ρ)
    (hD : ∀ ls, Entails (Fr ls) (ewpTS ls (.app (.val Dv) (.val .unit)) (opTable Ta) Qd))
    {ls : List SRec} {e : Expr} {ρ σ ρ' : WRes}
    (h : ewpTS ls e (cancelTab T N) (fun _ _ _ => False) ρ) (hσ : Fr ls σ)
    (hc : ResU.CompS ρ σ ρ') :
    ewpTS ls ((ubindK Nv Dv).plug e) (cancelTab T N) (fun _ _ _ => False) ρ' := by
  refine (ewp_abortive (cancelTab_abortive T N)).mpr ?_
  refine wpG_bind (ubindK Nv Dv) e ls _ ρ' ?_
  have h₁ := wpG_frame (e := e) Fr (hFs ls) ρ'
    ⟨ρ, σ, hc, (ewp_abortive (cancelTab_abortive T N)).mp h, hσ⟩
  refine wpG_mono (fun ls' t τ ht => ?_) h₁
  obtain ⟨τ₁, τ₂, hcτ, hp, hF⟩ := ht
  rcases hp with ⟨_, _, hv⟩ | ⟨K', err, hs⟩
  · exact hv.elim
  obtain ⟨⟨rfl, hK'⟩, τa, τb, hcab, he, hnb⟩ := pure_sep_iff.mp hs
  refine wpG_head (fun μ => Head.ufinC μ Nv Dv N err K' hK') rfl _ _ τ ?_
  obtain ⟨z, hz, hcz⟩ := compS_exch hcab hcτ
  exact (ewp_abortive (cancelTab_abortive T N)).mp (ewp_cancel_absorb
    (ewp_cfin hA hle hL hQd (hD ls' τ₂ hF) he (ResU.CompS.comm hz)) hnb hcz)

/-- **The finaliser frame around an effectful computation** (`M then x. N unwind D`).  As
`ewp_frame_plain`, but a cancel or an abortive stop runs the finaliser `D` on the frame instead of
dropping it: under `cfin` at a cancel, and before the `raise` goes on at an abortive stop.
`[spec §19]` -/
theorem ewp_frame_then (T Ta : OpTab) (hA : Ta.AbortOnly) (hle : Ta.Le T) (hL : T.Local)
    (h0 : ∀ i, T 0 i = none) (Nv Dv : Val) (Fr : List SRec → WProp)
    (hFs : ∀ ls ls', (∀ x, x ∈ ls' ↔ x ∈ ls) → Entails (Fr ls) (Fr ls'))
    (hFe : ∀ ls ls' ρ, Ext ls ls' ρ → Fr ls ρ → Fr ls' ρ)
    (hU : ∀ n i en, T n i = some en → en.q = .unr → ∀ ls ρ, Fr ls ρ → ρ = PMap.empty)
    {Qd : List SRec → Val → WProp} (hQd : ∀ ls v ρ, Qd ls v ρ → v = .unit ∧ NoOwn ρ)
    (hD : ∀ ls, Entails (Fr ls) (ewpTS ls (.app (.val Dv) (.val .unit)) (opTable Ta) Qd))
    (Q₁ Q : List SRec → Val → WProp)
    (hk : ∀ ls v, Entails (Q₁ ls v ⋆ Fr ls)
      (ewpTS ls ((ubindK Nv Dv).plug (.val v)) (opTable T) Q)) :
    ∀ {ls : List SRec} {e : Expr} {ρ : WRes}, ewpTS ls e (opTable T) Q₁ ρ →
      ∀ {ρ₂ ρ' : WRes}, Fr ls ρ₂ → ResU.CompS ρ ρ₂ ρ' →
        ewpTS ls ((ubindK Nv Dv).plug e) (opTable T) Q ρ' := by
  intro ls e ρ h
  refine ewp_ind (fun ls e ρ => ∀ {ρ₂ ρ' : WRes}, Fr ls ρ₂ → ResU.CompS ρ ρ₂ ρ' →
    ewpTS ls ((ubindK Nv Dv).plug e) (opTable T) Q ρ') ?_ h
  intro ls e ρ hs ρ₂ ρ' hF hc
  refine ewp_fold (opTable_mono T) (wpG_bind (ubindK Nv Dv) e ls _ ρ' ?_)
  have h₁ := wpG_frame (e := e) Fr (hFs ls) ρ' ⟨ρ, ρ₂, hc, hs, hF⟩
  refine wpG_mono (fun ls' t σ ht => ?_) h₁
  obtain ⟨σ₁, σ₂, hcσ, hp, hF'⟩ := ht
  rcases hp with ⟨v, rfl, hv⟩ | hp
  · exact ewp_unfold (opTable_mono T) (hk ls' v σ ⟨σ₁, σ₂, hcσ, hv, hF'⟩)
  rcases hp with ⟨K₁, n, i, v, en, hp⟩ | ⟨K₁, n, i, v, en, hp⟩
  · -- a `perform`: the frame joins the continuation's share
    refine wpG_here _ _ _ σ (Or.inr ?_)
    obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρk, hcak, hA', hu, hcont⟩ := pure_sep_iff.mp hp
    obtain ⟨ρk', hk', hcσ'⟩ := compS_reassoc hcak hcσ
    refine Or.inl ⟨(ubindK Nv Dv).comp K₁, n, i, v, en,
      pure_sep_mk ⟨(Kont.plug_comp _ _ _).symm, ?_, hT, ha⟩
      ⟨ρa, ρk', hcσ', hA', ?_, fun ls'' he => ⟨?_, fun hq => ?_⟩⟩⟩
    · rw [hasHnd_comp, hK₁]; rfl
    · intro hq
      rw [hu hq, hU n i en hT hq ls' σ₂ hF'] at hk'
      exact eq_of_compS_empty_left hk'
    · intro w τ₁ τ₂ hB hcτ
      obtain ⟨z, hz, hcz⟩ := compS_exch hk' hcτ
      rw [Kont.plug_comp]
      exact (hcont ls'' (he.left hk')).1 w τ₁ z hB hz (hFe ls' ls'' σ₂ (he.right hk') hF') hcz
    · intro N hn hNK
      have hc' := (hcont ls'' (he.left hk')).2 hq N hn
        (fun m hm => hNK m (by rw [hndNames_comp]; exact List.mem_append_right _ hm))
      rw [Kont.plug_comp]
      exact cancel_then hA hle hL Nv Dv Fr hFs (fun _ _ _ h => (hQd _ _ _ h).2) hD hc'
        (hFe ls' ls'' σ₂ (he.right hk') hF') hk'
  · -- a `raise`: the finaliser runs, then the `raise` goes on
    obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρn, hcan, ⟨hPA, hnA⟩, hn⟩ := pure_sep_iff.mp hp
    have hn0 : n ≠ 0 := fun h => by subst h; rw [h0 i] at hT; exact absurd hT (by simp)
    refine wpG_head (fun μ => Head.ufin μ Nv Dv n i v K₁ hn0 hK₁) rfl _ _ σ ?_
    refine wpG_bind (.seq .hole (raiseE (.val (opPayload n i v)))) _ ls' _ σ ?_
    let R : List SRec → WProp := fun ls => (fun τ => en.PA ls v τ ∧ NoOwn τ) ⋆ fun τ => NoOwn τ
    have hRs : ∀ ls'', (∀ x, x ∈ ls'' ↔ x ∈ ls') → Entails (R ls') (R ls'') := by
      rintro ls'' hs τ ⟨τa, τb, hcab, ⟨hPA', hnA'⟩, hnb⟩
      exact ⟨τa, τb, hcab, ⟨(hL n i en hT ls' ls'' v τa (ext_of_same hs τa)).1 hPA', hnA'⟩, hnb⟩
    have h₂ := wpG_frame (e := .app (.val Dv) (.val .unit)) R hRs σ
      ⟨σ₂, σ₁, ResU.CompS.comm hcσ,
        (ewp_abortive (opTable_abortive hA)).mp (hD ls' σ₂ hF'), ρa, ρn, hcan, ⟨hPA, hnA⟩, hn⟩
    refine wpG_mono (fun ls'' t τ ht => ?_) h₂
    obtain ⟨τ₁, τ₂, hcτ, hp, ra, rn, hcr, ⟨hPA', hnA'⟩, hnr⟩ := ht
    rcases hp with ⟨w, rfl, hw⟩ | hp
    · -- the finaliser finished: the `raise` goes on
      obtain ⟨rfl, hnw⟩ := hQd _ _ _ hw
      refine wpG_head (fun μ => Head.seq μ _) rfl _ _ τ ?_
      obtain ⟨z, hz, hcz⟩ := compS_lcomm hcr hcτ
      exact wpG_here _ _ _ τ (Or.inr (Or.inr ⟨.hole, n, i, v, en,
        pure_sep_mk ⟨rfl, rfl, hT, ha⟩
          ⟨ra, z, hcz, ⟨hPA', hnA'⟩, noOwn_compS hz hnw hnr⟩⟩))
    rcases hp with ⟨K', m, j, w, en', hp⟩ | ⟨K', m, j, w, en', hp⟩
    · obtain ⟨⟨-, -, hT', ha'⟩, -⟩ := pure_sep_iff.mp hp
      rw [hA m j en' hT'] at ha'; exact absurd ha' (by simp)
    -- the finaliser raised: its error supersedes the pending `raise`
    obtain ⟨⟨rfl, hK', hT', ha'⟩, qa, qn, hcq, ⟨hPq, hnq⟩, hnqn⟩ := pure_sep_iff.mp hp
    refine wpG_here _ _ _ τ (Or.inr (Or.inr ⟨.seq K' (raiseE (.val (opPayload n i v))), m, j, w, en',
      pure_sep_mk ⟨rfl, by simpa [Kont.Catches] using hK', hle _ _ _ hT', ha'⟩ ?_⟩))
    obtain ⟨z, hz, hcz⟩ := compS_reassoc hcq hcτ
    exact ⟨qa, z, hcz, ⟨hPq, hnq⟩,
      noOwn_compS hz hnqn (noOwn_compS hcr hnA' hnr)⟩

/-! ### The continuation `κ` -/

/-- Substituting into a context shifted past the substituted index. -/
theorem plug_shift_subst (d : Nat) : ∀ (K : Kont) (c j : Nat) (s : Val) (x : Expr), c ≤ j →
    j ≤ c + d → Expr.subst j s ((K.shift (d + 1) c).plug x) = (K.shift d c).plug (Expr.subst j s x)
  | .hole, _, _, _, _, _, _ => rfl
  | .pairL K e, c, j, s, x, h₁, h₂ => by
      simp only [Kont.shift, Kont.plug, Expr.subst, plug_shift_subst d K c j s x h₁ h₂,
        Expr.subst_shift d c j s e h₁ h₂]
  | .pairR v K, c, j, s, x, h₁, h₂ => by
      simp only [Kont.shift, Kont.plug, Expr.subst, Expr.val, Val.val_shift,
        plug_shift_subst d K c j s x h₁ h₂, Expr.subst_shift d c j s v.1 h₁ h₂]
  | .letpair K e, c, j, s, x, h₁, h₂ => by
      simp only [Kont.shift, Kont.plug, Expr.subst, plug_shift_subst d K c j s x h₁ h₂,
        Expr.subst_shift d (c + 2) (j + 2) (s.shift 2 0) e (by omega) (by omega)]
  | .case K e₁ e₂, c, j, s, x, h₁, h₂ => by
      simp only [Kont.shift, Kont.plug, Expr.subst, plug_shift_subst d K c j s x h₁ h₂,
        Expr.subst_shift d (c + 1) (j + 1) (s.shift 1 0) e₁ (by omega) (by omega),
        Expr.subst_shift d (c + 1) (j + 1) (s.shift 1 0) e₂ (by omega) (by omega)]
  | .appR f K, c, j, s, x, h₁, h₂ => by
      simp only [Kont.shift, Kont.plug, Expr.subst, plug_shift_subst d K c j s x h₁ h₂,
        Expr.subst_shift d c j s f h₁ h₂]
  | .appL K v, c, j, s, x, h₁, h₂ => by
      simp only [Kont.shift, Kont.plug, Expr.subst, Expr.val, Val.val_shift,
        plug_shift_subst d K c j s x h₁ h₂, Expr.subst_shift d c j s v.1 h₁ h₂]
  | .seq K e, c, j, s, x, h₁, h₂ => by
      simp only [Kont.shift, Kont.plug, Expr.subst, plug_shift_subst d K c j s x h₁ h₂,
        Expr.subst_shift d c j s e h₁ h₂]
  | .inj₁ K, c, j, s, x, h₁, h₂ => by
      simp only [Kont.shift, Kont.plug, Expr.subst, plug_shift_subst d K c j s x h₁ h₂]
  | .inj₂ K, c, j, s, x, h₁, h₂ => by
      simp only [Kont.shift, Kont.plug, Expr.subst, plug_shift_subst d K c j s x h₁ h₂]

theorem Kont.shift_zero : ∀ (K : Kont) (c : Nat), K.shift 0 c = K
  | .hole, _ => rfl
  | .pairL K e, c => by simp only [Kont.shift, Kont.shift_zero K c, Expr.shift_zero]
  | .pairR v K, c => by simp only [Kont.shift, Kont.shift_zero K c, Val.shift_zero]
  | .letpair K e, c => by simp only [Kont.shift, Kont.shift_zero K c, Expr.shift_zero]
  | .case K e₁ e₂, c => by simp only [Kont.shift, Kont.shift_zero K c, Expr.shift_zero]
  | .appR f K, c => by simp only [Kont.shift, Kont.shift_zero K c, Expr.shift_zero]
  | .appL K v, c => by simp only [Kont.shift, Kont.shift_zero K c, Val.shift_zero]
  | .seq K e, c => by simp only [Kont.shift, Kont.shift_zero K c, Expr.shift_zero]
  | .inj₁ K, c => by simp only [Kont.shift, Kont.shift_zero K c]
  | .inj₂ K, c => by simp only [Kont.shift, Kont.shift_zero K c]

/-- Resuming `κ` at `w` runs `hnd H K[w]`. -/
theorem ewp_kappa_resume {Tb : Table} (hTb : Tb.Mono) (n : UInt32) (H : Val) (K : Kont) (w : Val)
    {ls : List SRec} {Q : List SRec → Val → WProp} {ρ : WRes}
    (h : ewpTS ls (hndE H (K.plug (.val w))) Tb Q ρ) :
    ewpTS ls (.app (.app (kappa n H K) (.val (Val.inj₁ .unit))) (.val w)) Tb Q ρ := by
  refine ewp_step hTb (fun μ => (Step1N.head (Head.beta μ _ _) rfl).plug (Kont.appL .hole w)) ls Q ρ ?_
  refine ewp_step hTb (fun μ => (Step1N.head (Head.case₁ μ Val.unit _ _) rfl).plug
    (Kont.appL .hole w)) ls Q ρ ?_
  refine ewp_step hTb (fun μ => (Step1N.head (Head.seq μ _) rfl).plug (Kont.appL .hole w)) ls Q ρ ?_
  refine ewp_step hTb (fun μ => Step1N.head (Head.beta μ _ w) rfl) ls Q ρ ?_
  have e : ∀ (s u : Val), Expr.subst 0 w (Expr.subst 1 u (Expr.subst 2 s
      (hndE (Val.shift 3 0 H) ((Kont.shift 3 0 K).plug (Expr.var 0))))) =
      hndE H (K.plug (.val w)) := by
    intro s u
    simp only [hndE, Expr.subst, Expr.val, Val.val_shift]
    rw [Expr.subst_shift 2 0 2 s H.1 (by omega) (by omega),
      Expr.subst_shift 1 0 1 u H.1 (by omega) (by omega),
      Expr.subst_shift 0 0 0 w H.1 (by omega) (by omega), Expr.shift_zero,
      plug_shift_subst 2 K 0 2 s _ (by omega) (by omega),
      plug_shift_subst 1 K 0 1 u _ (by omega) (by omega),
      plug_shift_subst 0 K 0 0 w _ (by omega) (by omega), Kont.shift_zero]
    simp [Expr.subst]
  rw [show (0 + 1 : Nat) = 1 from rfl, show (0 + 1 + 1 : Nat) = 2 from rfl, e]
  exact h

theorem subst_namesVal (j : Nat) (s : Val) : ∀ N : List UInt32,
    Expr.subst j s (BoCa.BoLo.namesVal N).1 = (BoCa.BoLo.namesVal N).1
  | [] => rfl
  | m :: N => by
      simp only [BoCa.BoLo.namesVal, Val.inj₂, Val.pair, Val.i32, Expr.subst, subst_namesVal j s N]

theorem subst_cancelVal_none (j : Nat) (s : Val) (N : List UInt32) :
    Expr.subst j s (cancelVal N none).1 = (cancelVal N none).1 := by
  simp only [cancelVal, opPayload, BoCa.BoLo.errVal, Val.pair, Val.i32, Val.inj₁, Val.unit,
    Expr.subst, subst_namesVal]

/-- Cancelling `κ` runs `ccatch (hnd H K[raise (0, (0, (N, none)))])`. -/
theorem ewp_kappa_cancel {Tb : Table} (hTb : Tb.Mono) (n : UInt32) (H : Val) (K : Kont)
    {ls : List SRec} {Q : List SRec → Val → WProp} {ρ : WRes}
    (h : ewpTS ls (ccatchE (hndE H (K.plug (raiseE (.val (cancelVal (n :: K.hndNames) none))))))
      Tb Q ρ) :
    ewpTS ls (.app (kappa n H K) (.val (Val.inj₂ .unit))) Tb Q ρ := by
  refine ewp_step hTb (fun μ => Step1N.head (Head.beta μ _ _) rfl) ls Q ρ ?_
  refine ewp_step hTb (fun μ => Step1N.head (Head.case₂ μ Val.unit _ _) rfl) ls Q ρ ?_
  refine ewp_step hTb (fun μ => Step1N.head (Head.seq μ _) rfl) ls Q ρ ?_
  have e : ∀ (s u : Val), Expr.subst 0 u (Expr.subst 1 s
      (ccatchE (hndE (Val.shift 2 0 H) ((Kont.shift 2 0 K).plug
        (raiseE (.val (cancelVal (n :: K.hndNames) none))))))) =
      ccatchE (hndE H (K.plug (raiseE (.val (cancelVal (n :: K.hndNames) none))))) := by
    intro s u
    simp only [ccatchE, hndE, Expr.subst, Expr.val, Val.val_shift]
    rw [Expr.subst_shift 1 0 1 s H.1 (by omega) (by omega),
      Expr.subst_shift 0 0 0 u H.1 (by omega) (by omega), Expr.shift_zero,
      plug_shift_subst 1 K 0 1 s _ (by omega) (by omega),
      plug_shift_subst 0 K 0 0 u _ (by omega) (by omega), Kont.shift_zero]
    simp only [raiseE, Expr.subst, Expr.val, subst_cancelVal_none, Val.prim]
  rw [show (0 + 1 : Nat) = 1 from rfl, e]
  exact h

/-! ### Handlers -/

/-- The handler frame `hnd H [·]`. -/
abbrev hndK (H : Val) : Kont := .appR (.app (.val (.prim .hnd)) (.val H)) .hole

theorem hndK_catches (n : UInt32) (hr hs : Val) (m : UInt32) :
    (hndK (hndVal n hr hs)).Catches m = (n == m) := by
  simp [Kont.Catches, hndVal, Val.pair, Val.i32, Expr.val]

theorem hndK_hasHnd (n : UInt32) (hr hs : Val) (m : UInt32) :
    (hndK (hndVal n hr hs)).HasHnd m = (n == m) := by
  simp [Kont.HasHnd, hndVal, Val.pair, Val.i32, Expr.val]

theorem hndK_hndNames (n : UInt32) (hr hs : Val) : (hndK (hndVal n hr hs)).hndNames = [n] := by
  simp [Kont.hndNames, hndVal, Val.pair, Val.i32, Expr.val]

/-- The relation of `κ`'s type at an operation's entry: resumed at every answer, and, with
weakening, cancelled at `F_Σ 1`.  `[spec §19]` -/
def KapRel (Tout : OpTab) (Qout : List SRec → Val → WProp) (en : OpEnt) (ls : List SRec)
    (κ : Val) : WProp := fun ρ =>
  (en.q = .unr → ρ = PMap.empty) ∧
  ∀ ls', Ext ls ls' ρ →
    (∀ w : Val, (en.PB ls' w ─⋆
      ewpTS ls' (.app (.app κ.1 (.val (Val.inj₁ .unit))) (.val w)) (opTable Tout) Qout) ρ) ∧
    (en.q ≠ .lin → ewpTS ls' (.app κ.1 (.val (Val.inj₂ .unit))) (opTable Tout)
      (fun _ v => ⌜v = Val.unit⌝) ρ)

/-- A cancel run caught at `ccatch` under the reinstalled handler: `()`, or the kept error raised
at the canceller.  `[spec §19]` -/
theorem ewp_ccatch {Tin Tout : OpTab} {N : List UInt32} (H : Val) (hH : (hndK H).Catches 0 = false)
    (hT : ∀ m j en, m ∉ N → Tin m j = some en → Tout m j = some en)
    {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : ewpTS ls e (cancelTab Tin N) (fun _ _ _ => False) ρ) :
    ewpTS ls (ccatchE (hndE H e)) (opTable Tout) (fun _ v => ⌜v = Val.unit⌝) ρ := by
  refine ewp_fold (opTable_mono Tout) ?_
  refine wpG_bind ((Kont.appR (.val (.prim .ccatch)) .hole).comp (hndK H)) e ls _ ρ ?_
  refine wpG_mono (fun ls' t σ ht => ?_) ((ewp_abortive (cancelTab_abortive Tin N)).mp h)
  rcases ht with ⟨_, _, hv⟩ | ⟨K', err, hs⟩
  · exact hv.elim
  obtain ⟨⟨rfl, hK'⟩, τa, τb, hcab, he, hnb⟩ := pure_sep_iff.mp hs
  have hK : ((hndK H).comp K').Catches 0 = false := by rw [catches_comp, hH, hK']; rfl
  rw [Kont.plug_comp]
  show wpG ls' (ccatchE ((hndK H).plug (K'.plug _))) _ σ
  rw [← Kont.plug_comp]
  cases err with
  | none =>
      refine wpG_head (fun μ => Head.cancel μ N _ hK) rfl _ _ σ ?_
      have hτa : τa = PMap.empty := he.1
      subst hτa
      rw [← eq_of_compS_empty_left hcab] at hnb
      refine wpG_garbage (wpG_here _ _ _ σ ⟨PMap.empty, σ, compS_empty_left σ, hnb,
        Or.inl ⟨Val.unit, rfl, rfl, rfl⟩⟩)
  | some E =>
      refine wpG_head (fun μ => Head.creraise μ N E _ hK) rfl _ _ σ ?_
      obtain ⟨m, j, w, en, he⟩ := he
      obtain ⟨⟨rfl, hm, hTe, ha⟩, hPA, hnA⟩ := pure_sep_iff.mp he
      exact wpG_here _ _ _ σ (Or.inr (Or.inr ⟨.hole, m, j, w, en,
        pure_sep_mk ⟨rfl, rfl, hT m j en hm hTe, ha⟩ ⟨τa, τb, hcab, ⟨hPA, hnA⟩, hnb⟩⟩))

/-- **A handler** (`[handle]`), by induction on the least fixed point of the inner computation.
`[ret]` answers through `h_ret`; an operation of the handler's name runs its clause, with `κ`
resumed by the induction hypothesis and cancelled by the inner computation's cancel run under
`ccatch`; an abortive one runs its clause and drops the abandoned continuation; an operation of
another name passes outward, the handler reinstalled in its continuation.  `[spec §19]` -/
theorem ewp_handle (Tin Tout : OpTab) (n : UInt32) (hn0 : n ≠ 0)
    (hTin : ∀ m i, m ≠ n → Tin m i = Tout m i) (hr hs : Val)
    (Qin Qout : List SRec → Val → WProp)
    (hret : ∀ ls v ρ, Qin ls v ρ → ewpTS ls (.app (.val hr) (.val v)) (opTable Tout) Qout ρ)
    (hop : ∀ i en, Tin n i = some en → ∃ c, clauseAt hs.1 i.toNat = some c ∧
      (en.abort = false → ∀ ls v (κ : Val) ρ, (en.PA ls v ⋆ KapRel Tout Qout en ls κ) ρ →
        ewpTS ls (.app (.val c) (.pair (.val v) κ.1)) (opTable Tout) Qout ρ) ∧
      (en.abort = true → ∀ ls v ρ, en.PA ls v ρ →
        ewpTS ls (.app (.val c) (.val v)) (opTable Tout) Qout ρ)) :
    ∀ {ls : List SRec} {e : Expr} {ρ : WRes}, ewpTS ls e (opTable Tin) Qin ρ →
      ewpTS ls (hndE (hndVal n hr hs) e) (opTable Tout) Qout ρ := by
  have hmap : ∀ N : List UInt32, n ∈ N → ∀ m j en, m ∉ N → Tin m j = some en →
      Tout m j = some en := fun N hN m j en hm h => by
    rw [← hTin m j (fun e => hm (e ▸ hN))]; exact h
  have hmapE : ∀ N : List UInt32, n ∈ N → ∀ ls err ρ, errOk Tin N ls err ρ → errOk Tout N ls err ρ
    | N, hN, ls, none, ρ, h => h
    | N, hN, ls, some E, ρ, ⟨m, j, w, en, h⟩ => by
        obtain ⟨⟨h₁, h₂, h₃, h₄⟩, h₅⟩ := pure_sep_iff.mp h
        exact ⟨m, j, w, en, pure_sep_mk ⟨h₁, h₂, hmap N hN m j en h₂ h₃, h₄⟩ h₅⟩
  have hC0 : (hndK (hndVal n hr hs)).Catches 0 = false := by
    rw [hndK_catches]; simpa using hn0
  intro ls e ρ h
  refine ewp_ind (fun ls e ρ => ewpTS ls (hndE (hndVal n hr hs) e) (opTable Tout) Qout ρ) ?_ h
  intro ls e ρ hstep
  refine ewp_fold (opTable_mono Tout) (wpG_bind (hndK (hndVal n hr hs)) e ls _ ρ ?_)
  refine wpG_mono (fun ls' t σ ht => ?_) hstep
  rcases ht with ⟨v, rfl, hv⟩ | ht
  · -- `[ret]`
    exact wpG_head (fun μ => Head.hret μ n hr hs v) rfl _ _ σ
      (ewp_unfold (opTable_mono Tout) (hret _ _ _ hv))
  rcases ht with ⟨K₁, m, i, v, en, hp⟩ | ⟨K₁, m, i, v, en, hp⟩
  · obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρk, hcak, hA, hu, hcont⟩ := pure_sep_iff.mp hp
    by_cases hm : m = n
    · -- `[op]` at the handler's name: the clause, with `κ`
      subst hm
      obtain ⟨c, hc, hna, -⟩ := hop i en hT
      refine wpG_head (fun μ => Head.hop μ m i hr hs c v K₁ hc hK₁) rfl _ _ σ ?_
      refine ewp_unfold (opTable_mono Tout) (hna ha ls' v
        ⟨kappa m (hndVal m hr hs) K₁, by unfold kappa; exact .lam⟩ σ ⟨ρa, ρk, hcak, hA, ?_⟩)
      refine ⟨hu, fun ls'' he => ⟨fun w τ₁ τ₂ hB hc => ?_, fun hq => ?_⟩⟩
      · exact ewp_kappa_resume (opTable_mono Tout) m _ K₁ w
          ((hcont ls'' he).1 w τ₁ τ₂ hB hc)
      · refine ewp_kappa_cancel (opTable_mono Tout) m _ K₁ ?_
        exact ewp_ccatch (Tin := Tin) _ hC0 (hmap _ (List.mem_cons_self))
          ((hcont ls'' he).2 hq (m :: K₁.hndNames) List.mem_cons_self
            (fun x hx => List.mem_cons_of_mem _ hx))
    · -- an operation of another name passes outward
      refine wpG_here _ _ _ σ (Or.inr (Or.inl ⟨(hndK (hndVal n hr hs)).comp K₁, m, i, v, en,
        pure_sep_mk ⟨(Kont.plug_comp _ _ _).symm, ?_, (hTin m i hm) ▸ hT, ha⟩
          ⟨ρa, ρk, hcak, hA, hu, fun ls'' he => ⟨fun w τ₁ τ₂ hB hc => ?_, fun hq N hN hNK => ?_⟩⟩⟩))
      · rw [hasHnd_comp, hndK_hasHnd, hK₁]; simpa using Ne.symm hm
      · rw [Kont.plug_comp]; exact (hcont ls'' he).1 w τ₁ τ₂ hB hc
      · have hnN : n ∈ N := hNK n (by rw [hndNames_comp, hndK_hndNames]; exact List.mem_cons_self)
        rw [Kont.plug_comp]
        exact cancel_frame _ hC0 (hmapE N hnN)
          ((hcont ls'' he).2 hq N hN (fun x hx => hNK x (by
            rw [hndNames_comp, hndK_hndNames]; exact List.mem_cons_of_mem _ hx)))
          noOwn_empty (ResU.comp_empty_right _)
  · obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρn, hcan, ⟨hPA, hnA⟩, hnn⟩ := pure_sep_iff.mp hp
    by_cases hm : m = n
    · -- `[unwind]` at the handler's name: the clause; the continuation is dropped
      subst hm
      obtain ⟨c, hc, -, hab⟩ := hop i en hT
      refine wpG_head (fun μ => Head.hunwind μ m i hr hs c v K₁ hc hK₁) rfl _ _ σ ?_
      refine wpG_garbage (wpG_mono (fun _ _ _ ⟨τ₁, τ₂, hcτ, hq, hnτ⟩ => ⟨τ₁, τ₂, hcτ, hnτ, hq⟩)
        (wpG_frame (e := .app (.val c) (.val v)) (fun _ => fun τ => NoOwn τ)
          (fun _ _ _ h => h) σ ⟨ρa, ρn, hcan,
            ewp_unfold (opTable_mono Tout) (hab ha ls' v ρa hPA), hnn⟩))
    · -- an abortive operation of another name passes outward
      refine wpG_here _ _ _ σ (Or.inr (Or.inr ⟨(hndK (hndVal n hr hs)).comp K₁, m, i, v, en,
        pure_sep_mk ⟨(Kont.plug_comp _ _ _).symm, ?_, (hTin m i hm) ▸ hT, ha⟩
          ⟨ρa, ρn, hcan, ⟨hPA, hnA⟩, hnn⟩⟩))
      rw [catches_comp, hndK_catches, hK₁]; simpa using Ne.symm hm

end BoCa.Fig16.LogRel.Core
