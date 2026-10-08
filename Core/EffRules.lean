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
  cancelVal hndE ubindE ccatchE cfinE hndVal kappa clauseAt errNext capTag kappaAt kappaC
  kappaCBody kappaCell freeE stuckE)
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

/-- `κ`'s resume branch, substituted at its three binders and the answer `w`, is `hnd H K[w]`. -/
theorem kappa_resume_subst (H : Val) (K : Kont) (w s u : Val) :
    Expr.subst 0 w (Expr.subst 1 u (Expr.subst 2 s
      (hndE (Val.shift 3 0 H) ((Kont.shift 3 0 K).plug (Expr.var 0))))) =
      hndE H (K.plug (.val w)) := by
  simp only [hndE, Expr.subst, Expr.val, Val.val_shift]
  rw [Expr.subst_shift 2 0 2 s H.1 (by omega) (by omega),
    Expr.subst_shift 1 0 1 u H.1 (by omega) (by omega),
    Expr.subst_shift 0 0 0 w H.1 (by omega) (by omega), Expr.shift_zero,
    plug_shift_subst 2 K 0 2 s _ (by omega) (by omega),
    plug_shift_subst 1 K 0 1 u _ (by omega) (by omega),
    plug_shift_subst 0 K 0 0 w _ (by omega) (by omega), Kont.shift_zero]
  simp [Expr.subst]

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
  rw [show (0 + 1 : Nat) = 1 from rfl, show (0 + 1 + 1 : Nat) = 2 from rfl, kappa_resume_subst]
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

/-- `κ`'s cancel branch, substituted at its two binders, is `ccatch (hnd H K[raise …])`. -/
theorem kappa_cancel_subst (n : UInt32) (H : Val) (K : Kont) (s u : Val) :
    Expr.subst 0 u (Expr.subst 1 s
      (ccatchE (hndE (Val.shift 2 0 H) ((Kont.shift 2 0 K).plug
        (raiseE (.val (cancelVal (n :: K.hndNames) none))))))) =
      ccatchE (hndE H (K.plug (raiseE (.val (cancelVal (n :: K.hndNames) none))))) := by
  simp only [ccatchE, hndE, Expr.subst, Expr.val, Val.val_shift]
  rw [Expr.subst_shift 1 0 1 s H.1 (by omega) (by omega),
    Expr.subst_shift 0 0 0 u H.1 (by omega) (by omega), Expr.shift_zero,
    plug_shift_subst 1 K 0 1 s _ (by omega) (by omega),
    plug_shift_subst 0 K 0 0 u _ (by omega) (by omega), Kont.shift_zero]
  simp only [raiseE, Expr.subst, Expr.val, subst_cancelVal_none, Val.prim]

/-- Cancelling `κ` runs `ccatch (hnd H K[raise (0, (0, (N, none)))])`. -/
theorem ewp_kappa_cancel {Tb : Table} (hTb : Tb.Mono) (n : UInt32) (H : Val) (K : Kont)
    {ls : List SRec} {Q : List SRec → Val → WProp} {ρ : WRes}
    (h : ewpTS ls (ccatchE (hndE H (K.plug (raiseE (.val (cancelVal (n :: K.hndNames) none))))))
      Tb Q ρ) :
    ewpTS ls (.app (kappa n H K) (.val (Val.inj₂ .unit))) Tb Q ρ := by
  refine ewp_step hTb (fun μ => Step1N.head (Head.beta μ _ _) rfl) ls Q ρ ?_
  refine ewp_step hTb (fun μ => Step1N.head (Head.case₂ μ Val.unit _ _) rfl) ls Q ρ ?_
  refine ewp_step hTb (fun μ => Step1N.head (Head.seq μ _) rfl) ls Q ρ ?_
  rw [show (0 + 1 : Nat) = 1 from rfl, kappa_cancel_subst]
  exact h

/-! ### The capture cell  `[spec §25]` -/

/-- An allocation at an evaluation position, in front of an `ewpTS`: `[TR]` 6.141 (`wpTS_alloc`)
then the rest of the run, at the allocated cell. -/
theorem ewp_alloc {Tb : Table} (hTb : Tb.Mono) (K : Kont) (v : Val) {ls : List SRec}
    {Q : List SRec → Val → WProp} {ρ : WRes}
    (h : ∀ ℓ : Loc, (ptoOwn ℓ v ─⋆ ewpTS ls (K.plug (.val (Val.loc ℓ))) Tb Q) ρ) :
    ewpTS ls (K.plug (.app (.val (.prim .alloc)) (.val v))) Tb Q ρ :=
  ewp_fold hTb (wpG_bind_pure K _ ls _ ρ (wpTS_alloc ls v _ ρ
    (fun ℓ σ₁ σ₂ hp hc => ewp_unfold hTb (h ℓ σ₁ σ₂ hp hc))))

/-- A release of an owned cell at an evaluation position, in front of an `ewpTS`: `[TR]` 6.142
(`wpTS_free`) then the rest of the run, at the cell's contents. -/
theorem ewp_free {Tb : Table} (hTb : Tb.Mono) (K : Kont) (ℓ : Loc) (v : Val) {ls : List SRec}
    {Q : List SRec → Val → WProp} {ρ : WRes}
    (h : (ptoOwn ℓ v ⋆ ewpTS ls (K.plug (.val v)) Tb Q) ρ) :
    ewpTS ls (K.plug (freeE (.val (Val.loc ℓ)))) Tb Q ρ := by
  obtain ⟨ρ₁, ρ₂, hc, hp, hq⟩ := h
  exact ewp_fold hTb (wpG_bind_pure K _ ls _ ρ (wpTS_free ls ℓ v _ ρ
    ⟨ρ₁, ρ₂, hc, hp, ewp_unfold hTb hq⟩))

/-- `κ`'s body over its cell, at the cell's location, is `kappaC`. -/
theorem kappaCBody_subst (aff : Bool) (ℓ : Loc) (n : UInt32) (H : Val) (K : Kont) :
    Expr.subst 0 (Val.loc ℓ) (kappaCBody aff n H K) = kappaC aff ℓ n H K := by
  cases aff <;>
  simp only [kappaCBody, kappaC, freeE, stuckE, hndE, ccatchE, raiseE, Expr.subst, Expr.val,
    Val.val_shift, Bool.false_eq_true, if_true, if_false, Val.loc, Val.lam, Val.prim, Val.unit] <;>
  first
    | (rw [Expr.subst_shift 3 0 3 _ H.1 (by omega) (by omega),
        plug_shift_subst 3 K 0 3 _ _ (by omega) (by omega)]
       simp [Expr.subst, Val.shift, Expr.shift, Expr.subst_shift 2 0 2 _ H.1 (by omega) (by omega),
         plug_shift_subst 2 K 0 2 _ _ (by omega) (by omega), subst_cancelVal_none])
    | (simp [Expr.subst, Val.shift, Expr.shift, Expr.subst_shift 3 0 3 _ H.1 (by omega) (by omega),
         plug_shift_subst 3 K 0 3 _ _ (by omega) (by omega), Expr.subst_shift 2 0 2 _ H.1 (by omega) (by omega),
         plug_shift_subst 2 K 0 2 _ _ (by omega) (by omega), subst_cancelVal_none])

/-- **The capture cell's allocation**: `κ` before its cell, at an evaluation position, allocates
the cell by the ordinary `alloc` step and becomes `kappaC` at its location. -/
theorem ewp_kappaCell {Tb : Table} (hTb : Tb.Mono) (aff : Bool) (n : UInt32) (H : Val) (K : Kont)
    (Kc : Kont) {ls : List SRec} {Q : List SRec → Val → WProp} {ρ : WRes}
    (h : ∀ ℓ : Loc, (ptoOwn ℓ Val.unit ─⋆ ewpTS ls (Kc.plug (kappaC aff ℓ n H K)) Tb Q) ρ) :
    ewpTS ls (Kc.plug (kappaCell aff n H K)) Tb Q ρ := by
  have e : Kc.plug (kappaCell aff n H K) =
      (Kc.comp (.appR (.val (.lam (kappaCBody aff n H K))) .hole)).plug
        (.app (.val (.prim .alloc)) (.val Val.unit)) := by
    rw [Kont.plug_comp]; rfl
  rw [e]
  refine ewp_alloc hTb _ Val.unit (fun ℓ σ₁ σ₂ hp hc => ?_)
  rw [Kont.plug_comp]
  refine ewp_step hTb (fun μ => (Step1N.head (Head.beta μ _ (Val.loc ℓ)) rfl).plug Kc) ls Q σ₂ ?_
  rw [kappaCBody_subst]
  exact h ℓ σ₁ σ₂ hp hc

/-- `kappaC` is a value. -/
theorem isVal_kappaC (aff : Bool) (ℓ : Loc) (n : UInt32) (H : Val) (K : Kont) :
    IsVal (kappaC aff ℓ n H K) := by unfold kappaC; exact .lam

/-- **Resuming a `κ` that owns a cell** at `w` frees the cell, then runs `hnd H K[w]`. -/
theorem ewp_kappaC_resume {Tb : Table} (hTb : Tb.Mono) (aff : Bool) (ℓ : Loc) (n : UInt32)
    (H : Val) (K : Kont) (w : Val) {ls : List SRec} {Q : List SRec → Val → WProp} {ρ : WRes}
    (h : (ptoOwn ℓ Val.unit ⋆ ewpTS ls (hndE H (K.plug (.val w))) Tb Q) ρ) :
    ewpTS ls (.app (.app (kappaC aff ℓ n H K) (.val (Val.inj₁ .unit))) (.val w)) Tb Q ρ := by
  refine ewp_step hTb (fun μ => (Step1N.head (Head.beta μ _ _) rfl).plug (Kont.appL .hole w)) ls Q ρ ?_
  refine ewp_step hTb (fun μ => (Step1N.head (Head.case₁ μ Val.unit _ _) rfl).plug
    (Kont.appL .hole w)) ls Q ρ ?_
  refine ewp_step hTb (fun μ => (Step1N.head (Head.seq μ _) rfl).plug (Kont.appL .hole w)) ls Q ρ ?_
  refine ewp_free hTb (Kont.appL (Kont.seq .hole _) w) ℓ Val.unit ?_
  obtain ⟨ρ₁, ρ₂, hc, hp, hq⟩ := h
  refine ⟨ρ₁, ρ₂, hc, hp, ?_⟩
  refine ewp_step hTb (fun μ => (Step1N.head (Head.seq μ _) rfl).plug (Kont.appL .hole w)) ls Q ρ₂ ?_
  refine ewp_step hTb (fun μ => Step1N.head (Head.beta μ _ w) rfl) ls Q ρ₂ ?_
  rw [show (0 + 1 : Nat) = 1 from rfl, show (0 + 1 + 1 : Nat) = 2 from rfl, kappa_resume_subst]
  exact hq

/-- **Cancelling an affine `κ`** frees its cell, then runs
`ccatch (hnd H K[raise (0, (0, (N, none)))])`. -/
theorem ewp_kappaC_cancel {Tb : Table} (hTb : Tb.Mono) (ℓ : Loc) (n : UInt32) (H : Val) (K : Kont)
    {ls : List SRec} {Q : List SRec → Val → WProp} {ρ : WRes}
    (h : (ptoOwn ℓ Val.unit ⋆ ewpTS ls (ccatchE (hndE H (K.plug (raiseE (.val (cancelVal
      (n :: K.hndNames) none)))))) Tb Q) ρ) :
    ewpTS ls (.app (kappaC true ℓ n H K) (.val (Val.inj₂ .unit))) Tb Q ρ := by
  refine ewp_step hTb (fun μ => Step1N.head (Head.beta μ _ _) rfl) ls Q ρ ?_
  refine ewp_step hTb (fun μ => Step1N.head (Head.case₂ μ Val.unit _ _) rfl) ls Q ρ ?_
  refine ewp_step hTb (fun μ => Step1N.head (Head.seq μ _) rfl) ls Q ρ ?_
  refine ewp_free hTb (Kont.seq .hole _) ℓ Val.unit ?_
  obtain ⟨ρ₁, ρ₂, hc, hp, hq⟩ := h
  refine ⟨ρ₁, ρ₂, hc, hp, ?_⟩
  refine ewp_step hTb (fun μ => Step1N.head (Head.seq μ _) rfl) ls Q ρ₂ ?_
  rw [show (0 + 1 : Nat) = 1 from rfl, kappa_cancel_subst]
  exact hq

/-! ### Handlers -/

/-- The handler frame `hnd H [·]`. -/
abbrev hndK (H : Val) : Kont := .appR (.app (.val (.prim .hnd)) (.val H)) .hole

theorem hndK_catches (n : UInt32) (qs hr hs : Val) (m : UInt32) :
    (hndK (hndVal n qs hr hs)).Catches m = (n == m) := by
  simp [Kont.Catches, hndVal, Val.pair, Val.i32, Expr.val]

theorem hndK_hasHnd (n : UInt32) (qs hr hs : Val) (m : UInt32) :
    (hndK (hndVal n qs hr hs)).HasHnd m = (n == m) := by
  simp [Kont.HasHnd, hndVal, Val.pair, Val.i32, Expr.val]

theorem hndK_hndNames (n : UInt32) (qs hr hs : Val) :
    (hndK (hndVal n qs hr hs)).hndNames = [n] := by
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

/-- A qualifier's tag in a handler value: `0` linear, `1` affine, `2` unrestricted.
`[spec §25]` -/
def Qual.tag : Qual → UInt32
  | .lin => 0
  | .aff => 1
  | .unr => 2

/-- The tags of a list of qualifiers, as the right-nested tuple a handler value holds.
`[spec §25]` -/
def qualsVal : List Qual → Val
  | [] => Val.unit
  | q :: qs => Val.pair (Val.i32 q.tag) (qualsVal qs)

theorem capTag_qualsVal : ∀ (qs : List Qual) (j : Nat) (h : j < qs.length),
    capTag (qualsVal qs).1 j = qs[j].tag
  | [], _, h => by simp at h
  | q :: qs, 0, _ => by simp [qualsVal, capTag, Val.pair, Val.i32]
  | q :: qs, j + 1, h => by
      simp only [qualsVal, Val.pair, capTag, List.getElem_cons_succ]
      exact capTag_qualsVal qs j (by simpa using h)

@[simp] theorem psub_qualsVal (k : Nat) (γ : List Val) :
    ∀ qs : List Qual, Expr.psub k γ (qualsVal qs).1 = (qualsVal qs).1
  | [] => rfl
  | q :: qs => by
      simp only [qualsVal, Val.pair, Val.i32, Expr.psub, psub_qualsVal k γ qs]

@[simp] theorem shift_qualsVal (d c : Nat) :
    ∀ qs : List Qual, Expr.shift d c (qualsVal qs).1 = (qualsVal qs).1
  | [] => rfl
  | q :: qs => by
      simp only [qualsVal, Val.pair, Val.i32, Expr.shift, shift_qualsVal d c qs]

@[simp] theorem subst_qualsVal (j : Nat) (s : Val) :
    ∀ qs : List Qual, Expr.subst j s (qualsVal qs).1 = (qualsVal qs).1
  | [] => rfl
  | q :: qs => by
      simp only [qualsVal, Val.pair, Val.i32, Expr.subst, subst_qualsVal j s qs]

/-- The continuation `[op]` hands at a tag: a cell at a linear or affine operation. -/
theorem kappaAt_tag (q : Qual) (n : UInt32) (H : Val) (K : Kont) :
    kappaAt q.tag n H K = (match q with
      | .lin => kappaCell false n H K
      | .aff => kappaCell true n H K
      | .unr => kappa n H K) := by
  cases q <;> simp [kappaAt, Qual.tag]

/-- **A handler** (`[handle]`), by induction on the least fixed point of the inner computation.
`[ret]` answers through `h_ret`; an operation of the handler's name runs its clause, with `κ`
resumed by the induction hypothesis and cancelled by the inner computation's cancel run under
`ccatch`; at a linear or affine operation `κ` first gets its cell (`ewp_kappaCell`), which its
resume and its cancel free; an abortive one runs its clause and drops the abandoned continuation;
an operation of another name passes outward, the handler reinstalled in its continuation.  The
handler's tags `qs` record its operations' qualifiers.  `[spec §19, §25]` -/
theorem ewp_handle (Tin Tout : OpTab) (n : UInt32) (hn0 : n ≠ 0)
    (hTin : ∀ m i, m ≠ n → Tin m i = Tout m i) (qs hr hs : Val)
    (Qin Qout : List SRec → Val → WProp)
    (hq : ∀ i en, Tin n i = some en → en.abort = false → capTag qs.1 i.toNat = en.q.tag)
    (hret : ∀ ls v ρ, Qin ls v ρ → ewpTS ls (.app (.val hr) (.val v)) (opTable Tout) Qout ρ)
    (hop : ∀ i en, Tin n i = some en → ∃ c, clauseAt hs.1 i.toNat = some c ∧
      (en.abort = false → ∀ ls v (κ : Val) ρ, (en.PA ls v ⋆ KapRel Tout Qout en ls κ) ρ →
        ewpTS ls (.app (.val c) (.pair (.val v) κ.1)) (opTable Tout) Qout ρ) ∧
      (en.abort = true → ∀ ls v ρ, en.PA ls v ρ →
        ewpTS ls (.app (.val c) (.val v)) (opTable Tout) Qout ρ)) :
    ∀ {ls : List SRec} {e : Expr} {ρ : WRes}, ewpTS ls e (opTable Tin) Qin ρ →
      ewpTS ls (hndE (hndVal n qs hr hs) e) (opTable Tout) Qout ρ := by
  have hmap : ∀ N : List UInt32, n ∈ N → ∀ m j en, m ∉ N → Tin m j = some en →
      Tout m j = some en := fun N hN m j en hm h => by
    rw [← hTin m j (fun e => hm (e ▸ hN))]; exact h
  have hmapE : ∀ N : List UInt32, n ∈ N → ∀ ls err ρ, errOk Tin N ls err ρ → errOk Tout N ls err ρ
    | N, hN, ls, none, ρ, h => h
    | N, hN, ls, some E, ρ, ⟨m, j, w, en, h⟩ => by
        obtain ⟨⟨h₁, h₂, h₃, h₄⟩, h₅⟩ := pure_sep_iff.mp h
        exact ⟨m, j, w, en, pure_sep_mk ⟨h₁, h₂, hmap N hN m j en h₂ h₃, h₄⟩ h₅⟩
  have hC0 : (hndK (hndVal n qs hr hs)).Catches 0 = false := by
    rw [hndK_catches]; simpa using hn0
  intro ls e ρ h
  refine ewp_ind (fun ls e ρ => ewpTS ls (hndE (hndVal n qs hr hs) e) (opTable Tout) Qout ρ) ?_ h
  intro ls e ρ hstep
  refine ewp_fold (opTable_mono Tout) (wpG_bind (hndK (hndVal n qs hr hs)) e ls _ ρ ?_)
  refine wpG_mono (fun ls' t σ ht => ?_) hstep
  rcases ht with ⟨v, rfl, hv⟩ | ht
  · -- `[ret]`
    exact wpG_head (fun μ => Head.hret μ n qs hr hs v) rfl _ _ σ
      (ewp_unfold (opTable_mono Tout) (hret _ _ _ hv))
  rcases ht with ⟨K₁, m, i, v, en, hp⟩ | ⟨K₁, m, i, v, en, hp⟩
  · obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρk, hcak, hA, hu, hcont⟩ := pure_sep_iff.mp hp
    by_cases hm : m = n
    · -- `[op]` at the handler's name: the clause, with `κ`
      subst hm
      obtain ⟨c, hc, hna, -⟩ := hop i en hT
      refine wpG_head (fun μ => Head.hop μ m i qs hr hs c v K₁ hc hK₁) rfl _ _ σ ?_
      have hcan : ∀ ls'', Ext ls' ls'' ρk → en.q ≠ .lin →
          ewpTS ls'' (ccatchE (hndE (hndVal m qs hr hs) (K₁.plug (raiseE (.val
            (cancelVal (m :: K₁.hndNames) none)))))) (opTable Tout) (fun _ v => ⌜v = Val.unit⌝) ρk :=
        fun ls'' he hq' => ewp_ccatch (Tin := Tin) _ hC0 (hmap _ (List.mem_cons_self))
          ((hcont ls'' he).2 hq' (m :: K₁.hndNames) List.mem_cons_self
            (fun x hx => List.mem_cons_of_mem _ hx))
      rw [hq i en hT ha, kappaAt_tag]
      cases hqq : en.q with
      | unr =>
          refine ewp_unfold (opTable_mono Tout) (hna ha ls' v
            ⟨kappa m (hndVal m qs hr hs) K₁, by unfold kappa; exact .lam⟩ σ ⟨ρa, ρk, hcak, hA, ?_⟩)
          refine ⟨hu, fun ls'' he => ⟨fun w τ₁ τ₂ hB hc => ?_, fun hq' => ?_⟩⟩
          · exact ewp_kappa_resume (opTable_mono Tout) m _ K₁ w
              ((hcont ls'' he).1 w τ₁ τ₂ hB hc)
          · exact ewp_kappa_cancel (opTable_mono Tout) m _ K₁ (hcan ls'' he hq')
      | aff | lin =>
          refine ewp_unfold (opTable_mono Tout) (ewp_kappaCell (opTable_mono Tout) _ m
            (hndVal m qs hr hs) K₁ (.appR (.val c) (.pairR v .hole)) (fun ℓ σ₁ σ₂ hcell hc₂ => ?_))
          obtain ⟨y, hy₁, hy₂⟩ := compS_reassoc hcak hc₂
          refine hna ha ls' v ⟨_, isVal_kappaC _ ℓ m (hndVal m qs hr hs) K₁⟩ σ₂
            ⟨ρa, y, hy₂, hA, ?_⟩
          refine ⟨fun h' => (by rw [hqq] at h'; cases h'),
            fun ls'' he => ⟨fun w τ₁ τ₂ hB hcτ => ?_, fun hq' => ?_⟩⟩
          · obtain ⟨z, hz, hzτ⟩ := compS_exch hy₁ hcτ
            exact ewp_kappaC_resume (opTable_mono Tout) _ ℓ m _ K₁ w
              ⟨σ₁, z, ResU.CompS.comm hzτ, hcell, (hcont ls'' (Ext.left hy₁ he)).1 w τ₁ z hB hz⟩
          · first
              | exact absurd hqq hq'
              | exact ewp_kappaC_cancel (opTable_mono Tout) ℓ m _ K₁
                  ⟨σ₁, ρk, ResU.CompS.comm hy₁, hcell, hcan ls'' (Ext.left hy₁ he) hq'⟩
    · -- an operation of another name passes outward
      refine wpG_here _ _ _ σ (Or.inr (Or.inl ⟨(hndK (hndVal n qs hr hs)).comp K₁, m, i, v, en,
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
      refine wpG_head (fun μ => Head.hunwind μ m i qs hr hs c v K₁ hc hK₁) rfl _ _ σ ?_
      refine wpG_garbage (wpG_mono (fun _ _ _ ⟨τ₁, τ₂, hcτ, hq, hnτ⟩ => ⟨τ₁, τ₂, hcτ, hnτ, hq⟩)
        (wpG_frame (e := .app (.val c) (.val v)) (fun _ => fun τ => NoOwn τ)
          (fun _ _ _ h => h) σ ⟨ρa, ρn, hcan,
            ewp_unfold (opTable_mono Tout) (hab ha ls' v ρa hPA), hnn⟩))
    · -- an abortive operation of another name passes outward
      refine wpG_here _ _ _ σ (Or.inr (Or.inr ⟨(hndK (hndVal n qs hr hs)).comp K₁, m, i, v, en,
        pure_sep_mk ⟨(Kont.plug_comp _ _ _).symm, ?_, (hTin m i hm) ▸ hT, ha⟩
          ⟨ρa, ρn, hcan, ⟨hPA, hnA⟩, hnn⟩⟩))
      rw [catches_comp, hndK_catches, hK₁]; simpa using Ne.symm hm

/-! ### The typing rules' types  `[spec §19]` -/

theorem ext_empty' (ls ls' : List SRec) : Ext ls ls' PMap.empty :=
  ⟨fun _ _ hr => by obtain ⟨m, ψ, e, -⟩ := hr; simp at e,
   fun _ hb => by obtain ⟨m, ψ, e, -⟩ := hb; simp at e⟩

/-- The payload expression `(n, (i, V))`. -/
def opArgE (n i : UInt32) (V : Expr) : Expr := .pair (.val (Val.i32 n)) (.pair (.val (Val.i32 i)) V)

/-- `S ⊆ S′` as rows: every operation of `S` is `S′`'s. -/
def RowLe (S S' : Row) : Prop := ∀ n i o, Row.find S n i = some o → Row.find S' n i = some o

/-- A row's names are not the reserved `0`. -/
def Row.NZ (S : Row) : Prop := ∀ o ∈ S, o.n ≠ 0

/-- A row has an operation with weakening: an abortive, affine or unrestricted one. -/
def Row.Weak (S : Row) : Prop := ∃ o ∈ S, o.q ≠ .lin

/-- A row has an unrestricted operation. -/
def Row.Unr (S : Row) : Prop := ∃ o ∈ S, o.q = .unr

/-- A row's abortive operations. -/
def Row.abortOnly (S : Row) : Row := S.filter OpSig.abort

theorem Row.find_mem {S : Row} {n i : UInt32} {o : OpSig} (h : Row.find S n i = some o) :
    o ∈ S ∧ o.n = n ∧ o.i = i := by
  unfold Row.find at h
  have hm := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  simp only [decide_eq_true_eq] at hp
  exact ⟨hm, hp.1.symm, hp.2.symm⟩

theorem Row.tab_some {S : Row} {δ : LSub} {n i : UInt32} {en : OpEnt}
    (h : Row.tab S δ n i = some en) : ∃ o, Row.find S n i = some o ∧ en = o.ent δ := by
  unfold Row.tab at h
  cases hf : Row.find S n i with
  | none => rw [hf] at h; cases h
  | some o => rw [hf] at h; exact ⟨o, rfl, (Option.some.inj h).symm⟩

theorem Row.tab_le {S S' : Row} (δ : LSub) (h : RowLe S S') : (Row.tab S δ).Le (Row.tab S' δ) := by
  intro n i en hT
  obtain ⟨o, hf, rfl⟩ := Row.tab_some hT
  simp [Row.tab, h n i o hf]

theorem Row.tab_local (S : Row) (δ : LSub) : (Row.tab S δ).Local := by
  intro n i en hT ls ls' v ρ he
  obtain ⟨o, -, rfl⟩ := Row.tab_some hT
  exact ⟨vC_local true o.A he, vC_local true o.B he⟩

theorem Row.tab_zero {S : Row} (hS : S.NZ) (δ : LSub) (i : UInt32) : Row.tab S δ 0 i = none := by
  cases hf : Row.find S 0 i with
  | none => simp [Row.tab, hf]
  | some o =>
      obtain ⟨hm, hn, -⟩ := Row.find_mem hf
      exact absurd hn (hS o hm)

/-- A row's operations have distinct keys `(n, i)`. -/
def Row.Uniq (S : Row) : Prop := S.Pairwise fun o o' => ¬ (o.n = o'.n ∧ o.i = o'.i)

theorem Row.find_of_mem : ∀ {S : Row}, S.Uniq → ∀ {o : OpSig}, o ∈ S → Row.find S o.n o.i = some o
  | [], _, _, h => by simp at h
  | o' :: S, hU, o, hm => by
      unfold Row.find
      rw [List.find?_cons]
      rcases List.mem_cons.mp hm with rfl | hm'
      · simp
      · have hne : ¬ (o.n = o'.n ∧ o.i = o'.i) := fun h =>
          (List.pairwise_cons.mp hU).1 o hm' ⟨h.1.symm, h.2.symm⟩
        simp only [hne]
        exact Row.find_of_mem (List.pairwise_cons.mp hU).2 hm'

theorem Row.abortOnly_le {S : Row} (hU : S.Uniq) : RowLe S.abortOnly S := by
  intro n i o hf
  obtain ⟨hm, rfl, rfl⟩ := Row.find_mem hf
  exact Row.find_of_mem hU (List.mem_filter.mp hm).1

theorem Row.abortOnly_abort (S : Row) (δ : LSub) : (Row.tab S.abortOnly δ).AbortOnly := by
  intro n i en hT
  obtain ⟨o, hf, rfl⟩ := Row.tab_some hT
  obtain ⟨hm, -, -⟩ := Row.find_mem hf
  exact (List.mem_filter.mp hm).2

/-! ### Compatibility of `[sub]`, `[perform]`, `[raise]` -/

/-- `[sub]`: a row may grow.  `[spec §19]` -/
theorem sub_compatC {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {S S' : Row} {A : VTy}
    (hle : RowLe S S') (h : SemC Δ Γ e (CTy.effOf S A)) : SemC Δ Γ e (CTy.effOf S' A) := by
  intro δ γ ls ρ hδ hg
  exact (cC_effOf S' A ls δ _ ρ).mpr (ewp_sub (Row.tab_le δ hle)
    ((cC_effOf S A ls δ _ ρ).mp (h δ γ ls ρ hδ hg)))

/-- `[perform]`.  `[spec §19]` -/
theorem perform_compatC {Δ : LifeCtx} {Γ : Ctx VTy} {V : Expr} {S : Row} {o : OpSig}
    (hf : Row.find S o.n o.i = some o) (hna : o.abort = false) (h : SemV Δ Γ V o.A) :
    SemC Δ Γ (performE (opArgE o.n o.i V)) (CTy.effOf S o.B) := by
  intro δ γ ls ρ hδ hg
  refine (cC_effOf S o.B ls δ _ ρ).mpr ?_
  change ewpTS ls ((Kont.appR (.val (.prim .perform))
    (.pairR (Val.i32 o.n) (.pairR (Val.i32 o.i) .hole))).plug (substAll γ V)) _ _ ρ
  refine ewp_bind_pure_frame (opTable_mono _) _ _ ls (fun ls v => vC true o.A ls δ v)
    (fun _ => emp) _ (fun _ _ _ h => h) ?_ ρ
    ⟨ρ, PMap.empty, ResU.comp_empty_right ρ, h δ γ ls ρ hδ hg, ⟨rfl, trivial⟩⟩
  rintro ls' - v σ ⟨σ₁, σ₂, hc, hv, rfl, -⟩
  rw [ResU.CompS.functional hc (ResU.comp_empty_right σ₁)]
  exact ewp_perform_here (en := o.ent δ) (by simp [Row.tab, hf]) hna (fun _ _ _ h => h) hv

/-- `[raise]`: an abortive operation, at any answer type, its argument holding nothing owned.
`[spec §19]` -/
theorem raise_compatC {Δ : LifeCtx} {Γ : Ctx VTy} {V : Expr} {S : Row} {o : OpSig} {B : VTy}
    (hf : Row.find S o.n o.i = some o) (ha : o.abort = true)
    (hd : ∀ ls δ v ρ, vC true o.A ls δ v ρ → NoOwn ρ) (h : SemV Δ Γ V o.A) :
    SemC Δ Γ (raiseE (opArgE o.n o.i V)) (CTy.effOf S B) := by
  intro δ γ ls ρ hδ hg
  refine (cC_effOf S B ls δ _ ρ).mpr ?_
  change ewpTS ls ((Kont.appR (.val (.prim .raise))
    (.pairR (Val.i32 o.n) (.pairR (Val.i32 o.i) .hole))).plug (substAll γ V)) _ _ ρ
  refine ewp_bind_pure_frame (opTable_mono _) _ _ ls (fun ls v => vC true o.A ls δ v)
    (fun _ => emp) _ (fun _ _ _ h => h) ?_ ρ
    ⟨ρ, PMap.empty, ResU.comp_empty_right ρ, h δ γ ls ρ hδ hg, ⟨rfl, trivial⟩⟩
  rintro ls' - v σ ⟨σ₁, σ₂, hc, hv, rfl, -⟩
  rw [ResU.CompS.functional hc (ResU.comp_empty_right σ₁)]
  exact ewp_raise_here (en := o.ent δ) (by simp [Row.tab, hf]) ha hv (hd _ _ _ _ hv)

/-! ### Contexts that drop -/

/-- A type whose values hold no `own` cell: data, borrows, `!`.  `[spec §19]` -/
inductive _root_.BoCa.Fig16.LogRel.Core.VTy.Drop : VTy → Prop where
  | unit : VTy.Drop .unit
  | zero : VTy.Drop .zero
  | int (w : Width) : VTy.Drop (.int w)
  | unk : VTy.Drop .unk
  | opq (k : Opaque) : VTy.Drop (.opq k)
  | bang (A : VTy) : VTy.Drop (.bang A)
  | imm (a : Lifetime.Life) (A : VTy) : VTy.Drop (.imm a A)
  | «mut» (a : Lifetime.Life) (A : VTy) : VTy.Drop (.mut a A)
  | tensor {A B : VTy} : VTy.Drop A → VTy.Drop B → VTy.Drop (.tensor A B)
  | sum {A B : VTy} : VTy.Drop A → VTy.Drop B → VTy.Drop (.sum A B)

theorem vC_noOwn_of_drop {A : VTy} (hA : A.Drop) :
    ∀ {ls : List SRec} {δ : LSub} {v : Val} {ρ : WRes}, vC true A ls δ v ρ → NoOwn ρ := by
  induction hA with
  | unit => intro ls δ v ρ h; rw [h.1]; exact noOwn_empty
  | zero => intro ls δ v ρ h; exact h.elim
  | int w => intro ls δ v ρ h; rw [h.1]; exact noOwn_empty
  | unk => intro ls δ v ρ h; rw [h.1]; exact noOwn_empty
  | opq k => intro ls δ v ρ h; rw [h.1]; exact noOwn_empty
  | bang A => intro ls δ v ρ h; rw [h.1]; exact noOwn_empty
  | imm a A =>
      intro ls δ v ρ h
      obtain ⟨α, -, ℓ, hs⟩ := h
      obtain ⟨-, s, u, σ, hσ, ls₀, rfl, -⟩ := pure_sep_iff.mp hs
      exact ResU.restrict_single_other (by simp)
  | «mut» a A =>
      intro ls δ v ρ h
      obtain ⟨α, -, ℓ, hs⟩ := h
      obtain ⟨-, b, u, σ, hσ, Q, hw, ls₀, -, rfl, -⟩ := pure_sep_iff.mp hs
      exact ResU.restrict_single_other (by simp)
  | tensor _ _ ihA ihB =>
      intro ls δ v ρ h
      obtain ⟨v₁, v₂, h⟩ := h
      obtain ⟨-, ρ₁, ρ₂, hc, h₁, h₂⟩ := pure_sep_iff.mp h
      exact noOwn_compS hc (ihA h₁) (ihB h₂)
  | sum _ _ ihA ihB =>
      intro ls δ v ρ h
      rcases h with ⟨v₁, h⟩ | ⟨v₂, h⟩
      · exact ihA (pure_sep_iff.mp h).2
      · exact ihB (pure_sep_iff.mp h).2

/-- Every live slot of `Γ` is at a type that drops. -/
def _root_.BoCa.Ctx.Drops (Γ : Ctx VTy) : Prop := ∀ s ∈ Γ, s.live = true → s.ty.Drop

theorem gSepC_noOwn {ls : List SRec} {δ : LSub} : ∀ {Γ : Ctx VTy} {γ : List Val} {ρ : WRes},
    Γ.Drops → gSepC ls δ Γ γ ρ → NoOwn ρ
  | [], _, _, _, h => by rw [h.1]; exact noOwn_empty
  | _ :: _, [], _, _, h => by rw [h.1]; exact noOwn_empty
  | s :: Γ, v :: γ, ρ, hd, h => by
      unfold gSepC at h
      split at h
      · rename_i hl
        obtain ⟨ρ₁, ρ₂, hc, h₁, h₂⟩ := h
        exact noOwn_compS hc (vC_noOwn_of_drop (hd s (by simp) hl) h₁)
          (gSepC_noOwn (fun s' hs' => hd s' (List.mem_cons_of_mem _ hs')) h₂)
      · exact gSepC_noOwn (fun s' hs' => hd s' (List.mem_cons_of_mem _ hs')) h

theorem gDenC_noOwn {ls : List SRec} {δ : LSub} {Γ : Ctx VTy} {γ : List Val} {ρ : WRes}
    (hd : Γ.Drops) (h : gDenC ls δ Γ γ ρ) : NoOwn ρ :=
  gSepC_noOwn hd (gDenC_iff.mp h).2

theorem gDenC_persistent {ls : List SRec} {δ : LSub} {Γ : Ctx VTy} {γ : List Val} {ρ : WRes}
    (hp : Persistent Γ) (h : gDenC ls δ Γ γ ρ) : ρ = PMap.empty :=
  gSepC_persistent hp (gDenC_iff.mp h).2

/-! ### Compatibility of `[let]` and `[then]` -/

private theorem substAll_cons' (v : Val) (γ : List Val) (e : Expr) :
    substAll (v :: γ) e = Expr.subst 0 v (Expr.psub 1 γ e) := by
  show Expr.psub 0 (v :: γ) e = _
  rw [Expr.psub_cons 0 v γ e, Val.shift_zero]

theorem OpSig.weak_of_ent {o : OpSig} {δ : LSub} (h : (o.ent δ).q ≠ .lin ∨ (o.ent δ).abort = true) :
    o.q ≠ .lin := by
  rcases h with h | h
  · exact h
  · simp only [OpSig.ent, OpSig.abort, Bool.and_eq_true, bne_iff_ne, ne_eq] at h; exact h.2

/-- `[let]` at a row: `M to x. N`, the context of `N` dropping at a row with weakening and
persistent at an unrestricted row.  `[spec §19]` -/
theorem let_compatC {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {M N : Expr} {A B : VTy} {S : Row}
    (hsp : Ctx.SplitP Γ Γ₁ Γ₂) (hW : S.Weak → Γ₂.Drops) (hU : S.Unr → Persistent Γ₂)
    (hM : SemC Δ Γ₁ M (CTy.effOf S A)) (hN : SemC Δ (⟨A, true⟩ :: Γ₂) N (CTy.effOf S B)) :
    SemC Δ Γ (.app (.val (.lam N)) M) (CTy.effOf S B) := by
  intro δ γ ls ρ hδ hg
  obtain ⟨ρ₁, ρ₂, hc, hg₁, hg₂⟩ := gDenC_split hsp hg
  refine (cC_effOf S B ls δ _ ρ).mpr ?_
  refine ewp_frame_plain (Row.tab S δ) (.appR (.val (.lam (Expr.psub 1 γ N))) .hole)
    (fun n => by simp [Kont.HasHnd]) (fun n => by simp [Kont.Catches]) (by simp [Kont.hndNames])
    (fun ls => gDenC ls δ Γ₂ γ) (fun _ _ hs σ h => gDenC_same hs h)
    (fun _ _ _ he h => gDenC_local he h) ?_ ?_ (fun ls v => vC true A ls δ v) _ ?_
    ((cC_effOf S A ls δ _ ρ₁).mp (hM δ γ ls ρ₁ hδ hg₁)) hg₂ hc
  · intro n i en hT hq ls' σ h
    obtain ⟨o, hf, rfl⟩ := Row.tab_some hT
    exact gDenC_noOwn (hW ⟨o, (Row.find_mem hf).1, OpSig.weak_of_ent hq⟩) h
  · intro n i en hT hq ls' σ h
    obtain ⟨o, hf, rfl⟩ := Row.tab_some hT
    exact gDenC_persistent (hU ⟨o, (Row.find_mem hf).1, hq⟩) h
  · rintro ls' v σ ⟨σ₁, σ₂, hcσ, hv, hg₂'⟩
    obtain ⟨hlen, hgs⟩ := gDenC_iff.mp hg₂'
    refine ewp_step (opTable_mono _)
      (fun μ => Step1N.head (Head.beta μ (Expr.psub 1 γ N) v) rfl) ls' _ σ ?_
    rw [← substAll_cons']
    exact (cC_effOf S B ls' δ _ σ).mp
      (hN δ (v :: γ) ls' σ hδ (gDenC_mk (by simpa using hlen) ⟨σ₁, σ₂, hcσ, hv, hgs⟩))

/-- `M then x. N unwind D`: `ubind (λx. N, λ_. D) M`. -/
def thenE (N D M : Expr) : Expr :=
  .app (.app (.val (.prim .ubind)) (.pair (.val (.lam N)) (.val (.lam D)))) M

/-- `[then]` at a row: the finaliser `D`, at the row's abortive operations, runs on the context of
`N` at a cancel and at an abortive stop.  `[spec §19]` -/
theorem then_compatC {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {M N D : Expr} {A B : VTy} {S : Row}
    (hsp : Ctx.SplitP Γ Γ₁ Γ₂) (hNZ : S.NZ) (hUq : S.Uniq) (hU : S.Unr → Persistent Γ₂)
    (hM : SemC Δ Γ₁ M (CTy.effOf S A)) (hN : SemC Δ (⟨A, true⟩ :: Γ₂) N (CTy.effOf S B))
    (hD : SemC Δ (⟨.unit, false⟩ :: Γ₂) D (CTy.effOf S.abortOnly .unit)) :
    SemC Δ Γ (thenE N D M) (CTy.effOf S B) := by
  intro δ γ ls ρ hδ hg
  obtain ⟨ρ₁, ρ₂, hc, hg₁, hg₂⟩ := gDenC_split hsp hg
  refine (cC_effOf S B ls δ _ ρ).mpr ?_
  change ewpTS ls ((ubindK (Val.lam (Expr.psub 1 γ N)) (Val.lam (Expr.psub 1 γ D))).plug
    (substAll γ M)) _ _ ρ
  refine ewp_frame_then (Row.tab S δ) (Row.tab S.abortOnly δ) (Row.abortOnly_abort S δ)
    (Row.tab_le δ (Row.abortOnly_le hUq)) (Row.tab_local S δ) (Row.tab_zero hNZ δ) _ _
    (fun ls => gDenC ls δ Γ₂ γ) (fun _ _ hs σ h => gDenC_same hs h)
    (fun _ _ _ he h => gDenC_local he h) ?_ (Qd := fun ls v => vC true .unit ls δ v) ?_ ?_
    (fun ls v => vC true A ls δ v) _ ?_
    ((cC_effOf S A ls δ _ ρ₁).mp (hM δ γ ls ρ₁ hδ hg₁)) hg₂ hc
  · intro n i en hT hq ls' σ h
    obtain ⟨o, hf, rfl⟩ := Row.tab_some hT
    exact gDenC_persistent (hU ⟨o, (Row.find_mem hf).1, hq⟩) h
  · intro ls' v σ h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, noOwn_empty⟩
  · intro ls' σ h
    refine ewp_step (opTable_mono _)
      (fun μ => Step1N.head (Head.beta μ (Expr.psub 1 γ D) Val.unit) rfl) ls' _ σ ?_
    rw [← substAll_cons']
    exact (cC_effOf S.abortOnly .unit ls' δ _ σ).mp
      (hD δ (Val.unit :: γ) ls' σ hδ (gDenC_dead_cons .unit Val.unit h))
  · rintro ls' v σ ⟨σ₁, σ₂, hcσ, hv, hg₂'⟩
    obtain ⟨hlen, hgs⟩ := gDenC_iff.mp hg₂'
    refine ewp_step (opTable_mono _)
      (fun μ => Step1N.head (Head.uthen μ _ _ v) rfl) ls' _ σ ?_
    refine ewp_step (opTable_mono _)
      (fun μ => Step1N.head (Head.beta μ (Expr.psub 1 γ N) v) rfl) ls' _ σ ?_
    rw [← substAll_cons']
    exact (cC_effOf S B ls' δ _ σ).mp
      (hN δ (v :: γ) ls' σ hδ (gDenC_mk (by simpa using hlen) ⟨σ₁, σ₂, hcσ, hv, hgs⟩))

/-! ### Compatibility of `[handle]` -/

/-- An effect's operations, as a row of the name `n`: the `j`-th at index `k + j`. -/
def Row.ofEff (n : UInt32) : List (Qual × VTy × VTy) → Nat → Row
  | [], _ => []
  | (q, A, B) :: E, k => ⟨n, UInt32.ofNat k, q, A, B⟩ :: Row.ofEff n E (k + 1)

/-- `κ`'s type at an operation `A ↠^q B` of a handler answering `F_Σ R`: `U((B ⊸ F_Σ R) & ⊤)`
(linear: resumed), `U((B ⊸ F_Σ R) & F_Σ 1)` (affine: resumed or cancelled), and its `!`
(unrestricted).  `[spec §19]` -/
def kTy (S : Row) (R : VTy) (q : Qual) (B : VTy) : VTy :=
  match q with
  | .lin => .thunk (.amp (.arr B (CTy.effOf S R)) .top)
  | .aff => .thunk (.amp (.arr B (CTy.effOf S R)) (CTy.effOf S .unit))
  | .unr => .bang (.thunk (.amp (.arr B (CTy.effOf S R)) (CTy.effOf S .unit)))

/-- A clause's type: `!U(A ⊗ K ⊸ F_Σ R)`, or `!U(A ⊸ F_Σ R)` at an abortive operation.
`[spec §19]` -/
def clauseTy (S : Row) (R : VTy) : Qual × VTy × VTy → VTy
  | (q, A, B) => if (B.isZero && q != .lin) then .bang (.thunk (.arr A (CTy.effOf S R)))
      else .bang (.thunk (.arr (.tensor A (kTy S R q B)) (CTy.effOf S R)))

/-- The clauses' type: a right-nested tuple, the `j`-th clause at index `j`. -/
def clausesTy (S : Row) (R : VTy) : List (Qual × VTy × VTy) → VTy
  | [] => .unit
  | o :: E => .tensor (clauseTy S R o) (clausesTy S R E)

/-- `h_ret`'s type: `!U(A ⊸ F_Σ R)`. -/
def retTy (S : Row) (A R : VTy) : VTy := .bang (.thunk (.arr A (CTy.effOf S R)))

/-- `handle_n e with (h_ret, hs)`, `h_ret` and `hs` variables, the handler's tags those of the
qualifiers `qs` (`qualsVal`).  `[spec §19, §25]` -/
def hndTerm (n : UInt32) (qs : List Qual) (ir ic : Nat) (e : Expr) : Expr :=
  .app (.app (.val (.prim .hnd)) (.pair (.val (Val.i32 n))
    (.pair (.val (qualsVal qs)) (.pair (.var ir) (.var ic))))) e

theorem Row.find_ofEff (n : UInt32) : ∀ (E : List (Qual × VTy × VTy)) (k : Nat) (m i : UInt32)
    (o : OpSig), Row.find (Row.ofEff n E k) m i = some o →
      m = n ∧ ∃ j, ∃ h : j < E.length, i = UInt32.ofNat (k + j) ∧
        o = ⟨n, UInt32.ofNat (k + j), E[j].1, E[j].2.1, E[j].2.2⟩
  | [], _, _, _, _, h => by simp [Row.ofEff, Row.find] at h
  | (q, A, B) :: E, k, m, i, o, h => by
      unfold Row.find at h
      simp only [Row.ofEff, List.find?_cons] at h
      split at h
      · rename_i hk
        simp only [decide_eq_true_eq] at hk
        obtain ⟨rfl, rfl⟩ := hk
        cases h
        exact ⟨rfl, 0, by simp, by simp, by simp⟩
      · obtain ⟨hm, j, hj, hi, ho⟩ := Row.find_ofEff n E (k + 1) m i o h
        exact ⟨hm, j + 1, by simp; omega, by rw [hi]; congr 1; omega,
          by rw [ho]; simp [show k + 1 + j = k + (j + 1) by omega]⟩

theorem Row.find_ofEff_ne (n : UInt32) : ∀ (E : List (Qual × VTy × VTy)) (k : Nat) (m i : UInt32),
    m ≠ n → Row.find (Row.ofEff n E k) m i = none
  | [], _, _, _, _ => by simp [Row.ofEff, Row.find]
  | (q, A, B) :: E, k, m, i, hm => by
      unfold Row.find
      simp only [Row.ofEff, List.find?_cons]
      have hd : decide (m = n ∧ i = UInt32.ofNat k) = false := by simp [hm]
      rw [hd]
      exact Row.find_ofEff_ne n E (k + 1) m i hm

theorem Row.find_append (S S' : Row) (m i : UInt32) :
    Row.find (S ++ S') m i = (Row.find S m i).or (Row.find S' m i) := by
  unfold Row.find; rw [List.find?_append]

theorem clausesTy_at {S : Row} {R : VTy} {ls : List SRec} {δ : LSub} :
    ∀ (E : List (Qual × VTy × VTy)) {hs : Val} {ρ : WRes}, vC true (clausesTy S R E) ls δ hs ρ →
      ∀ j (h : j < E.length), ∃ c, clauseAt hs.1 j = some c ∧
        vC true (clauseTy S R E[j]) ls δ c PMap.empty
  | [], _, _, _, j, h => by simp at h
  | o :: E, hs, ρ, h, j, hj => by
      obtain ⟨c, rest, h⟩ := h
      obtain ⟨rfl, ρ₁, ρ₂, hc, hc₁, hr⟩ := pure_sep_iff.mp h
      have hc₁' := hc₁
      obtain ⟨q, A, B⟩ := o
      have he : ρ₁ = PMap.empty := by
        simp only [clauseTy] at hc₁'; split at hc₁' <;> exact hc₁'.1
      cases j with
      | zero =>
          refine ⟨c, ?_, he ▸ hc₁⟩
          simp [clauseAt, Val.pair, c.2]
      | succ j =>
          obtain ⟨c', hc', hv⟩ := clausesTy_at E hr j (by simpa using hj)
          exact ⟨c', by simpa [clauseAt, Val.pair] using hc', by simpa using hv⟩

/-- `κ`'s relation gives `κ`'s type. -/
theorem vC_kTy_of_kapRel {S : Row} {R B : VTy} {q : Qual} {δ : LSub} {ls : List SRec} {κ : Val}
    {ρ : WRes} (A : VTy) (n i : UInt32)
    (h : KapRel (Row.tab S δ) (fun ls v => vC true R ls δ v)
      (OpSig.ent δ ⟨n, i, q, A, B⟩) ls κ ρ) :
    vC true (kTy S R q B) ls δ κ ρ := by
  obtain ⟨hu, hk⟩ := h
  have hres : ∀ ls', Ext ls ls' ρ →
      cC (.arr B (CTy.effOf S R)) ls' δ (.app κ.1 (.val (Val.inj₁ .unit))) ρ := by
    intro ls' he w σ₁ σ₂ hB hc
    exact (cC_effOf S R ls' δ _ σ₂).mpr ((hk ls' he).1 w σ₁ σ₂ hB hc)
  have hcan : q ≠ .lin → ∀ ls', Ext ls ls' ρ →
      cC (CTy.effOf S .unit) ls' δ (.app κ.1 (.val (Val.inj₂ .unit))) ρ := by
    intro hq ls' he
    exact (cC_effOf S .unit ls' δ _ ρ).mpr ((hk ls' he).2 hq)
  cases q with
  | lin => exact fun ls' he => ⟨hres ls' he, trivial⟩
  | aff => exact fun ls' he => ⟨hres ls' he, hcan (by simp) ls' he⟩
  | unr => exact ⟨hu rfl, fun ls' he => ⟨hres ls' he, hcan (by simp) ls' he⟩⟩

/-- The clauses hold nothing. -/
theorem clausesTy_empty {S : Row} {R : VTy} {ls : List SRec} {δ : LSub} :
    ∀ (E : List (Qual × VTy × VTy)) {hs : Val} {ρ : WRes}, vC true (clausesTy S R E) ls δ hs ρ →
      ρ = PMap.empty
  | [], _, _, h => h.1
  | (q, A, B) :: E, hs, ρ, h => by
      obtain ⟨c, rest, h⟩ := h
      obtain ⟨-, ρ₁, ρ₂, hc, hc₁, hr⟩ := pure_sep_iff.mp h
      have he : ρ₁ = PMap.empty := by
        simp only [clauseTy] at hc₁; split at hc₁ <;> exact hc₁.1
      rw [he, clausesTy_empty E hr] at hc
      exact eq_of_compS_empty_left hc

private theorem substAll_var' {γ : List Val} {i : Nat} {v : Val} (hv : γ[i]? = some v) :
    substAll γ (.var i) = .val v := by
  show Expr.psub 0 γ (.var i) = _
  simp only [Expr.psub, if_neg (Nat.not_lt_zero i), Nat.sub_zero, hv, Val.shift_zero]

/-- An operation of the handler's name in `Σ` extended by the handler's effect is the effect's
`j`-th, at index `j`. -/
theorem Row.tab_ofEff_self {S : Row} {E : List (Qual × VTy × VTy)} {n : UInt32} {δ : LSub}
    (hnS : ∀ o ∈ S, o.n ≠ n) (hlen : E.length ≤ 2 ^ 32) {i : UInt32} {en : OpEnt}
    (hT : Row.tab (Row.ofEff n E 0 ++ S) δ n i = some en) :
    ∃ j, ∃ hj : j < E.length, i.toNat = j ∧ i = UInt32.ofNat (0 + j) ∧
      en = OpSig.ent δ ⟨n, UInt32.ofNat (0 + j), E[j].1, E[j].2.1, E[j].2.2⟩ := by
  obtain ⟨o, hf, rfl⟩ := Row.tab_some hT
  have hfo : Row.find (Row.ofEff n E 0) n i = some o := by
    rw [Row.find_append] at hf
    cases h₁ : Row.find (Row.ofEff n E 0) n i with
    | some o' => rw [h₁] at hf; exact hf
    | none =>
        rw [h₁] at hf
        obtain ⟨hm, hn, -⟩ := Row.find_mem hf
        exact absurd hn (hnS o hm)
  obtain ⟨-, j, hj, rfl, rfl⟩ := Row.find_ofEff n E 0 n i o hfo
  have hjn : (UInt32.ofNat (0 + j)).toNat = j := by
    rw [Nat.zero_add]; exact UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega)
  exact ⟨j, hj, hjn, rfl, rfl⟩

/-- A handler records its effect's qualifiers: the tag at each operation's index is its
qualifier's.  `[spec §25]` -/
theorem capTag_ofEff {S : Row} {E : List (Qual × VTy × VTy)} {n : UInt32} {δ : LSub}
    (hnS : ∀ o ∈ S, o.n ≠ n) (hlen : E.length ≤ 2 ^ 32) (i : UInt32) (en : OpEnt)
    (hT : Row.tab (Row.ofEff n E 0 ++ S) δ n i = some en) :
    capTag (qualsVal (E.map Prod.fst)).1 i.toNat = en.q.tag := by
  obtain ⟨j, hj, hji, -, rfl⟩ := Row.tab_ofEff_self hnS hlen hT
  rw [hji, capTag_qualsVal _ j (by simpa using hj)]
  simp [OpSig.ent]

/-- **A handler at clause values**: the answer clause and the clauses related at `∅`, at one list
(at a `!` type the relation at one list gives it at every list, `ext_empty'`), and the handled
computation at `Σ` extended by the handler's name, which `Σ` does not hold.  The handler's tags are
its effect's qualifiers.  `[spec §19, §25]` -/
theorem ewp_handle_vals {S : Row} {E : List (Qual × VTy × VTy)} {n : UInt32} {A R : VTy}
    {δ : LSub} {ls₀ : List SRec} {vr vc : Val} (hn0 : n ≠ 0) (hnS : ∀ o ∈ S, o.n ≠ n)
    (hlen : E.length ≤ 2 ^ 32) (hVr : vC true (retTy S A R) ls₀ δ vr PMap.empty)
    (hVc : vC true (clausesTy S R E) ls₀ δ vc PMap.empty) {ls : List SRec} {e : Expr} {ρ : WRes}
    (he : ewpTS ls e (opTable (Row.tab (Row.ofEff n E 0 ++ S) δ)) (fun ls v => vC true A ls δ v) ρ) :
    ewpTS ls (hndE (hndVal n (qualsVal (E.map Prod.fst)) vr vc) e) (opTable (Row.tab S δ))
      (fun ls v => vC true R ls δ v) ρ := by
  refine ewp_handle (Row.tab (Row.ofEff n E 0 ++ S) δ) (Row.tab S δ) n hn0 ?_
    (qualsVal (E.map Prod.fst)) vr vc
    (fun ls v => vC true A ls δ v) (fun ls v => vC true R ls δ v)
    (fun i en hT _ => capTag_ofEff hnS hlen i en hT) ?_ ?_ he
  · intro m i hm
    simp [Row.tab, Row.find_append, Row.find_ofEff_ne n E 0 m i hm]
  · intro ls' v σ hv
    have hf := (hVr.2 ls' (ext_empty' ls₀ ls')) v σ σ hv (compS_empty_left σ)
    exact (cC_effOf S R ls' δ _ σ).mp hf
  · intro i en hT
    obtain ⟨o, hf, rfl⟩ := Row.tab_some hT
    have hfo : Row.find (Row.ofEff n E 0) n i = some o := by
      rw [Row.find_append] at hf
      cases h₁ : Row.find (Row.ofEff n E 0) n i with
      | some o' => rw [h₁] at hf; exact hf
      | none =>
          rw [h₁] at hf
          obtain ⟨hm, hn, -⟩ := Row.find_mem hf
          exact absurd hn (hnS o hm)
    obtain ⟨-, j, hj, rfl, rfl⟩ := Row.find_ofEff n E 0 n i o hfo
    have hjn : (UInt32.ofNat (0 + j)).toNat = j := by
      rw [Nat.zero_add]; exact UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega)
    obtain ⟨c, hcl, hVcl⟩ := clausesTy_at E hVc j hj
    refine ⟨c, by rw [hjn]; exact hcl, ?_, ?_⟩
    · intro hna ls' v κ σ hσ
      generalize hEj : E[j] = t at hVcl hna hσ
      obtain ⟨q, A', B'⟩ := t
      simp only [OpSig.ent, OpSig.abort] at hna
      simp only [clauseTy, hna] at hVcl
      obtain ⟨σa, σk, hck, hA', hK⟩ := hσ
      have hκ := vC_kTy_of_kapRel (S := S) (R := R) (B := B') (q := q) A' n (UInt32.ofNat (0 + j)) hK
      have hf := (hVcl.2 ls' (ext_empty' ls₀ ls')) (Val.pair v κ) σ σ
        ⟨v, κ, pure_sep_mk rfl ⟨σa, σk, hck, hA', hκ⟩⟩ (compS_empty_left σ)
      exact (cC_effOf S R ls' δ _ σ).mp hf
    · intro ha ls' v σ hσ
      generalize hEj : E[j] = t at hVcl ha hσ
      obtain ⟨q, A', B'⟩ := t
      simp only [OpSig.ent, OpSig.abort] at ha hσ
      simp only [clauseTy, ha] at hVcl
      have hf := (hVcl.2 ls' (ext_empty' ls₀ ls')) v σ σ hσ (compS_empty_left σ)
      exact (cC_effOf S R ls' δ _ σ).mp hf

/-- `[handle]`: the clauses and `h_ret` at `Σ`, the handled computation at `Σ` extended by the
handler's name, which `Σ` does not hold.  `[spec §19]` -/
theorem handle_compatC {Δ : LifeCtx} {Γ Γ₁ Γ₂ Γr Γc : Ctx VTy} {e : Expr} {S : Row}
    {E : List (Qual × VTy × VTy)} {n : UInt32} {A R : VTy} {ir ic : Nat}
    (hsp : Ctx.SplitP Γ Γ₁ Γ₂) (hsp₁ : Ctx.SplitP Γ₁ Γr Γc)
    (hr : Ctx.SoloP Γr ir (retTy S A R)) (hc : Ctx.SoloP Γc ic (clausesTy S R E))
    (hn0 : n ≠ 0) (hnS : ∀ o ∈ S, o.n ≠ n) (hlen : E.length ≤ 2 ^ 32)
    (he : SemC Δ Γ₂ e (CTy.effOf (Row.ofEff n E 0 ++ S) A)) :
    SemC Δ Γ (hndTerm n (E.map Prod.fst) ir ic e) (CTy.effOf S R) := by
  intro δ γ ls ρ hδ hg
  obtain ⟨ρ₁, ρ₂, hc12, hg₁, hg₂⟩ := gDenC_split hsp hg
  obtain ⟨ρr, ρcl, hcrc, hgr, hgc⟩ := gDenC_split hsp₁ hg₁
  obtain ⟨hlr, hsr⟩ := gDenC_iff.mp hgr
  obtain ⟨vr, hvr, hVr⟩ := gSepC_soloP hr (hr.lt_of_liveWithin hlr) hsr
  obtain ⟨hlc, hsc⟩ := gDenC_iff.mp hgc
  obtain ⟨vc, hvc, hVc⟩ := gSepC_soloP hc (hc.lt_of_liveWithin hlc) hsc
  have hρr : ρr = PMap.empty := hVr.1
  have hρc : ρcl = PMap.empty := clausesTy_empty E hVc
  subst hρr hρc
  rw [eq_of_compS_empty_left hcrc] at hc12
  rw [eq_of_compS_empty_left hc12]
  have hsub : substAll γ (hndTerm n (E.map Prod.fst) ir ic e) =
      Expr.app (Expr.app (.val (.prim .hnd)) (.pair (.val (Val.i32 n))
        (.pair (.val (qualsVal (E.map Prod.fst))) (.pair (substAll γ (.var ir))
          (substAll γ (.var ic)))))) (substAll γ e) := by
    simp only [hndTerm, substAll, Expr.psub, Expr.val, Val.prim, Val.i32, psub_qualsVal]
  show cC _ ls δ (substAll γ (hndTerm n (E.map Prod.fst) ir ic e)) ρ₂
  rw [hsub, substAll_var' hvr, substAll_var' hvc]
  exact (cC_effOf S R ls δ _ ρ₂).mpr (ewp_handle_vals hn0 hnS hlen hVr hVc
    ((cC_effOf _ A ls δ _ ρ₂).mp (he δ γ ls ρ₂ hδ hg₂)))

/-! ### The general `[handle]`: the handler as a value form  `[spec §24]` -/

/-- `handle_n e with H`, `H` the handler's pair `(h_ret, hs)` as an expression.  `hndTerm` is its
instance at two variables (`hndTerm_eq`).  `[spec §19, §24]` -/
def hndExpr (n : UInt32) (qs : List Qual) (H e : Expr) : Expr :=
  .app (.app (.val (.prim .hnd)) (.pair (.val (Val.i32 n)) (.pair (.val (qualsVal qs)) H))) e

theorem hndTerm_eq (n : UInt32) (qs : List Qual) (ir ic : Nat) (e : Expr) :
    hndTerm n qs ir ic e = hndExpr n qs (.pair (.var ir) (.var ic)) e := rfl

/-- A closing substitution of `handle_n e with H` closes `H` and `e`. -/
theorem psub_hndExpr (k : Nat) (γ : List Val) (n : UInt32) (qs : List Qual) (H e : Expr) :
    Expr.psub k γ (hndExpr n qs H e) = hndExpr n qs (Expr.psub k γ H) (Expr.psub k γ e) := by
  simp only [hndExpr, Expr.psub, Expr.val, Val.prim, Val.i32, psub_qualsVal]

theorem shift_hndExpr (d c : Nat) (n : UInt32) (qs : List Qual) (H e : Expr) :
    Expr.shift d c (hndExpr n qs H e) = hndExpr n qs (Expr.shift d c H) (Expr.shift d c e) := by
  simp only [hndExpr, Expr.shift, Expr.val, Val.prim, Val.i32, shift_qualsVal]

theorem subst_hndExpr (j : Nat) (s : Val) (n : UInt32) (qs : List Qual) (H e : Expr) :
    Expr.subst j s (hndExpr n qs H e) = hndExpr n qs (Expr.subst j s H) (Expr.subst j s e) := by
  simp only [hndExpr, Expr.subst, Expr.val, Val.prim, Val.i32, subst_qualsVal]

/-- `e` is a value form over the live slots of `Γ`: a value, a variable of a live slot, or a pair
or injection of these.  A closing substitution of `Γ` makes it a value
(`isVal_psub_valFormIn`).  `[spec §24]` -/
inductive _root_.BoCa.Expr.ValFormIn (Γ : Ctx VTy) : Expr → Prop where
  | var {i : Nat} {s : Slot VTy} (h : Γ[i]? = some s) (hl : s.live = true) :
      Expr.ValFormIn Γ (.var i)
  | val (v : Val) : Expr.ValFormIn Γ (.val v)
  | pair {a b : Expr} : Expr.ValFormIn Γ a → Expr.ValFormIn Γ b → Expr.ValFormIn Γ (.pair a b)
  | inj₁ {a : Expr} : Expr.ValFormIn Γ a → Expr.ValFormIn Γ (.inj₁ a)
  | inj₂ {a : Expr} : Expr.ValFormIn Γ a → Expr.ValFormIn Γ (.inj₂ a)

/-- A live slot is within the closing substitution. -/
theorem liveWithin_lt : ∀ {Γ : Ctx VTy} {γ : List Val} {i : Nat} {s : Slot VTy},
    Ctx.LiveWithin Γ γ → Γ[i]? = some s → s.live = true → i < γ.length
  | [], _, _, _, _, h, _ => by simp at h
  | s₀ :: Γ, [], 0, s, hw, h, hl => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      exact absurd hl (by simpa using hw.1)
  | s₀ :: Γ, [], i + 1, s, hw, h, hl => by
      have := liveWithin_lt hw.2 (by simpa using h) hl
      simp at this
  | s₀ :: Γ, _ :: γ, 0, _, _, _, _ => by simp
  | s₀ :: Γ, _ :: γ, i + 1, s, hw, h, hl => by
      simpa using liveWithin_lt (Γ := Γ) (γ := γ) hw (by simpa using h) hl

/-- A closing substitution keeps a value a value. -/
theorem isVal_psub {e : Expr} (h : IsVal e) (k : Nat) (γ : List Val) : IsVal (Expr.psub k γ e) := by
  induction h generalizing k with
  | unit => exact .unit
  | pair _ _ ih₁ ih₂ => exact .pair (ih₁ k) (ih₂ k)
  | inj₁ _ ih => exact .inj₁ (ih k)
  | inj₂ _ ih => exact .inj₂ (ih k)
  | lam => exact .lam
  | loc => exact .loc
  | prim => exact .prim
  | storeV _ ih => exact .storeV (ih k)

/-- **A value form, closed, is a value.** -/
theorem isVal_psub_valFormIn {Γ : Ctx VTy} {γ : List Val} (hw : Ctx.LiveWithin Γ γ) {e : Expr}
    (h : e.ValFormIn Γ) : IsVal (Expr.psub 0 γ e) := by
  induction h with
  | @var i s hs hl =>
      have hi := liveWithin_lt hw hs hl
      obtain ⟨v, hv⟩ : ∃ v, γ[i]? = some v := ⟨γ[i], List.getElem?_eq_getElem hi⟩
      simp only [Expr.psub, if_neg (Nat.not_lt_zero i), Nat.sub_zero, hv]
      exact (v.shift 0 0).2
  | val v => exact isVal_psub v.2 0 γ
  | pair _ _ ih₁ ih₂ => exact .pair ih₁ ih₂
  | inj₁ _ ih => exact .inj₁ ih
  | inj₂ _ ih => exact .inj₂ ih

theorem _root_.BoCa.Expr.ValFormIn.append {Γ Γ' : Ctx VTy} {e : Expr} (h : e.ValFormIn Γ) :
    e.ValFormIn (Γ ++ Γ') := by
  induction h with
  | @var i s hs hl =>
      refine .var ?_ hl
      have hi : i < Γ.length := by
        by_contra hn
        rw [List.getElem?_eq_none (by omega)] at hs
        cases hs
      rw [List.getElem?_append_left hi]
      exact hs
  | val v => exact .val v
  | pair _ _ ih₁ ih₂ => exact .pair ih₁ ih₂
  | inj₁ _ ih => exact .inj₁ ih
  | inj₂ _ ih => exact .inj₂ ih

/-- `h_ret`'s type is persistent. -/
theorem retTy_persistent (S : Row) (A R : VTy) : (retTy S A R).Persistent := rfl

/-- The clauses' type is persistent: a tuple of `!` types. -/
theorem clausesTy_persistent (S : Row) (R : VTy) :
    ∀ E : List (Qual × VTy × VTy), (clausesTy S R E).Persistent
  | [] => rfl
  | (q, A, B) :: E => by
      have h := clausesTy_persistent S R E
      simp only [VTy.Persistent] at h ⊢
      simp only [clausesTy, VTy.persistent, Bool.and_eq_true, h, and_true]
      simp only [clauseTy]
      split <;> rfl

/-- A context of one live persistent slot, up to persistent slots elsewhere, is consumed up to
persistent slots. -/
theorem _root_.BoCa.Fig16.LogRel.Core.Ctx.SoloP.deadP {T : VTy} (hT : T.Persistent) :
    ∀ {Γ : Ctx VTy} {i : Nat}, Ctx.SoloP Γ i T → Ctx.DeadP Γ
  | _, _, .here h => .drop hT h
  | _, _, .there h => .cons (Ctx.SoloP.deadP hT h)
  | _, _, .skip hS h => .drop hS (Ctx.SoloP.deadP hT h)

/-- Two consumed halves, up to persistent slots, make a consumed whole. -/
theorem _root_.BoCa.Fig16.LogRel.Core.Ctx.SplitP.deadP :
    ∀ {Γ Γ₁ Γ₂ : Ctx VTy}, Ctx.SplitP Γ Γ₁ Γ₂ → Ctx.DeadP Γ₁ → Ctx.DeadP Γ₂ → Ctx.DeadP Γ
  | _, _, _, .nil, _, _ => .nil
  | _, _, _, .left h, .drop hT h₁, .cons h₂ => .drop hT (Ctx.SplitP.deadP h h₁ h₂)
  | _, _, _, .right h, .cons h₁, .drop hT h₂ => .drop hT (Ctx.SplitP.deadP h h₁ h₂)
  | _, _, _, .dead h, .cons h₁, .cons h₂ => .cons (Ctx.SplitP.deadP h h₁ h₂)
  | _, _, _, .dup hT h, .drop _ h₁, .drop _ h₂ => .drop hT (Ctx.SplitP.deadP h h₁ h₂)

/-- The slot of `SoloP` is live. -/
theorem _root_.BoCa.Fig16.LogRel.Core.Ctx.SoloP.live :
    ∀ {Γ : Ctx VTy} {i : Nat} {T : VTy}, Ctx.SoloP Γ i T → ∃ s, Γ[i]? = some s ∧ s.live = true
  | _, _, _, .here _ => ⟨_, rfl, rfl⟩
  | _, _, _, .there h => by simpa using Ctx.SoloP.live h
  | _, _, _, .skip _ h => by simpa using Ctx.SoloP.live h

/-- A slot live in a part of a split is live in the whole. -/
theorem _root_.BoCa.Fig16.LogRel.Core.Ctx.SplitP.live_left :
    ∀ {Γ Γ₁ Γ₂ : Ctx VTy} {i : Nat} {s : Slot VTy}, Ctx.SplitP Γ Γ₁ Γ₂ → Γ₁[i]? = some s →
      s.live = true → ∃ s', Γ[i]? = some s' ∧ s'.live = true
  | _, _, _, _, _, .nil, h, _ => by simp at h
  | _, _, _, 0, _, .left _, h, _ => ⟨_, rfl, rfl⟩
  | _, _, _, 0, _, .right _, h, hl => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h; subst h; cases hl
  | _, _, _, 0, _, .dead _, h, hl => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h; subst h; cases hl
  | _, _, _, 0, _, .dup _ _, h, _ => ⟨_, rfl, rfl⟩
  | _, _, _, i + 1, _, .left hs, h, hl => by simpa using Ctx.SplitP.live_left hs (by simpa using h) hl
  | _, _, _, i + 1, _, .right hs, h, hl => by simpa using Ctx.SplitP.live_left hs (by simpa using h) hl
  | _, _, _, i + 1, _, .dead hs, h, hl => by simpa using Ctx.SplitP.live_left hs (by simpa using h) hl
  | _, _, _, i + 1, _, .dup _ hs, h, hl => by simpa using Ctx.SplitP.live_left hs (by simpa using h) hl

theorem _root_.BoCa.Fig16.LogRel.Core.Ctx.SplitP.live_right :
    ∀ {Γ Γ₁ Γ₂ : Ctx VTy} {i : Nat} {s : Slot VTy}, Ctx.SplitP Γ Γ₁ Γ₂ → Γ₂[i]? = some s →
      s.live = true → ∃ s', Γ[i]? = some s' ∧ s'.live = true
  | _, _, _, _, _, .nil, h, _ => by simp at h
  | _, _, _, 0, _, .left _, h, hl => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h; subst h; cases hl
  | _, _, _, 0, _, .right _, h, _ => ⟨_, rfl, rfl⟩
  | _, _, _, 0, _, .dead _, h, hl => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h; subst h; cases hl
  | _, _, _, 0, _, .dup _ _, h, _ => ⟨_, rfl, rfl⟩
  | _, _, _, i + 1, _, .left hs, h, hl => by simpa using Ctx.SplitP.live_right hs (by simpa using h) hl
  | _, _, _, i + 1, _, .right hs, h, hl => by simpa using Ctx.SplitP.live_right hs (by simpa using h) hl
  | _, _, _, i + 1, _, .dead hs, h, hl => by simpa using Ctx.SplitP.live_right hs (by simpa using h) hl
  | _, _, _, i + 1, _, .dup _ hs, h, hl => by simpa using Ctx.SplitP.live_right hs (by simpa using h) hl

/-- A run from a value takes no step. -/
theorem arun_val {Al : BoCa.BoLo.Alloc} {k k' : Nat} {μ μ' : Heap} {v : Val} {e : Expr}
    (h : BoCa.BoLo.ARun (ℍ := ℍ) Al k μ (.val v) k' μ' e) : e = .val v := by
  cases h with
  | refl => rfl
  | more s _ => exact (BoCa.BoLo.no_step_val s.toStep1).elim

/-- **At a value, under a frame of the world, `wpTS`'s postcondition holds**, at a list with the
same members: the run from a value takes no step. -/
theorem wpTS_val_post {ls : List SRec} {v : Val} {Q : List SRec → Val → WProp} {ρ ρf fρ : WRes}
    {ps : List FrameRec} (h : wpTS ls (.val v) Q ρ) (hf : ResU.Hash ρf ρ)
    (hc : ResU.CompS ρf ρ fρ) (hT : TW fρ ps (rsOf ls)) (htg : Tagged fρ ps ls) :
    ∃ ls' ρ', (∀ x, x ∈ ls' ↔ x ∈ ls) ∧ Q ls' v ρ' := by
  obtain ⟨ρ', _, _, _, _, w, _, _, _, ls', _, _, _, _, _, _, ⟨_, hrun⟩, _, _, _, _, _, _, hls, hQ⟩ :=
    h ρf fρ ps hf hc hT htg BoCa.BoLo.Alloc.leastFree 0
  have hw : w = v := Val.ext (by simpa using arun_val hrun)
  subst hw
  exact ⟨ls', ρ', hls, hQ⟩

/-- **The general `[handle]`**: `handle_n e with H`, `H` a value form over a context whose live
slots are persistent, typed at the answer clause's and the clauses' types; the handled
computation at `Σ` extended by the handler's name.  `H` closes to a value; its relation is read off
`wpTS` at that value under the frame the run starts in (`wpTS_val_post`), and the handler is
`ewp_handle_vals`.  `[spec §24]` -/
theorem handleV_compatC {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {H e : Expr} {S : Row}
    {E : List (Qual × VTy × VTy)} {n : UInt32} {A R : VTy}
    (hsp : Ctx.SplitP Γ Γ₁ Γ₂) (hd : Ctx.DeadP Γ₁) (hH : H.ValFormIn Γ₁)
    (hc : SemV Δ Γ₁ H (.tensor (retTy S A R) (clausesTy S R E)))
    (hn0 : n ≠ 0) (hnS : ∀ o ∈ S, o.n ≠ n) (hlen : E.length ≤ 2 ^ 32)
    (he : SemC Δ Γ₂ e (CTy.effOf (Row.ofEff n E 0 ++ S) A)) :
    SemC Δ Γ (hndExpr n (E.map Prod.fst) H e) (CTy.effOf S R) := by
  intro δ γ ls ρ hδ hg
  obtain ⟨ρ₁, ρ₂, hc12, hg₁, hg₂⟩ := gDenC_split hsp hg
  obtain ⟨hlw₁, hs₁⟩ := gDenC_iff.mp hg₁
  have hρ₁ : ρ₁ = PMap.empty := gSepC_deadP hd hs₁
  subst hρ₁
  rw [eq_of_compS_empty_left hc12]
  have hval : IsVal (substAll γ H) := isVal_psub_valFormIn hlw₁ hH
  have hH' := hc δ γ ls PMap.empty hδ hg₁
  have hE' := (cC_effOf _ A ls δ _ ρ₂).mp (he δ γ ls ρ₂ hδ hg₂)
  show cC _ ls δ (Expr.psub 0 γ (hndExpr n (E.map Prod.fst) H e)) ρ₂
  rw [psub_hndExpr]
  show cC _ ls δ (hndExpr n (E.map Prod.fst) (substAll γ H) (substAll γ e)) ρ₂
  refine (cC_effOf S R ls δ _ ρ₂).mpr (ewp_fold (opTable_mono _) ?_)
  intro ρf fρ ps hf hcf hT htg Al k
  obtain ⟨ls', ρ', -, hv⟩ := wpTS_val_post (v := ⟨substAll γ H, hval⟩) hH'
    (ResU.hash_empty_right (hash_valid_comp hf hcf)) (ResU.comp_empty_right fρ) hT htg
  have hT₀ : (VTy.tensor (retTy S A R) (clausesTy S R E)).Persistent := by
    simp only [VTy.Persistent, VTy.persistent, Bool.and_eq_true]
    exact ⟨retTy_persistent S A R, clausesTy_persistent S R E⟩
  have hρ' : ρ' = PMap.empty := vP_empty_of_persistent hT₀ hv
  subst hρ'
  obtain ⟨vr, vc, h⟩ := hv
  obtain ⟨hpair, σ₁, σ₂, -, hVr, hVc⟩ := pure_sep_iff.mp h
  have hσ₁ : σ₁ = PMap.empty := vP_empty_of_persistent (retTy_persistent S A R) hVr
  have hσ₂ : σ₂ = PMap.empty := vP_empty_of_persistent (clausesTy_persistent S R E) hVc
  subst hσ₁ hσ₂
  have hHe : substAll γ H = (Val.pair vr vc).1 := congrArg Subtype.val hpair
  rw [hHe]
  exact ewp_unfold (opTable_mono _) (ewp_handle_vals hn0 hnS hlen hVr hVc hE')
    ρf fρ ps hf hcf hT htg Al k

/-! ### `[then]` at option A  `[spec §24]` -/

/-- **`[then]` with a finaliser that lets no raise escape** (option A, decision D3): the finaliser
at the pure row.  `[spec §24]` -/
theorem thenA_compatC {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {M N D : Expr} {A B : VTy} {S : Row}
    (hsp : Ctx.SplitP Γ Γ₁ Γ₂) (hNZ : S.NZ) (hUq : S.Uniq) (hU : S.Unr → Persistent Γ₂)
    (hM : SemC Δ Γ₁ M (CTy.effOf S A)) (hN : SemC Δ (⟨A, true⟩ :: Γ₂) N (CTy.effOf S B))
    (hD : SemC Δ (⟨.unit, false⟩ :: Γ₂) D (.ret .unit)) :
    SemC Δ Γ (thenE N D M) (CTy.effOf S B) :=
  then_compatC hsp hNZ hUq hU hM hN
    (sub_compatC (S := []) (fun _ _ _ h => by simp [Row.find] at h) hD)

end BoCa.Fig16.LogRel.Core
