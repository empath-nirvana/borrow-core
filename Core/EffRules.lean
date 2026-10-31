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

/-- **A cancellable wait** (`[await-c]`): a marked (`OpSig.rc`) must-resume operation answering
`1 ⊕ 1`, "go on" or "cancelled". A cancel is a resume with `inr ()`.  `[spec §29a]` -/
def OpSig.Cancellable (o : OpSig) : Prop :=
  o.rc = true ∧ o.q = .lin ∧ o.B = .sum .unit .unit

/-- `OpSig.Cancellable`, decided. -/
def OpSig.cancellableB (o : OpSig) : Bool := o.rc && o.q == .lin && o.B.isNextB

theorem VTy.isUnitB_iff (A : VTy) : A.isUnitB = true ↔ A = .unit := by
  cases A <;> simp [VTy.isUnitB]

theorem VTy.isNextB_iff (B : VTy) : B.isNextB = true ↔ B = .sum .unit .unit := by
  cases B <;> simp [VTy.isNextB, VTy.isUnitB_iff]

theorem OpSig.cancellableB_iff (o : OpSig) : o.cancellableB = true ↔ o.Cancellable := by
  simp [OpSig.cancellableB, OpSig.Cancellable, VTy.isNextB_iff, and_assoc]

/-- **The cancel target** of a cancellable wait: the marked abortive `cancelled : 1 ↠ 0` that
`[await-c]` raises on the answer `inr ()`.  `[spec §29a]` -/
def OpSig.CancelTarget (o : OpSig) : Prop :=
  o.rc = true ∧ o.abort = true ∧ o.A = .unit

/-- `OpSig.CancelTarget`, decided. -/
def OpSig.cancelTargetB (o : OpSig) : Bool := o.rc && o.abort && o.A.isUnitB

theorem OpSig.cancelTargetB_iff (o : OpSig) : o.cancelTargetB = true ↔ o.CancelTarget := by
  simp [OpSig.cancelTargetB, OpSig.CancelTarget, VTy.isUnitB_iff, and_assoc]

/-- An entry whose cancel row typing reads: a capturable one (§27), or a marked one that is not
abortive (a cancellable wait), whose cancel is a resume with `inr ()` that unwinds through the
finalisers between it and its handler.  `[spec §27, §29a]` -/
def OpSig.finRead (o : OpSig) : Bool := capB o.q o.B || (o.rc && !o.abort)

theorem OpSig.finRead_of_capB {o : OpSig} (h : capB o.q o.B = true) : o.finRead = true := by
  simp [OpSig.finRead, h]

/-- The entry of an operation at `δ`, with its cancel row's obligation at a capturable operation.
-/
def OpSig.ent (δ : LSub) (o : OpSig) : OpEnt :=
  ⟨o.q, o.abort, fun ls v => vC true o.A ls δ v, fun ls v => vC true o.B ls δ v,
    if capB o.q o.B then finObl o.fin δ else none⟩

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

/-- The row holds `Div`: the operation it finds at `(divEff, 0)` is `tick`.  `[spec §14]` -/
def Row.divB (S : Row) : Bool := (CTy.effOf S .unit).divAt

theorem divAt_effOf : ∀ (S : Row) (R : VTy), (CTy.effOf S R).divAt = Row.divB S
  | [], _ => rfl
  | o :: S, R => by
      simp only [Row.divB, CTy.effOf, CTy.divAt]
      rw [show (CTy.effOf S R).divAt = (CTy.effOf S .unit).divAt from
        (divAt_effOf S R).trans rfl]

/-- **The relation at a row** is the relation at its table: `cwp` where it holds `Div`, `ewpTS`
elsewhere.  `[spec §14, §19]` -/
theorem cC_effOf_wp (S : Row) (R : VTy) (ls : List SRec) (δ : LSub) (e : Expr) (ρ : WRes) :
    cC (CTy.effOf S R) ls δ e ρ ↔
      effWp (Row.divB S) (Row.tab S δ) (fun ls v => vC true R ls δ v) ls e ρ := by
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
      have hd := divAt_effOf (o :: S) R
      simp only [CTy.effOf] at h hr hd
      simp only [CTy.effOf, cC]
      rw [show OpTab.ext o.n o.i ⟨o.q, o.B.isZero && o.q != .lin, fun ls v => vCE none true o.A ls δ v,
          fun ls v => vCE none true o.B ls δ v, if capB o.q o.B then finObl o.fin δ else none⟩
          (effTab (CTy.effOf S R) δ) = Row.tab (o :: S) δ from h,
        show effRet (CTy.effOf S R) δ = _ from hr, hd]

/-- **The relation at a row that does not hold `Div`** is `ewpTS` at its table.  `[spec §19]` -/
theorem cC_effOf (S : Row) (R : VTy) (ls : List SRec) (δ : LSub) (e : Expr) (ρ : WRes)
    (hS : Row.divB S = false) :
    cC (CTy.effOf S R) ls δ e ρ ↔
      ewpTS ls e (opTable (Row.tab S δ)) (fun ls v => vC true R ls δ v) ρ := by
  rw [cC_effOf_wp, hS]; rfl

/-! ### Stopping at an operation -/

/-- A `perform` stops at once; its continuation (the hole) answers `Q` at every answer in `PB`,
and its cancel run, of the empty region, holds at the entry's cancel obligation (`hfin`).
`[spec §19]` -/
theorem ewp_perform_here {T : OpTab} {n i : UInt32} {en : OpEnt} (hT : T n i = some en)
    (ha : en.abort = false) (hfin : ∀ ls, cancelOK en ls .hole PMap.empty) {ls : List SRec}
    {v : Val} {Q : List SRec → Val → WProp}
    (hQ : ∀ ls' w ρ, en.PB ls' w ρ → Q ls' w ρ) {ρ : WRes} (h : en.PA ls v ρ) :
    ewpTS ls (performE (.val (opPayload n i v))) (opTable T) Q ρ := by
  refine ewp_fold (opTable_mono T) (wpG_here _ _ _ ρ (Or.inr (Or.inl
    ⟨.hole, n, i, v, en, pure_sep_mk ⟨rfl, rfl, hT, ha⟩
      ⟨ρ, PMap.empty, ResU.comp_empty_right ρ, h, ?_⟩⟩)))
  refine ⟨fun _ => rfl, fun ls' _ => ⟨fun w σ₁ σ₂ hB hc => ?_, fun _ => hfin ls'⟩⟩
  rw [eq_of_compS_empty_left hc]
  exact ewp_val (opTable_mono T) (hQ _ _ _ hB)

/-- A `raise` stops at once, at an argument that holds nothing owned.  `[spec §19]` -/
theorem ewp_raise_here {T : OpTab} {n i : UInt32} {en : OpEnt} (hT : T n i = some en)
    (ha : en.abort = true) {ls : List SRec} {v : Val} {Q : List SRec → Val → WProp} {ρ : WRes}
    (h : en.PA ls v ρ) (hn : NoOwn ρ) :
    ewpTS ls (raiseE (.val (opPayload n i v))) (opTable T) Q ρ :=
  ewp_fold (opTable_mono T) (wpG_here _ _ _ ρ (Or.inr (Or.inr
    ⟨.hole, n, i, v, en, pure_sep_mk ⟨rfl, rfl, hT, ha⟩
      ⟨ρ, PMap.empty, ResU.comp_empty_right ρ, ⟨h, hn⟩, noOwn_empty⟩⟩)))

/-- The cancel run of the empty region at a cancel table: it ends at once, keeping no error. -/
theorem cancelObl_start (T : OpTab) (ls : List SRec) :
    cancelObl T ls (raiseE (.val (cancelVal none))) PMap.empty :=
  ewp_fold (cancelTab_mono T) (wpG_here _ _ _ _ (Or.inr (Or.inl
    ⟨.hole, none, pure_sep_mk ⟨rfl, rfl⟩
      ⟨PMap.empty, PMap.empty, ResU.comp_empty_right _, ⟨rfl, trivial⟩, noOwn_empty⟩⟩)))

/-! ### Growing the row -/

/-- One cancel obligation below another: below `⊤`'s (`none`) everything is, and `⊤`'s is below
only `⊤`'s.  `[spec §27]` -/
def FinLeS : Option (List SRec → Expr → WProp) → Option (List SRec → Expr → WProp) → Prop
  | _, none => True
  | none, some _ => False
  | some P, some P' => ∀ ls e ρ, P ls e ρ → P' ls e ρ

theorem FinLeS.refl : ∀ (P : Option (List SRec → Expr → WProp)), FinLeS P P
  | none => trivial
  | some _ => fun _ _ _ h => h

theorem FinLeS.trans : ∀ {P P' P'' : Option (List SRec → Expr → WProp)},
    FinLeS P P' → FinLeS P' P'' → FinLeS P P''
  | _, _, none, _, _ => trivial
  | none, none, some _, _, h => h
  | none, some _, some _, h, _ => h.elim
  | some _, none, some _, _, h => h.elim
  | some _, some _, some _, h, h' => fun ls e ρ hp => h' ls e ρ (h ls e ρ hp)

/-- `en ≤ en′`: the same operation, and at a capturable one a weaker cancel obligation.
`[spec §27]` -/
def OpEnt.Le (en en' : OpEnt) : Prop :=
  en.q = en'.q ∧ en.abort = en'.abort ∧ en.PA = en'.PA ∧ en.PB = en'.PB ∧
    (en.abort = false → en.q ≠ .lin → FinLeS en.fin en'.fin)

theorem OpEnt.Le.refl (en : OpEnt) : en.Le en :=
  ⟨rfl, rfl, rfl, rfl, fun _ _ => FinLeS.refl _⟩

theorem OpEnt.Le.trans {en en' en'' : OpEnt} (h : en.Le en') (h' : en'.Le en'') : en.Le en'' :=
  ⟨h.1.trans h'.1, h.2.1.trans h'.2.1, h.2.2.1.trans h'.2.2.1, h.2.2.2.1.trans h'.2.2.2.1,
    fun ha hq => FinLeS.trans (h.2.2.2.2 ha hq)
      (h'.2.2.2.2 (h.2.1 ▸ ha) (h.1 ▸ hq))⟩

/-- `T` is included in `T′`: every entry of `T` is below `T′`'s at its key.  `[spec §19, §27]` -/
def OpTab.Le (T T' : OpTab) : Prop :=
  ∀ n i en, T n i = some en → ∃ en', T' n i = some en' ∧ en.Le en'

theorem OpTab.Le.refl (T : OpTab) : T.Le T := fun _ _ en h => ⟨en, h, OpEnt.Le.refl en⟩

theorem OpTab.Le.trans {T T' T'' : OpTab} (h : T.Le T') (h' : T'.Le T'') : T.Le T'' := by
  intro n i en hT
  obtain ⟨en', hT', hle⟩ := h n i en hT
  obtain ⟨en'', hT'', hle'⟩ := h' n i en' hT'
  exact ⟨en'', hT'', hle.trans hle'⟩

/-- A cancel obligation grows with the entry. -/
theorem cancelOK_le {en en' : OpEnt} (h : en.Le en') (ha : en.abort = false)
    (hq : en.q ≠ .lin) {ls : List SRec} {K : Kont} {ρ : WRes} (hc : cancelOK en ls K ρ) :
    cancelOK en' ls K ρ := by
  intro P' hP'
  have hf := h.2.2.2.2 ha hq
  rw [hP'] at hf
  cases hfin : en.fin with
  | none => rw [hfin] at hf; exact hf.elim
  | some P => rw [hfin] at hf; exact hf _ _ _ (hc P hfin)

/-- A continuation's share grows with the entry. -/
theorem contShare_le {en en' : OpEnt} (h : en.Le en') (ha : en.abort = false) {ls : List SRec}
    {K : Kont} {Φ : List SRec → Expr → WProp} {ρ : WRes} (hc : contShare en ls K Φ ρ) :
    contShare en' ls K Φ ρ := by
  have hq := h.1
  have hB := h.2.2.2.1
  refine ⟨fun hu => hc.1 (hq ▸ hu), fun ls' he => ⟨?_, fun hq' => ?_⟩⟩
  · rw [← hB]; exact (hc.2 ls' he).1
  · exact cancelOK_le h ha (hq ▸ hq') ((hc.2 ls' he).2 (hq ▸ hq'))

theorem errOk_le {T T' : OpTab} (hT : T.Le T') {ls : List SRec} :
    ∀ {err : Option Val} {ρ : WRes}, errOk T ls err ρ → errOk T' ls err ρ
  | none, _, h => h
  | some _, _, ⟨m, j, w, en, h⟩ => by
      obtain ⟨⟨h₁, h₃, h₄⟩, h₅⟩ := pure_sep_iff.mp h
      obtain ⟨en', h₃', ⟨-, hab, hA, -, -⟩⟩ := hT _ _ _ h₃
      exact ⟨m, j, w, en', pure_sep_mk ⟨h₁, h₃', hab ▸ h₄⟩ (by rw [← hA]; exact h₅)⟩

theorem performStop_le {T T' : OpTab} (hT : T.Le T') {ls : List SRec} {t : Expr}
    {Φ : List SRec → Expr → WProp} {ρ : WRes} (h : performStop T ls t Φ ρ) :
    performStop T' ls t Φ ρ := by
  obtain ⟨K, n, i, v, en, h⟩ := h
  obtain ⟨⟨h₁, h₂, h₃, h₄⟩, ρa, ρk, hc, hA, hk⟩ := pure_sep_iff.mp h
  obtain ⟨en', h₃', hle⟩ := hT _ _ _ h₃
  refine ⟨K, n, i, v, en', pure_sep_mk ⟨h₁, h₂, h₃', hle.2.1 ▸ h₄⟩ ⟨ρa, ρk, hc, ?_, ?_⟩⟩
  · rw [← hle.2.2.1]; exact hA
  · exact contShare_le hle h₄ hk

theorem cancelTab_le {T T' : OpTab} (hT : T.Le T') {ls : List SRec} {t : Expr}
    {Φ : List SRec → Expr → WProp} {ρ : WRes} (h : cancelTab T ls t Φ ρ) :
    cancelTab T' ls t Φ ρ := by
  rcases h with ⟨K, err, h⟩ | h
  · obtain ⟨hp, ρ₁, ρ₂, hc, he, hn⟩ := pure_sep_iff.mp h
    exact Or.inl ⟨K, err, pure_sep_mk hp ⟨ρ₁, ρ₂, hc, errOk_le hT he, hn⟩⟩
  · exact Or.inr (performStop_le hT h)

/-- The protocol table grows with the operation table. -/
theorem opTable_le {T T' : OpTab} (hT : T.Le T') {ls : List SRec} {t : Expr}
    {Φ : List SRec → Expr → WProp} {ρ : WRes} (h : opTable T ls t Φ ρ) : opTable T' ls t Φ ρ := by
  rcases h with h | ⟨K, n, i, v, en, h⟩
  · exact Or.inl (performStop_le hT h)
  · obtain ⟨⟨h₁, h₂, h₃, h₄⟩, h₅⟩ := pure_sep_iff.mp h
    obtain ⟨en', h₃', ⟨-, hab, hA, -, -⟩⟩ := hT _ _ _ h₃
    exact Or.inr ⟨K, n, i, v, en', pure_sep_mk ⟨h₁, h₂, h₃', hab ▸ h₄⟩ (by rw [← hA]; exact h₅)⟩

/-- **A row may grow** (`[sub]`).  `[spec §19]` -/
theorem ewp_sub {T T' : OpTab} (hT : T.Le T') {ls : List SRec} {e : Expr}
    {Q : List SRec → Val → WProp} {ρ : WRes} (h : ewpTS ls e (opTable T) Q ρ) :
    ewpTS ls e (opTable T') Q ρ :=
  ewp_mono (opTable_mono T') (fun _ _ _ _ h => opTable_le hT h) (fun _ _ _ h => h) h

/-- A cancel obligation grows with its table. -/
theorem cancelObl_le {T T' : OpTab} (hT : T.Le T') {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : cancelObl T ls e ρ) : cancelObl T' ls e ρ :=
  ewp_mono (cancelTab_mono T') (fun _ _ _ _ h => cancelTab_le hT h) (fun _ _ _ h => h) h

/-- **Garbage before a run**: a part of the resource with no `own` cell is left behind at the run's
first stop or answer, joining `wpG`'s leftover. -/
theorem ewp_absorb {Tb : Table} (hTb : Tb.Mono) {ls : List SRec} {e : Expr}
    {Q : List SRec → Val → WProp} {ρ σ ρ' : WRes} (h : ewpTS ls e Tb Q ρ) (hσ : NoOwn σ)
    (hc : ResU.CompS ρ σ ρ') : ewpTS ls e Tb Q ρ' := by
  refine ewp_fold hTb (wpG_garbage ?_)
  refine wpG_mono (fun ls' t τ ht => ?_) (wpG_frame (e := e) (fun _ τ => NoOwn τ)
    (fun _ _ _ h => h) ρ' ⟨ρ, σ, hc, ewp_unfold hTb h, hσ⟩)
  obtain ⟨τ₁, τ₂, hcτ, hp, hn⟩ := ht
  exact ⟨τ₁, τ₂, hcτ, hn, hp⟩

/-! ### A frame around a stopped computation -/

/-- **A cancel run under a plain context** `K`, which holds no handler and catches nothing, beside
a frame `σ` holding nothing owned, and nothing at all where the run may stop at an unrestricted
operation: the cancel's end leaves the context and the frame behind; a stop at an operation keeps
both in its continuation, whose own cancel carries through `K` (`hK`).  `[spec §19, §27]` -/
theorem cancel_frame {T T' : OpTab} (K : Kont) (hH : ∀ n, K.HasHnd n = false)
    (hC : K.Catches 0 = false) (hT : T.Le T') {σ : WRes} (hσ : NoOwn σ)
    (hU : ∀ n i en, T n i = some en → en.abort = false → en.q = .unr → σ = PMap.empty)
    (hK : ∀ n i en, T n i = some en → en.abort = false → en.q ≠ .lin →
      ∀ ls K₁ ρ ρ', cancelOK en ls K₁ ρ → ResU.CompS ρ σ ρ' → cancelOK en ls (K.comp K₁) ρ') :
    ∀ {ls : List SRec} {e : Expr} {ρ : WRes}, ewpTS ls e (cancelTab T) (fun _ _ _ => False) ρ →
      ∀ {ρ' : WRes}, ResU.CompS ρ σ ρ' →
        ewpTS ls (K.plug e) (cancelTab T') (fun _ _ _ => False) ρ' := by
  intro ls e ρ h
  refine ewp_ind (fun ls e ρ => ∀ {ρ' : WRes}, ResU.CompS ρ σ ρ' →
    ewpTS ls (K.plug e) (cancelTab T') (fun _ _ _ => False) ρ') ?_ h
  intro ls e ρ hs ρ' hc
  refine ewp_fold (cancelTab_mono T') (wpG_bind K e ls _ ρ' ?_)
  have h₁ := wpG_frame (e := e) (fun _ τ => τ = σ) (fun _ _ _ h => h) ρ' ⟨ρ, σ, hc, hs, rfl⟩
  refine wpG_mono (fun ls' t τ ht => ?_) h₁
  obtain ⟨τ₁, τ₂, hcτ, hp, rfl⟩ := ht
  rcases hp with ⟨_, _, hv⟩ | hp
  · exact hv.elim
  refine wpG_here _ _ _ τ (Or.inr ?_)
  rcases hp with ⟨K', err, hs'⟩ | ⟨K₁, n, i, v, en, hp⟩
  · -- the cancel's end: the context and the frame are left behind
    obtain ⟨⟨rfl, hK'⟩, τa, τb, hcab, he, hnb⟩ := pure_sep_iff.mp hs'
    refine Or.inl ⟨K.comp K', err, pure_sep_mk ⟨(Kont.plug_comp _ _ _).symm, ?_⟩ ?_⟩
    · rw [catches_comp, hC, hK']; rfl
    · obtain ⟨z, hz, hcz⟩ := compS_reassoc hcab hcτ
      exact ⟨τa, z, hcz, errOk_le hT he, noOwn_compS hz hnb hσ⟩
  · -- an operation: the context and the frame join its continuation
    obtain ⟨⟨rfl, hK₁, hT₁, ha⟩, ρa, ρk, hcak, hA, hu, hcont⟩ := pure_sep_iff.mp hp
    obtain ⟨ρk', hk', hcσ'⟩ := compS_reassoc hcak hcτ
    obtain ⟨en', hT', hle⟩ := hT _ _ _ hT₁
    refine Or.inr ⟨K.comp K₁, n, i, v, en', pure_sep_mk ⟨(Kont.plug_comp _ _ _).symm, ?_, hT',
      hle.2.1 ▸ ha⟩ ⟨ρa, ρk', hcσ', by rw [← hle.2.2.1]; exact hA, ?_⟩⟩
    · rw [hasHnd_comp, hH, hK₁]; rfl
    refine contShare_le hle ha ⟨fun hq => ?_, fun ls'' he => ⟨fun w τ₁ τ₂ hB hcτ' => ?_,
      fun hq => ?_⟩⟩
    · rw [hu hq, hU n i en hT₁ ha hq] at hk'
      exact eq_of_compS_empty_left hk'
    · obtain ⟨z, hz, hcz⟩ := compS_exch hk' hcτ'
      rw [Kont.plug_comp]
      exact (hcont ls'' (he.left hk')).1 w τ₁ z hB hz hcz
    · exact hK n i en hT₁ ha hq ls'' K₁ ρk ρk' ((hcont ls'' (he.left hk')).2 hq) hk'

/-- The cancel obligations of `T`'s capturable entries carry through a plain context, which holds
no handler and catches nothing, beside no frame.  `[spec §27]` -/
def OpTab.PlainCancel (T : OpTab) : Prop :=
  ∀ n i en, T n i = some en → en.abort = false → en.q ≠ .lin →
    ∀ K : Kont, (∀ m, K.HasHnd m = false) → K.Catches 0 = false →
      ∀ ls K₁ ρ, cancelOK en ls K₁ ρ → cancelOK en ls (K.comp K₁) ρ

/-- **A plain frame around an effectful computation**, at `opTable T` with a table `Px` beside it
whose stops owe nothing to the least fixed point.  `K` holds no handler and catches nothing
(`M to x. N`'s `(λx. N) [·]`); the frame `Fr` (the context of `N`) is carried through every stop
of the computation in the hole: resumed with it, at an abortive stop left behind, holding nothing
owned, and at a cancel carried through `K` by the entry's cancel obligation (`hK`).  At an
unrestricted operation the frame is empty.  A stop of `Px` with the frame is one of `Px'`
(`hPx`): a tick at a row holding `Div` (`Core/Div.lean`).  `[spec §14, §19, §27]` -/
theorem ewp_frame_plain_or (T T' : OpTab) (hTT : T.Le T') (Px Px' : Table) (hPx' : Px'.Mono)
    (K : Kont)
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
    (hk : ∀ ls v, Entails (Q₁ ls v ⋆ Fr ls) (ewpTS ls (K.plug (.val v)) (orTab (opTable T') Px') Q)) :
    ∀ {ls : List SRec} {e : Expr} {ρ : WRes}, ewpTS ls e (orTab (opTable T) Px) Q₁ ρ →
      ∀ {ρ₂ ρ' : WRes}, Fr ls ρ₂ → ResU.CompS ρ ρ₂ ρ' →
        ewpTS ls (K.plug e) (orTab (opTable T') Px') Q ρ' := by
  have hM := orTab_mono (opTable_mono T') hPx'
  intro ls e ρ h
  refine ewp_ind (fun ls e ρ => ∀ {ρ₂ ρ' : WRes}, Fr ls ρ₂ → ResU.CompS ρ ρ₂ ρ' →
    ewpTS ls (K.plug e) (orTab (opTable T') Px') Q ρ') ?_ h
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
      obtain ⟨en', hT', hle⟩ := hTT _ _ _ hT
      refine Or.inl ⟨K.comp K₁, n, i, v, en', pure_sep_mk ⟨(Kont.plug_comp _ _ _).symm, ?_, hT',
        hle.2.1 ▸ ha⟩ ⟨ρa, ρk', hcσ', by rw [← hle.2.2.1]; exact hA, contShare_le hle ha
          ⟨?_, fun ls'' he => ⟨?_, fun hq => ?_⟩⟩⟩⟩
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
      obtain ⟨en', hT', hle⟩ := hTT _ _ _ hT
      refine Or.inr ⟨K.comp K₁, n, i, v, en', pure_sep_mk ⟨(Kont.plug_comp _ _ _).symm, ?_, hT',
        hle.2.1 ▸ ha⟩ ⟨ρa, ρn', hcσ', by rw [← hle.2.2.1]; exact hA,
          noOwn_compS hn' hn (hW n i en hT ha ls' σ₂ hF')⟩⟩
      rw [catches_comp, hC, hK₁]; rfl
  · -- a stop of the table beside: the frame joins it
    exact wpG_here _ _ _ σ (Or.inr (Or.inr (hPx ls' t _ _ σ₁ σ₂ σ hp hF' hcσ)))

/-- **A plain frame around an effectful computation** (`ewp_frame_plain_or` with nothing
beside the table).  `[spec §19, §27]` -/
theorem ewp_frame_plain (T : OpTab) (K : Kont) (hH : ∀ n, K.HasHnd n = false)
    (hC : ∀ n, K.Catches n = false) (Fr : List SRec → WProp)
    (hFs : ∀ ls ls', (∀ x, x ∈ ls' ↔ x ∈ ls) → Entails (Fr ls) (Fr ls'))
    (hFe : ∀ ls ls' ρ, Ext ls ls' ρ → Fr ls ρ → Fr ls' ρ)
    (hW : ∀ n i en, T n i = some en → en.abort = true → ∀ ls ρ, Fr ls ρ → NoOwn ρ)
    (hU : ∀ n i en, T n i = some en → en.q = .unr → ∀ ls ρ, Fr ls ρ → ρ = PMap.empty)
    (hK : ∀ n i en, T n i = some en → en.abort = false → en.q ≠ .lin →
      ∀ ls K₁ ρ σ ρ', cancelOK en ls K₁ ρ → Fr ls σ → ResU.CompS ρ σ ρ' →
        cancelOK en ls (K.comp K₁) ρ')
    (Q₁ Q : List SRec → Val → WProp)
    (hk : ∀ ls v, Entails (Q₁ ls v ⋆ Fr ls) (ewpTS ls (K.plug (.val v)) (opTable T) Q)) :
    ∀ {ls : List SRec} {e : Expr} {ρ : WRes}, ewpTS ls e (opTable T) Q₁ ρ →
      ∀ {ρ₂ ρ' : WRes}, Fr ls ρ₂ → ResU.CompS ρ ρ₂ ρ' →
        ewpTS ls (K.plug e) (opTable T) Q ρ' := by
  intro ls e ρ h ρ₂ ρ' hF hc
  exact (ewp_orBot (opTable_mono T)).mp (ewp_frame_plain_or T T (OpTab.Le.refl T) Table.bot
    Table.bot Table.bot_const.mono K
    hH hC Fr hFs hFe hW hU hK (fun _ _ _ _ _ _ _ h => h.elim) Q₁ Q
    (fun ls v σ hσ => (ewp_orBot (opTable_mono T)).mpr (hk ls v σ hσ))
    ((ewp_orBot (opTable_mono T)).mpr h) hF hc)

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

/-- At an abortive-only table a cancel run performs nothing: it owes nothing. -/
theorem cancelTab_abortive {T : OpTab} (hA : T.AbortOnly) : (cancelTab T).Abortive := by
  intro ls t Φ Φ' ρ h
  rcases h with h | ⟨K, n, i, v, en, h⟩
  · exact Or.inl h
  · obtain ⟨⟨-, -, hT, ha⟩, -⟩ := pure_sep_iff.mp h
    rw [hA n i en hT] at ha; exact absurd ha (by simp)

theorem errOk_local {T : OpTab} (hL : T.Local) {ls ls' : List SRec} {ρ : WRes}
    (he : Ext ls ls' ρ) : ∀ {err : Option Val}, errOk T ls err ρ → errOk T ls' err ρ
  | none, h => h
  | some _, ⟨m, j, w, en, h⟩ => by
      obtain ⟨⟨h₁, h₃, h₄⟩, hA, hn⟩ := pure_sep_iff.mp h
      exact ⟨m, j, w, en, pure_sep_mk ⟨h₁, h₃, h₄⟩
        ⟨(hL m j en h₃ ls ls' w ρ he).1 hA, hn⟩⟩

/-- The empty table is abortive-only. -/
theorem OpTab.empty_abortOnly : OpTab.empty.AbortOnly := fun _ _ _ h => by
  simp [OpTab.empty] at h

/-- The finaliser frame `ubind (N, D) [·]`. -/
abbrev ubindK (Nv Dv : Val) : Kont :=
  .appR (.app (.val (.prim .ubind)) (.val (Val.pair Nv Dv))) .hole

/-- A finaliser frame stays in a cancelled region. -/
theorem dead_ubindK (Nv Dv : Val) : (ubindK Nv Dv).dead = ubindK Nv Dv := by
  simp [Kont.dead, Kont.DeadFrame, Val.pair, Expr.val]

/-- The cancel frame `cfin s [·]` of a running finaliser. -/
abbrev cfinK (st : Val) : Kont := .appR (.app (.val (.prim .cfin)) (.val st)) .hole

/-- A running finaliser's `cfin` stays in a cancelled region. -/
theorem dead_cfinK (st : Val) : (cfinK st).dead = cfinK st := by
  simp [Kont.dead, Kont.DeadFrame, Expr.val]

/-- The delimiter `ccatch [·]` of a cancel. -/
abbrev ccatchK : Kont := .appR (.val (.prim .ccatch)) .hole

/-- A cancel's delimiter is dead in a cancelled region. -/
theorem dead_ccatchK : ccatchK.dead = .hole := by
  simp [Kont.dead, Kont.DeadFrame, Expr.val]

/-- A cancel stop at the end absorbs garbage. -/
theorem cancelEnd_absorb {T : OpTab} {ls : List SRec} {t : Expr} {Φ : List SRec → Expr → WProp}
    {ρ₁ ρ₂ ρ : WRes}
    (h : (ex fun (K : Kont) => ex fun (err : Option Val) =>
      ⌜t = K.plug (raiseE (.val (cancelVal err))) ∧ K.Catches 0 = false⌝ ⋆
        (errOk T ls err ⋆ fun ρ => NoOwn ρ)) ρ₁) (hn : NoOwn ρ₂)
    (hc : ResU.CompS ρ₁ ρ₂ ρ) : cancelTab T ls t Φ ρ := by
  obtain ⟨K, err, h⟩ := h
  obtain ⟨hp, τa, τb, hcab, he, hnb⟩ := pure_sep_iff.mp h
  obtain ⟨z, hz, hcz⟩ := compS_reassoc hcab hc
  exact Or.inl ⟨K, err, pure_sep_mk hp ⟨τa, z, hcz, he, noOwn_compS hz hnb hn⟩⟩

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
theorem ewp_kappa_resume {Tb : Table} (hTb : Tb.Mono) (H : Val) (K : Kont) (w : Val)
    {ls : List SRec} {Q : List SRec → Val → WProp} {ρ : WRes}
    (h : ewpTS ls (hndE H (K.plug (.val w))) Tb Q ρ) :
    ewpTS ls (.app (.app (kappa H K) (.val (Val.inj₁ .unit))) (.val w)) Tb Q ρ := by
  refine ewp_step hTb (fun μ => (Step1N.head (Head.beta μ _ _) rfl).plug (Kont.appL .hole w)) ls Q ρ ?_
  refine ewp_step hTb (fun μ => (Step1N.head (Head.case₁ μ Val.unit _ _) rfl).plug
    (Kont.appL .hole w)) ls Q ρ ?_
  refine ewp_step hTb (fun μ => (Step1N.head (Head.seq μ _) rfl).plug (Kont.appL .hole w)) ls Q ρ ?_
  refine ewp_step hTb (fun μ => Step1N.head (Head.beta μ _ w) rfl) ls Q ρ ?_
  rw [show (0 + 1 : Nat) = 1 from rfl, show (0 + 1 + 1 : Nat) = 2 from rfl, kappa_resume_subst]
  exact h

theorem subst_cancelVal_none (j : Nat) (s : Val) :
    Expr.subst j s (cancelVal none).1 = (cancelVal none).1 := by
  simp only [cancelVal, opPayload, BoCa.BoLo.errVal, Val.pair, Val.i32, Val.inj₁, Val.unit,
    Expr.subst]

/-- `κ`'s cancel branch, substituted at its two binders, is `ccatch (K†[raise …])`. -/
theorem kappa_cancel_subst (K : Kont) (s u : Val) :
    Expr.subst 0 u (Expr.subst 1 s
      (ccatchE ((K.dead.shift 2 0).plug (raiseE (.val (cancelVal none)))))) =
      ccatchE (K.dead.plug (raiseE (.val (cancelVal none)))) := by
  simp only [ccatchE, Expr.subst, Expr.val]
  rw [plug_shift_subst 1 K.dead 0 1 s _ (by omega) (by omega),
    plug_shift_subst 0 K.dead 0 0 u _ (by omega) (by omega), Kont.shift_zero]
  simp only [raiseE, Expr.subst, Expr.val, subst_cancelVal_none, Val.prim]

/-- Cancelling `κ` runs `ccatch (K†[raise (0, (0, none))])`. -/
theorem ewp_kappa_cancel {Tb : Table} (hTb : Tb.Mono) (H : Val) (K : Kont)
    {ls : List SRec} {Q : List SRec → Val → WProp} {ρ : WRes}
    (h : ewpTS ls (ccatchE (K.dead.plug (raiseE (.val (cancelVal none))))) Tb Q ρ) :
    ewpTS ls (.app (kappa H K) (.val (Val.inj₂ .unit))) Tb Q ρ := by
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
theorem kappaCBody_subst (hasCancel : Bool) (ℓ : Loc) (H : Val) (K : Kont) :
    Expr.subst 0 (Val.loc ℓ) (kappaCBody hasCancel H K) = kappaC hasCancel ℓ H K := by
  cases hasCancel <;>
  simp only [kappaCBody, kappaC, freeE, stuckE, hndE, ccatchE, raiseE, Expr.subst, Expr.val,
    Val.val_shift, Bool.false_eq_true, if_true, if_false, Val.loc, Val.lam, Val.prim, Val.unit] <;>
  rw [Expr.subst_shift 3 0 3 _ H.1 (by omega) (by omega),
    plug_shift_subst 3 K 0 3 _ _ (by omega) (by omega)] <;>
  simp [Expr.subst, Val.shift, Expr.shift,
    plug_shift_subst 2 K.dead 0 2 _ _ (by omega) (by omega), subst_cancelVal_none]

/-- **The capture cell's allocation**: `κ` before its cell, at an evaluation position, allocates
the cell by the ordinary `alloc` step and becomes `kappaC` at its location. -/
theorem ewp_kappaCell {Tb : Table} (hTb : Tb.Mono) (hasCancel : Bool) (H : Val) (K : Kont)
    (Kc : Kont) {ls : List SRec} {Q : List SRec → Val → WProp} {ρ : WRes}
    (h : ∀ ℓ : Loc, (ptoOwn ℓ Val.unit ─⋆ ewpTS ls (Kc.plug (kappaC hasCancel ℓ H K)) Tb Q) ρ) :
    ewpTS ls (Kc.plug (kappaCell hasCancel H K)) Tb Q ρ := by
  have e : Kc.plug (kappaCell hasCancel H K) =
      (Kc.comp (.appR (.val (.lam (kappaCBody hasCancel H K))) .hole)).plug
        (.app (.val (.prim .alloc)) (.val Val.unit)) := by
    rw [Kont.plug_comp]; rfl
  rw [e]
  refine ewp_alloc hTb _ Val.unit (fun ℓ σ₁ σ₂ hp hc => ?_)
  rw [Kont.plug_comp]
  refine ewp_step hTb (fun μ => (Step1N.head (Head.beta μ _ (Val.loc ℓ)) rfl).plug Kc) ls Q σ₂ ?_
  rw [kappaCBody_subst]
  exact h ℓ σ₁ σ₂ hp hc

/-- `kappaC` is a value. -/
theorem isVal_kappaC (hasCancel : Bool) (ℓ : Loc) (H : Val) (K : Kont) :
    IsVal (kappaC hasCancel ℓ H K) := by unfold kappaC; exact .lam

/-- **Resuming a `κ` that owns a cell** at `w` frees the cell, then runs `hnd H K[w]`. -/
theorem ewp_kappaC_resume {Tb : Table} (hTb : Tb.Mono) (hasCancel : Bool) (ℓ : Loc)
    (H : Val) (K : Kont) (w : Val) {ls : List SRec} {Q : List SRec → Val → WProp} {ρ : WRes}
    (h : (ptoOwn ℓ Val.unit ⋆ ewpTS ls (hndE H (K.plug (.val w))) Tb Q) ρ) :
    ewpTS ls (.app (.app (kappaC hasCancel ℓ H K) (.val (Val.inj₁ .unit))) (.val w)) Tb Q ρ := by
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

/-- **Cancelling a cancellable `κ`** frees its cell, then runs
`ccatch (K†[raise (0, (0, none))])`. -/
theorem ewp_kappaC_cancel {Tb : Table} (hTb : Tb.Mono) (ℓ : Loc) (H : Val) (K : Kont)
    {ls : List SRec} {Q : List SRec → Val → WProp} {ρ : WRes}
    (h : (ptoOwn ℓ Val.unit ⋆ ewpTS ls (ccatchE (K.dead.plug (raiseE (.val (cancelVal none)))))
      Tb Q) ρ) :
    ewpTS ls (.app (kappaC true ℓ H K) (.val (Val.inj₂ .unit))) Tb Q ρ := by
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

/-- A handler frame is dead in a cancelled region. -/
theorem dead_hndK (n : UInt32) (qs hr hs : Val) : (hndK (hndVal n qs hr hs)).dead = .hole := by
  simp [Kont.dead, Kont.DeadFrame, hndVal, Val.pair, Val.i32, Expr.val]

/-- The relation of `κ`'s type at an operation's entry: resumed at every answer into `ewpTS` at
the table `Tb`, and, with weakening, cancelled at `opTable Tk` when its cancel branch has the
table `Tk` (`Tc = some Tk`), nothing when that branch is `⊤` (`Tc = none`).
`[spec §14, §19, §27]` -/
def KapRelT (Tb : Table) (Qout : List SRec → Val → WProp) (en : OpEnt) (Tc : Option OpTab)
    (ls : List SRec) (κ : Val) : WProp := fun ρ =>
  (en.q = .unr → ρ = PMap.empty) ∧
  ∀ ls', Ext ls ls' ρ →
    (∀ w : Val, (en.PB ls' w ─⋆
      ewpTS ls' (.app (.app κ.1 (.val (Val.inj₁ .unit))) (.val w)) Tb Qout) ρ) ∧
    (en.q ≠ .lin → ∀ Tk, Tc = some Tk →
      ewpTS ls' (.app κ.1 (.val (Val.inj₂ .unit))) (opTable Tk) (fun _ v => ⌜v = Val.unit⌝) ρ)

/-- `KapRelT` at the protocol table of a row's operation table.  `[spec §19, §27]` -/
abbrev KapRel (Tout : OpTab) (Qout : List SRec → Val → WProp) (en : OpEnt) (Tc : Option OpTab)
    (ls : List SRec) (κ : Val) : WProp := KapRelT (opTable Tout) Qout en Tc ls κ

/-- `κ`'s relation grows with what its resumption lands in. -/
theorem KapRelT.mono {Tb Tb' : Table} {Qout : List SRec → Val → WProp} {en : OpEnt}
    {Tc : Option OpTab} {ls : List SRec} {κ : Val} {ρ : WRes}
    (hT : ∀ ls e ρ, ewpTS ls e Tb Qout ρ → ewpTS ls e Tb' Qout ρ) (h : KapRelT Tb Qout en Tc ls κ ρ) :
    KapRelT Tb' Qout en Tc ls κ ρ :=
  ⟨h.1, fun ls' he => ⟨fun w τ₁ τ₂ hB hc => hT _ _ _ ((h.2 ls' he).1 w τ₁ τ₂ hB hc), (h.2 ls' he).2⟩⟩

/-- **A cancel run caught at `ccatch`**: `()`, or the kept error raised at the canceller, where its
operation is the canceller's; an operation a finaliser performs passes `ccatch`, its continuation's
cancel at the same region, since `ccatch` is dead in it.  `[spec §19, §27]` -/
theorem ewp_ccatch {T Tout : OpTab} (hT : T.Le Tout) :
    ∀ {ls : List SRec} {e : Expr} {ρ : WRes}, ewpTS ls e (cancelTab T) (fun _ _ _ => False) ρ →
      ewpTS ls (ccatchE e) (opTable Tout) (fun _ v => ⌜v = Val.unit⌝) ρ := by
  intro ls e ρ h
  refine ewp_ind (fun ls e ρ => ewpTS ls (ccatchE e) (opTable Tout) (fun _ v => ⌜v = Val.unit⌝) ρ)
    ?_ h
  intro ls e ρ hs
  refine ewp_fold (opTable_mono Tout) ?_
  refine wpG_bind ccatchK e ls _ ρ ?_
  refine wpG_mono (fun ls' t σ ht => ?_) hs
  rcases ht with ⟨_, _, hv⟩ | ht
  · exact hv.elim
  rcases ht with ⟨K', err, hs'⟩ | ⟨K₁, n, i, v, en, hp⟩
  · obtain ⟨⟨rfl, hK'⟩, τa, τb, hcab, he, hnb⟩ := pure_sep_iff.mp hs'
    cases err with
    | none =>
        refine wpG_head (fun μ => Head.cancel μ K' hK') rfl _ _ σ ?_
        have hτa : τa = PMap.empty := he.1
        subst hτa
        rw [← eq_of_compS_empty_left hcab] at hnb
        refine wpG_garbage (wpG_here _ _ _ σ ⟨PMap.empty, σ, compS_empty_left σ, hnb,
          Or.inl ⟨Val.unit, rfl, rfl, rfl⟩⟩)
    | some E =>
        refine wpG_head (fun μ => Head.creraise μ E K' hK') rfl _ _ σ ?_
        obtain ⟨m, j, w, en, he⟩ := he
        obtain ⟨⟨rfl, hTe, ha⟩, hPA, hnA⟩ := pure_sep_iff.mp he
        obtain ⟨en', hTe', ⟨-, hab, hA, -, -⟩⟩ := hT m j en hTe
        exact wpG_here _ _ _ σ (Or.inr (Or.inr ⟨.hole, m, j, w, en',
          pure_sep_mk ⟨rfl, rfl, hTe', hab ▸ ha⟩
            ⟨τa, τb, hcab, ⟨by rw [← hA]; exact hPA, hnA⟩, hnb⟩⟩))
  · -- an operation of a finaliser passes `ccatch`
    obtain ⟨⟨rfl, hK₁, hT₁, ha⟩, ρa, ρk, hcak, hA, hu, hcont⟩ := pure_sep_iff.mp hp
    obtain ⟨en', hT', hle⟩ := hT _ _ _ hT₁
    refine wpG_here _ _ _ σ (Or.inr (Or.inl ⟨ccatchK.comp K₁, n, i, v, en',
      pure_sep_mk ⟨(Kont.plug_comp _ _ _).symm, ?_, hT', hle.2.1 ▸ ha⟩
        ⟨ρa, ρk, hcak, by rw [← hle.2.2.1]; exact hA, contShare_le hle ha
          ⟨hu, fun ls'' he => ⟨fun w τ₁ τ₂ hB hcτ => ?_, fun hq => ?_⟩⟩⟩⟩))
    · rw [hasHnd_comp, hK₁]; simp [Kont.HasHnd, Expr.val]
    · rw [Kont.plug_comp]; exact (hcont ls'' he).1 w τ₁ τ₂ hB hcτ
    · intro P hP
      show P ls'' ((ccatchK.comp K₁).dead.plug _) ρk
      rw [dead_comp, dead_ccatchK]
      exact (hcont ls'' he).2 hq P hP

/-- A qualifier's tag in a handler value: `0` must resume, `1` cancellable, `2` unrestricted.
`[spec §25]` -/
def Qual.tag : Qual → UInt32
  | .lin => 0
  | .cancel => 1
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

/-- The continuation `[op]` hands at a tag: a cell at a must-resume or cancellable operation. -/
theorem kappaAt_tag (q : Qual) (H : Val) (K : Kont) :
    kappaAt q.tag H K = (match q with
      | .lin => kappaCell false H K
      | .cancel => kappaCell true H K
      | .unr => kappa H K) := by
  cases q <;> simp [kappaAt, Qual.tag]

/-- **A handler** (`[handle]`), by induction on the least fixed point of the inner computation.
`[ret]` answers through `h_ret`; an operation of the handler's name runs its clause, with `κ`
resumed by the induction hypothesis and cancelled by the inner computation's cancel run of the
dead region under `ccatch`; at a must-resume or cancellable operation `κ` first gets its cell
(`ewp_kappaCell`), which its resume and its cancel free; an abortive one runs its clause and drops
the abandoned continuation; an operation of another name passes outward, the handler reinstalled in
its continuation, and dead in that continuation's cancel, so the inner cancel run is the outer one.
The handler's tags `qs` record its operations' qualifiers.  `κ`'s cancel branch at the operation
`i` has the table `Tc i` (`⊤` at `none`), above the table of the entry's cancel obligation (`hTc`).
At `opTable Tin` with a table `Px` beside it whose stops owe nothing to the least fixed point, the
handler joins `Px`'s stops as `hPx` says: a tick at a row holding `Div` (`Core/DivHandle.lean`).
`[spec §14, §19, §25, §27]` -/
theorem ewp_handle_or (Tin Tout : OpTab) (Px Px' : Table) (hPx' : Px'.Mono) (n : UInt32)
    (hn0 : n ≠ 0)
    (hTin : ∀ m i, m ≠ n → Tin m i = Tout m i) (qs hr hs : Val)
    (Qin Qout : List SRec → Val → WProp) (Tc : UInt32 → Option OpTab)
    (hq : ∀ i en, Tin n i = some en → en.abort = false → capTag qs.1 i.toNat = en.q.tag)
    (hTc : ∀ i en, Tin n i = some en → en.abort = false → en.q ≠ .lin → ∀ Tk, Tc i = some Tk →
      ∃ T₁, en.fin = some (cancelObl T₁) ∧ T₁.Le Tk)
    (hPx : ∀ ls t Φ Φ' σ, Px ls t Φ σ → Px' ls ((hndK (hndVal n qs hr hs)).plug t) Φ' σ)
    (hret : ∀ ls v ρ, Qin ls v ρ →
      ewpTS ls (.app (.val hr) (.val v)) (orTab (opTable Tout) Px') Qout ρ)
    (hop : ∀ i en, Tin n i = some en → ∃ c, clauseAt hs.1 i.toNat = some c ∧
      (en.abort = false → ∀ ls v (κ : Val) ρ,
        (en.PA ls v ⋆ KapRelT (orTab (opTable Tout) Px') Qout en (Tc i) ls κ) ρ →
        ewpTS ls (.app (.val c) (.pair (.val v) κ.1)) (orTab (opTable Tout) Px') Qout ρ) ∧
      (en.abort = true → ∀ ls v ρ, en.PA ls v ρ →
        ewpTS ls (.app (.val c) (.val v)) (orTab (opTable Tout) Px') Qout ρ)) :
    ∀ {ls : List SRec} {e : Expr} {ρ : WRes}, ewpTS ls e (orTab (opTable Tin) Px) Qin ρ →
      ewpTS ls (hndE (hndVal n qs hr hs) e) (orTab (opTable Tout) Px') Qout ρ := by
  have hM := orTab_mono (opTable_mono Tout) hPx'
  intro ls e ρ h
  refine ewp_ind (fun ls e ρ => ewpTS ls (hndE (hndVal n qs hr hs) e)
    (orTab (opTable Tout) Px') Qout ρ) ?_ h
  intro ls e ρ hstep
  refine ewp_fold hM (wpG_bind (hndK (hndVal n qs hr hs)) e ls _ ρ ?_)
  refine wpG_mono (fun ls' t σ ht => ?_) hstep
  rcases ht with ⟨v, rfl, hv⟩ | ht | ht
  · -- `[ret]`
    exact wpG_head (fun μ => Head.hret μ n qs hr hs v) rfl _ _ σ
      (ewp_unfold hM (hret _ _ _ hv))
  swap
  · -- a stop of the table beside passes the handler
    exact wpG_here _ _ _ σ (Or.inr (Or.inr (hPx _ _ _ _ σ ht)))
  rcases ht with ⟨K₁, m, i, v, en, hp⟩ | ⟨K₁, m, i, v, en, hp⟩
  · obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρk, hcak, hA, hu, hcont⟩ := pure_sep_iff.mp hp
    by_cases hm : m = n
    · -- `[op]` at the handler's name: the clause, with `κ`
      subst hm
      obtain ⟨c, hc, hna, -⟩ := hop i en hT
      refine wpG_head (fun μ => Head.hop μ m i qs hr hs c v K₁ hc hK₁) rfl _ _ σ ?_
      have hcan : ∀ ls'', Ext ls' ls'' ρk → en.q ≠ .lin → ∀ Tk, Tc i = some Tk →
          ewpTS ls'' (ccatchE (K₁.dead.plug (raiseE (.val (cancelVal none))))) (opTable Tk)
            (fun _ v => ⌜v = Val.unit⌝) ρk := by
        intro ls'' he hq' Tk hTk
        obtain ⟨T₁, hf, hle⟩ := hTc i en hT ha hq' Tk hTk
        exact ewp_ccatch hle ((hcont ls'' he).2 hq' _ hf)
      rw [hq i en hT ha, kappaAt_tag]
      cases hqq : en.q with
      | unr =>
          refine ewp_unfold hM (hna ha ls' v
            ⟨kappa (hndVal m qs hr hs) K₁, by unfold kappa; exact .lam⟩ σ ⟨ρa, ρk, hcak, hA, ?_⟩)
          refine ⟨hu, fun ls'' he => ⟨fun w τ₁ τ₂ hB hc => ?_, fun hq' => ?_⟩⟩
          · exact ewp_kappa_resume hM _ K₁ w
              ((hcont ls'' he).1 w τ₁ τ₂ hB hc)
          · exact fun Tk hTk => ewp_kappa_cancel (opTable_mono Tk) _ K₁ (hcan ls'' he hq' Tk hTk)
      | cancel | lin =>
          refine ewp_unfold hM (ewp_kappaCell hM _
            (hndVal m qs hr hs) K₁ (.appR (.val c) (.pairR v .hole)) (fun ℓ σ₁ σ₂ hcell hc₂ => ?_))
          obtain ⟨y, hy₁, hy₂⟩ := compS_reassoc hcak hc₂
          refine hna ha ls' v ⟨_, isVal_kappaC _ ℓ (hndVal m qs hr hs) K₁⟩ σ₂
            ⟨ρa, y, hy₂, hA, ?_⟩
          refine ⟨fun h' => (by rw [hqq] at h'; cases h'),
            fun ls'' he => ⟨fun w τ₁ τ₂ hB hcτ => ?_, fun hq' => ?_⟩⟩
          · obtain ⟨z, hz, hzτ⟩ := compS_exch hy₁ hcτ
            exact ewp_kappaC_resume hM _ ℓ _ K₁ w
              ⟨σ₁, z, ResU.CompS.comm hzτ, hcell, (hcont ls'' (Ext.left hy₁ he)).1 w τ₁ z hB hz⟩
          · first
              | exact absurd hqq hq'
              | exact fun Tk hTk => ewp_kappaC_cancel (opTable_mono Tk) ℓ _ K₁
                  ⟨σ₁, ρk, ResU.CompS.comm hy₁, hcell, hcan ls'' (Ext.left hy₁ he) hq' Tk hTk⟩
    · -- an operation of another name passes outward
      refine wpG_here _ _ _ σ (Or.inr (Or.inl (Or.inl ⟨(hndK (hndVal n qs hr hs)).comp K₁, m, i, v, en,
        pure_sep_mk ⟨(Kont.plug_comp _ _ _).symm, ?_, (hTin m i hm) ▸ hT, ha⟩
          ⟨ρa, ρk, hcak, hA, hu, fun ls'' he => ⟨fun w τ₁ τ₂ hB hc => ?_, fun hq => ?_⟩⟩⟩)))
      · rw [hasHnd_comp, hndK_hasHnd, hK₁]; simpa using Ne.symm hm
      · rw [Kont.plug_comp]; exact (hcont ls'' he).1 w τ₁ τ₂ hB hc
      · intro P hP
        show P ls'' (((hndK (hndVal n qs hr hs)).comp K₁).dead.plug _) ρk
        rw [dead_comp, dead_hndK]
        exact (hcont ls'' he).2 hq P hP
  · obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρn, hcan, ⟨hPA, hnA⟩, hnn⟩ := pure_sep_iff.mp hp
    by_cases hm : m = n
    · -- `[unwind]` at the handler's name: the clause; the continuation is dropped
      subst hm
      obtain ⟨c, hc, -, hab⟩ := hop i en hT
      refine wpG_head (fun μ => Head.hunwind μ m i qs hr hs c v K₁ hc hK₁) rfl _ _ σ ?_
      refine wpG_garbage (wpG_mono (fun _ _ _ ⟨τ₁, τ₂, hcτ, hq, hnτ⟩ => ⟨τ₁, τ₂, hcτ, hnτ, hq⟩)
        (wpG_frame (e := .app (.val c) (.val v)) (fun _ => fun τ => NoOwn τ)
          (fun _ _ _ h => h) σ ⟨ρa, ρn, hcan,
            ewp_unfold hM (hab ha ls' v ρa hPA), hnn⟩))
    · -- an abortive operation of another name passes outward
      refine wpG_here _ _ _ σ (Or.inr (Or.inl (Or.inr ⟨(hndK (hndVal n qs hr hs)).comp K₁, m, i, v,
        en, pure_sep_mk ⟨(Kont.plug_comp _ _ _).symm, ?_, (hTin m i hm) ▸ hT, ha⟩
          ⟨ρa, ρn, hcan, ⟨hPA, hnA⟩, hnn⟩⟩)))
      rw [catches_comp, hndK_catches, hK₁]; simpa using Ne.symm hm

/-- **A handler** (`[handle]`): `ewp_handle_or` with nothing beside the tables.
`[spec §19, §25, §27]` -/
theorem ewp_handle (Tin Tout : OpTab) (n : UInt32) (hn0 : n ≠ 0)
    (hTin : ∀ m i, m ≠ n → Tin m i = Tout m i) (qs hr hs : Val)
    (Qin Qout : List SRec → Val → WProp) (Tc : UInt32 → Option OpTab)
    (hq : ∀ i en, Tin n i = some en → en.abort = false → capTag qs.1 i.toNat = en.q.tag)
    (hTc : ∀ i en, Tin n i = some en → en.abort = false → en.q ≠ .lin → ∀ Tk, Tc i = some Tk →
      ∃ T₁, en.fin = some (cancelObl T₁) ∧ T₁.Le Tk)
    (hret : ∀ ls v ρ, Qin ls v ρ → ewpTS ls (.app (.val hr) (.val v)) (opTable Tout) Qout ρ)
    (hop : ∀ i en, Tin n i = some en → ∃ c, clauseAt hs.1 i.toNat = some c ∧
      (en.abort = false → ∀ ls v (κ : Val) ρ, (en.PA ls v ⋆ KapRel Tout Qout en (Tc i) ls κ) ρ →
        ewpTS ls (.app (.val c) (.pair (.val v) κ.1)) (opTable Tout) Qout ρ) ∧
      (en.abort = true → ∀ ls v ρ, en.PA ls v ρ →
        ewpTS ls (.app (.val c) (.val v)) (opTable Tout) Qout ρ)) :
    ∀ {ls : List SRec} {e : Expr} {ρ : WRes}, ewpTS ls e (opTable Tin) Qin ρ →
      ewpTS ls (hndE (hndVal n qs hr hs) e) (opTable Tout) Qout ρ := by
  intro ls e ρ h
  have hb := fun {ls e Q ρ} => @ewp_orBot _ _ (opTable Tout) (opTable_mono Tout) ls e Q ρ
  refine hb.mp (ewp_handle_or Tin Tout Table.bot Table.bot Table.bot_const.mono n hn0 hTin qs hr
    hs Qin Qout Tc hq hTc (fun _ _ _ _ _ h => h.elim) (fun ls v ρ hv => hb.mpr (hret ls v ρ hv))
    (fun i en hT => ?_) ((ewp_orBot (opTable_mono Tin)).mpr h))
  obtain ⟨c, hc, h₁, h₂⟩ := hop i en hT
  refine ⟨c, hc, fun ha ls v κ ρ ⟨ρ₁, ρ₂, hc₁, hA, hK⟩ => hb.mpr (h₁ ha ls v κ ρ
    ⟨ρ₁, ρ₂, hc₁, hA, KapRelT.mono (fun _ _ _ h => hb.mp h) hK⟩), fun ha ls v ρ hv => hb.mpr
      (h₂ ha ls v ρ hv)⟩

/-! ### The typing rules' types  `[spec §19]` -/

theorem ext_empty' (ls ls' : List SRec) : Ext ls ls' PMap.empty :=
  ⟨fun _ _ hr => by obtain ⟨m, ψ, e, -⟩ := hr; simp at e,
   fun _ hb => by obtain ⟨m, ψ, e, -⟩ := hb; simp at e⟩

/-- The payload expression `(n, (i, V))`. -/
def opArgE (n i : UInt32) (V : Expr) : Expr := .pair (.val (Val.i32 n)) (.pair (.val (Val.i32 i)) V)

/-- `await_n ≜ perform_n (0, ()) to r. case r {inl u. return u | inr u. raise_n (1, u)}`: the
only form in which a cancellable wait is performed (`[await-c]`).  `[spec §29a]` -/
def awaitE (n : UInt32) : Expr :=
  .app (.val (.lam (.case (.var 0) (.var 0) (raiseE (opArgE n 1 (.var 0))))))
    (performE (opArgE n 0 (.val .unit)))

/-- A row's names are not the reserved `0`. -/
def Row.NZ (S : Row) : Prop := ∀ o ∈ S, o.n ≠ 0

/-- A row has a cancellable or unrestricted operation (every abortive one is one of these). -/
def Row.Cancels (S : Row) : Prop := ∃ o ∈ S, o.q ≠ .lin

/-- A row has an unrestricted operation. -/
def Row.Unr (S : Row) : Prop := ∃ o ∈ S, o.q = .unr

/-- A cancel row may perform an unrestricted operation, at some depth: a layer at `unr`, or one in
the cancel row of a capturable layer.  `[spec §27]` -/
def CTy.FinUnr : CTy → Prop
  | .eff _ _ q _ B f _ C => q = .unr ∨ (capB q B = true ∧ f.FinUnr) ∨ C.FinUnr
  | _ => False

/-- A row has an unrestricted operation at its top, or in the cancel row of a capturable operation
at some depth, where a cancel may stop at it: what a finaliser frame, which runs in the cancels
below it, meets (`[then]`).  `[spec §27]` -/
def Row.UnrD (S : Row) : Prop := ∃ o ∈ S, o.q = .unr ∨ (capB o.q o.B = true ∧ o.fin.FinUnr)

@[simp] theorem CTy.finUnr_ret (A : VTy) : (CTy.ret A).FinUnr ↔ False := Iff.rfl

theorem Row.unrD_of_unr {S : Row} (h : S.Unr) : S.UnrD :=
  let ⟨o, ho, hq⟩ := h; ⟨o, ho, Or.inl hq⟩

/-- At empty cancel rows a row has an unrestricted operation at some depth exactly when it has one
at its top. -/
theorem Row.unrD_iff_of_fin {S : Row} (h : ∀ o ∈ S, o.fin = .ret .unit) : S.UnrD ↔ S.Unr := by
  constructor
  · rintro ⟨o, ho, hq | ⟨-, hf⟩⟩
    · exact ⟨o, ho, hq⟩
    · rw [h o ho] at hf; exact hf.elim
  · exact Row.unrD_of_unr

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

theorem Row.abortOnly_abort (S : Row) (δ : LSub) : (Row.tab S.abortOnly δ).AbortOnly := by
  intro n i en hT
  obtain ⟨o, hf, rfl⟩ := Row.tab_some hT
  obtain ⟨hm, -, -⟩ := Row.find_mem hf
  exact (List.mem_filter.mp hm).2

/-! ### Own-free contexts -/

/-- A type whose values hold no `own` cell: data, borrows, `!`, the opaque host types. An abort
abandons a value of such a type (SPEC §19); that is not a drop. `Tok` owns its cell, so it is not
here, and neither is any type that holds it (SPEC §11, §42).  `[spec §19]` -/
inductive _root_.BoCa.Fig16.LogRel.Core.VTy.OwnFree : VTy → Prop where
  | unit : VTy.OwnFree .unit
  | zero : VTy.OwnFree .zero
  | int (w : Width) : VTy.OwnFree (.int w)
  | unk : VTy.OwnFree .unk
  | opq (k : Opaque) (hk : k.Host) : VTy.OwnFree (.opq k)
  | bang (A : VTy) : VTy.OwnFree (.bang A)
  | imm (a : Lifetime.Life) (A : VTy) : VTy.OwnFree (.imm a A)
  | «mut» (a : Lifetime.Life) (A : VTy) : VTy.OwnFree (.mut a A)
  | tensor {A B : VTy} : VTy.OwnFree A → VTy.OwnFree B → VTy.OwnFree (.tensor A B)
  | sum {A B : VTy} : VTy.OwnFree A → VTy.OwnFree B → VTy.OwnFree (.sum A B)

theorem vC_noOwn_of_ownFree {A : VTy} (hA : A.OwnFree) :
    ∀ {ls : List SRec} {δ : LSub} {v : Val} {ρ : WRes}, vC true A ls δ v ρ → NoOwn ρ := by
  induction hA with
  | unit => intro ls δ v ρ h; rw [h.1]; exact noOwn_empty
  | zero => intro ls δ v ρ h; exact h.elim
  | int w => intro ls δ v ρ h; rw [h.1]; exact noOwn_empty
  | unk => intro ls δ v ρ h; rw [h.1]; exact noOwn_empty
  | opq k hk => intro ls δ v ρ h; rw [vCE, Opaque.rel_host hk] at h; rw [h.1]; exact noOwn_empty
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

/-- Every live slot of `Γ` is at an own-free type. -/
def _root_.BoCa.Ctx.OwnFree (Γ : Ctx VTy) : Prop := ∀ s ∈ Γ, s.live = true → s.ty.OwnFree

theorem gSepC_noOwn {ls : List SRec} {δ : LSub} : ∀ {Γ : Ctx VTy} {γ : List Val} {ρ : WRes},
    Γ.OwnFree → gSepC ls δ Γ γ ρ → NoOwn ρ
  | [], _, _, _, h => by rw [h.1]; exact noOwn_empty
  | _ :: _, [], _, _, h => by rw [h.1]; exact noOwn_empty
  | s :: Γ, v :: γ, ρ, hd, h => by
      unfold gSepC at h
      split at h
      · rename_i hl
        obtain ⟨ρ₁, ρ₂, hc, h₁, h₂⟩ := h
        exact noOwn_compS hc (vC_noOwn_of_ownFree (hd s (by simp) hl) h₁)
          (gSepC_noOwn (fun s' hs' => hd s' (List.mem_cons_of_mem _ hs')) h₂)
      · exact gSepC_noOwn (fun s' hs' => hd s' (List.mem_cons_of_mem _ hs')) h

theorem gDenC_noOwn {ls : List SRec} {δ : LSub} {Γ : Ctx VTy} {γ : List Val} {ρ : WRes}
    (hd : Γ.OwnFree) (h : gDenC ls δ Γ γ ρ) : NoOwn ρ :=
  gSepC_noOwn hd (gDenC_iff.mp h).2

theorem gDenC_persistent {ls : List SRec} {δ : LSub} {Γ : Ctx VTy} {γ : List Val} {ρ : WRes}
    (hp : Ctx.Banged Γ) (h : gDenC ls δ Γ γ ρ) : ρ = PMap.empty :=
  gSepC_persistent hp (gDenC_iff.mp h).2

/-! ### Compatibility of `[let]` and `[then]` -/

theorem substAll_cons_psub (v : Val) (γ : List Val) (e : Expr) :
    substAll (v :: γ) e = Expr.subst 0 v (Expr.psub 1 γ e) := by
  show Expr.psub 0 (v :: γ) e = _
  rw [Expr.psub_cons 0 v γ e, Val.shift_zero]

theorem OpSig.cancels_of_ent {o : OpSig} {δ : LSub}
    (h : (o.ent δ).q ≠ .lin ∨ (o.ent δ).abort = true) :
    o.q ≠ .lin := by
  rcases h with h | h
  · exact h
  · simp only [OpSig.ent, OpSig.abort, Bool.and_eq_true, bne_iff_ne, ne_eq] at h; exact h.2

/-- `M then x. N unwind D`: `ubind (λx. N, λ_. D) M`. -/
def thenE (N D M : Expr) : Expr :=
  .app (.app (.val (.prim .ubind)) (.pair (.val (.lam N)) (.val (.lam D)))) M

/-! ### Compatibility of `[handle]` -/

/-- The cancel rows of an effect whose operations' cancel rows are all empty.  `[spec §27]` -/
abbrev finsNil : Nat → CTy := fun _ => .ret .unit

/-- The markers of an effect none of whose operations is cancelled by resuming it.
`[spec §29a]` -/
abbrev rcsNil : Nat → Bool := fun _ => false

/-- An effect's operations, as a row of the name `n`: the `j`-th at index `k + j`, with the
cancel row `fs j` and the marker `cs j` (`OpSig.rc`).  `[spec §19, §27, §29a]` -/
def Row.ofEff (n : UInt32) (E : List (Qual × VTy × VTy)) (k : Nat) (fs : Nat → CTy := finsNil)
    (cs : Nat → Bool := rcsNil) : Row :=
  match E with
  | [] => []
  | (q, A, B) :: E => ⟨n, UInt32.ofNat k, q, A, B, fs 0, cs 0⟩ ::
      Row.ofEff n E (k + 1) (fun j => fs (j + 1)) (fun j => cs (j + 1))

/-- The type of `κ`'s cancel branch at a handler whose outer row is `Σ`, for an operation whose
cancel row is `F`: `F_{F ⊕ Σ} 1`, the cancel row's operations ahead of `Σ`, or `⊤` when `F` is
`⊤`.  At the empty cancel row it is `F_Σ 1`.  `[spec §27]` -/
def cancelTy (S : Row) (F : CTy) : CTy :=
  if F.isTop then .top else CTy.effOf (F.rowOf ++ S) .unit

/-- `κ`'s type at an operation `A ↠^q B` of a handler answering `F_Σ R`, whose cancel row is `F`:
`U((B ⊸ F_Σ R) & ⊤)` (must resume: resumed), `U((B ⊸ F_Σ R) & C)` (cancellable: resumed or
cancelled), and its `!` (unrestricted), with `C = cancelTy Σ F`.  `[spec §19, §27]` -/
def kTy (S : Row) (R : VTy) (q : Qual) (B : VTy) (F : CTy := .ret .unit) : VTy :=
  match q with
  | .lin => .thunk (.amp (.arr B (CTy.effOf S R)) .top)
  | .cancel => .thunk (.amp (.arr B (CTy.effOf S R)) (cancelTy S F))
  | .unr => .bang (.thunk (.amp (.arr B (CTy.effOf S R)) (cancelTy S F)))

/-- A clause's type: `!U(A ⊗ K ⊸ F_Σ R)`, or `!U(A ⊸ F_Σ R)` at an abortive operation, `K` at the
operation's cancel row `F`.  `[spec §19, §27]` -/
def clauseTy (S : Row) (R : VTy) (o : Qual × VTy × VTy) (F : CTy := .ret .unit) : VTy :=
  match o with
  | (q, A, B) => if (B.isZero && q != .lin) then .bang (.thunk (.arr A (CTy.effOf S R)))
      else .bang (.thunk (.arr (.tensor A (kTy S R q B F)) (CTy.effOf S R)))

/-- The clauses' type: a right-nested tuple, the `j`-th clause at index `j`, at the cancel row
`fs j`.  `[spec §19, §27]` -/
def clausesTy (S : Row) (R : VTy) (E : List (Qual × VTy × VTy)) (fs : Nat → CTy := finsNil) :
    VTy :=
  match E with
  | [] => .unit
  | o :: E => .tensor (clauseTy S R o (fs 0)) (clausesTy S R E (fun j => fs (j + 1)))

/-- `h_ret`'s type: `!U(A ⊸ F_Σ R)`. -/
def retTy (S : Row) (A R : VTy) : VTy := .bang (.thunk (.arr A (CTy.effOf S R)))

/-- `handle_n e with (h_ret, hs)`, `h_ret` and `hs` variables, the handler's tags those of the
qualifiers `qs` (`qualsVal`).  `[spec §19, §25]` -/
def hndTerm (n : UInt32) (qs : List Qual) (ir ic : Nat) (e : Expr) : Expr :=
  .app (.app (.val (.prim .hnd)) (.pair (.val (Val.i32 n))
    (.pair (.val (qualsVal qs)) (.pair (.var ir) (.var ic))))) e

theorem Row.find_ofEff (n : UInt32) : ∀ (E : List (Qual × VTy × VTy)) (k : Nat) (fs : Nat → CTy)
    (m i : UInt32) (o : OpSig), Row.find (Row.ofEff n E k fs) m i = some o →
      m = n ∧ ∃ j, ∃ h : j < E.length, i = UInt32.ofNat (k + j) ∧
        o = ⟨n, UInt32.ofNat (k + j), E[j].1, E[j].2.1, E[j].2.2, fs j, false⟩
  | [], _, _, _, _, _, h => by simp [Row.ofEff, Row.find] at h
  | (q, A, B) :: E, k, fs, m, i, o, h => by
      unfold Row.find at h
      simp only [Row.ofEff, List.find?_cons] at h
      split at h
      · rename_i hk
        simp only [decide_eq_true_eq] at hk
        obtain ⟨rfl, rfl⟩ := hk
        cases h
        exact ⟨rfl, 0, by simp, by simp, by simp⟩
      · obtain ⟨hm, j, hj, hi, ho⟩ := Row.find_ofEff n E (k + 1) (fun j => fs (j + 1)) m i o h
        exact ⟨hm, j + 1, by simp; omega, by rw [hi]; congr 1; omega,
          by rw [ho]; simp [show k + 1 + j = k + (j + 1) by omega]⟩

theorem Row.find_ofEff_neC (n : UInt32) : ∀ (E : List (Qual × VTy × VTy)) (k : Nat)
    (fs : Nat → CTy) (cs : Nat → Bool) (m i : UInt32), m ≠ n →
    Row.find (Row.ofEff n E k fs cs) m i = none
  | [], _, _, _, _, _, _ => by simp [Row.ofEff, Row.find]
  | (q, A, B) :: E, k, fs, cs, m, i, hm => by
      unfold Row.find
      simp only [Row.ofEff, List.find?_cons]
      have hd : decide (m = n ∧ i = UInt32.ofNat k) = false := by simp [hm]
      rw [hd]
      exact Row.find_ofEff_neC n E (k + 1) (fun j => fs (j + 1)) (fun j => cs (j + 1)) m i hm

theorem Row.find_ofEff_ne (n : UInt32) {cs : Nat → Bool} (E : List (Qual × VTy × VTy)) (k : Nat)
    (fs : Nat → CTy) (m i : UInt32) (hm : m ≠ n) : Row.find (Row.ofEff n E k fs cs) m i = none :=
  Row.find_ofEff_neC n E k fs cs m i hm

theorem Row.find_append (S S' : Row) (m i : UInt32) :
    Row.find (S ++ S') m i = (Row.find S m i).or (Row.find S' m i) := by
  unfold Row.find; rw [List.find?_append]

theorem clausesTy_at {S : Row} {R : VTy} {ls : List SRec} {δ : LSub} :
    ∀ (E : List (Qual × VTy × VTy)) (fs : Nat → CTy) {hs : Val} {ρ : WRes},
      vC true (clausesTy S R E fs) ls δ hs ρ →
      ∀ j (h : j < E.length), ∃ c, clauseAt hs.1 j = some c ∧
        vC true (clauseTy S R E[j] (fs j)) ls δ c PMap.empty
  | [], _, _, _, _, j, h => by simp at h
  | o :: E, fs, hs, ρ, h, j, hj => by
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
          obtain ⟨c', hc', hv⟩ := clausesTy_at E (fun j => fs (j + 1)) hr j (by simpa using hj)
          exact ⟨c', by simpa [clauseAt, Val.pair] using hc', by simpa using hv⟩

/-- The clauses hold nothing. -/
theorem clausesTy_empty {S : Row} {R : VTy} {ls : List SRec} {δ : LSub} :
    ∀ (E : List (Qual × VTy × VTy)) (fs : Nat → CTy) {hs : Val} {ρ : WRes},
      vC true (clausesTy S R E fs) ls δ hs ρ → ρ = PMap.empty
  | [], _, _, _, h => h.1
  | (q, A, B) :: E, fs, hs, ρ, h => by
      obtain ⟨c, rest, h⟩ := h
      obtain ⟨-, ρ₁, ρ₂, hc, hc₁, hr⟩ := pure_sep_iff.mp h
      have he : ρ₁ = PMap.empty := by
        simp only [clauseTy] at hc₁; split at hc₁ <;> exact hc₁.1
      rw [he, clausesTy_empty E (fun j => fs (j + 1)) hr] at hc
      exact eq_of_compS_empty_left hc

theorem substAll_var_some {γ : List Val} {i : Nat} {v : Val} (hv : γ[i]? = some v) :
    substAll γ (.var i) = .val v := by
  show Expr.psub 0 γ (.var i) = _
  simp only [Expr.psub, if_neg (Nat.not_lt_zero i), Nat.sub_zero, hv, Val.shift_zero]

/-- An operation of the handler's name in `Σ` extended by the handler's effect is the effect's
`j`-th, at index `j`. -/
theorem Row.tab_ofEff_self {S : Row} {E : List (Qual × VTy × VTy)} {fs : Nat → CTy} {n : UInt32}
    {δ : LSub} (hnS : ∀ o ∈ S, o.n ≠ n) (hlen : E.length ≤ 2 ^ 32) {i : UInt32} {en : OpEnt}
    (hT : Row.tab (Row.ofEff n E 0 fs ++ S) δ n i = some en) :
    ∃ j, ∃ hj : j < E.length, i.toNat = j ∧ i = UInt32.ofNat (0 + j) ∧
      en = OpSig.ent δ ⟨n, UInt32.ofNat (0 + j), E[j].1, E[j].2.1, E[j].2.2, fs j, false⟩ := by
  obtain ⟨o, hf, rfl⟩ := Row.tab_some hT
  have hfo : Row.find (Row.ofEff n E 0 fs) n i = some o := by
    rw [Row.find_append] at hf
    cases h₁ : Row.find (Row.ofEff n E 0 fs) n i with
    | some o' => rw [h₁] at hf; exact hf
    | none =>
        rw [h₁] at hf
        obtain ⟨hm, hn, -⟩ := Row.find_mem hf
        exact absurd hn (hnS o hm)
  obtain ⟨-, j, hj, rfl, rfl⟩ := Row.find_ofEff n E 0 fs n i o hfo
  have hjn : (UInt32.ofNat (0 + j)).toNat = j := by
    rw [Nat.zero_add]; exact UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega)
  exact ⟨j, hj, hjn, rfl, rfl⟩

/-- A handler records its effect's qualifiers: the tag at each operation's index is its
qualifier's.  `[spec §25]` -/
theorem capTag_ofEff {S : Row} {E : List (Qual × VTy × VTy)} {fs : Nat → CTy} {n : UInt32}
    {δ : LSub} (hnS : ∀ o ∈ S, o.n ≠ n) (hlen : E.length ≤ 2 ^ 32) (i : UInt32) (en : OpEnt)
    (hT : Row.tab (Row.ofEff n E 0 fs ++ S) δ n i = some en) :
    capTag (qualsVal (E.map Prod.fst)).1 i.toNat = en.q.tag := by
  obtain ⟨j, hj, hji, -, rfl⟩ := Row.tab_ofEff_self hnS hlen hT
  rw [hji, capTag_qualsVal _ j (by simpa using hj)]
  simp [OpSig.ent]

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
    ∀ (E : List (Qual × VTy × VTy)) (fs : Nat → CTy), (clausesTy S R E fs).Persistent
  | [], _ => rfl
  | (q, A, B) :: E, fs => by
      have h := clausesTy_persistent S R E (fun j => fs (j + 1))
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

end BoCa.Fig16.LogRel.Core
