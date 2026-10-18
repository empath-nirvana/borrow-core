import DivEffect.Reify

/-!
# DivEffect — `[handle]` of another name around a computation that ticks  (§4.1, unknown 1, item 1)

`hnd_m H e`, `e` at a row holding `Div` and `m`, `m ≠ d`.  The handler forwards `tick`: a tick of
`e` stops the whole, its continuation `hnd_m H K[n]`.  So the forwarded tick is the coinductive
case.

**What is proved here** (`handle_tail`): the compatibility for a handler whose clause **resumes
`κ` in tail position**: `h_m (v, κ) ↦* κ (N v)`, `N v` a computation of `cwp` that is not given
`κ`.  This is the clause class that lowers to a direct call (`tail_resumes`,
`Core/Handlers.lean`).  `N v` may tick.  By coinduction up to `cwp`, the candidate is

* `hnd_m H e` at every `e` of the inner `cwp` (`W₁`);
* the resume frame `κ [·]` around a computation of the outer `cwp`, the frame owning `κ`'s cell
  and its continuation's share (`W₂`).

`W₁` is one segment by induction on `e`'s segment (with the segment itself, `P ∧ cwpF`, so that
a resumed continuation is both the induction hypothesis and in the candidate).  At an operation
of `m`, the clause's `N v` runs under the resume frame, one segment (`cwpF_frame`); its ticks
owe `W₂`; its answer resumes `κ` into the induction hypothesis.  `W₂` is one segment by
`cwpF_frame`, its answer resuming `κ` into `W₁`.  `Closing` is Core's `ewp_handle` at the closing
tables.

The rest of the row is linear (`hLin`): an abortive or affine operation of `N` would abandon the
resume frame, and `κ` with it, as Core's `[let]` side condition says for a linear `κ` in a
clause's context.

**What is not proved** (`handle_general`, a `sorry`): a clause that hands `κ` to code it does not
control (stores it, passes it on).  Its compatibility at `cwp` needs the clause's relation at the
coinduction's candidate, which the relation does not carry; `README.md` states the obligation.
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

attribute [local simp] Expr.subst Val.val_shift Expr.shift_shift Expr.shift_zero

/-- `λw. κ.1 w`. -/
def resF (κ : Val) : Val := .lam (.app (.app (κ.1.shift 1 0) (.val (Val.inj₁ .unit))) (.var 0))

/-- The resume frame `(λw. κ.1 w) [·]`. -/
def resK (κ : Val) : Kont := .appR (.val (resF κ)) .hole

theorem resK_plain (κ : Val) : (∀ n, (resK κ).HasHnd n = false) ∧ (∀ n, (resK κ).Catches n = false) :=
  ⟨fun n => by simp [resK, Kont.HasHnd, resF], fun n => by simp [resK, Kont.Catches, resF]⟩

theorem resK_dead (κ : Val) : (resK κ).dead = resK κ := by
  simp [resK, Kont.dead, Kont.DeadFrame, resF]

theorem resK_steps (κ w : Val) :
    PureSteps ((resK κ).plug (.val w)) (.app (.app (.val κ) (.val (Val.inj₁ .unit))) (.val w)) := by
  refine (PureSteps.beta _ w).trans ?_
  simp [subst_shift_succ]
  exact .refl

/-- An operation `0` of `m`, linear, under its handler: the clause, with `κ` given its cell. -/
theorem hnd_tick_like {Tb : Table} (hTb : Tb.Mono) (m : UInt32) (hr c : Val) (K₁ : Kont)
    (hK₁ : K₁.HasHnd m = false) (v : Val) {ls : List SRec} {Q : List SRec → Val → WProp}
    {ρ : WRes}
    (h : ∀ ℓ : Loc, (ptoOwn ℓ Val.unit ─⋆ ewpTS ls (.app (.val c)
      (.val (Val.pair v (kapV ℓ (hndVal m (qualsVal [.lin]) hr (c.pair .unit)) K₁)))) Tb Q) ρ) :
    ewpTS ls (hndE (hndVal m (qualsVal [.lin]) hr (c.pair .unit))
      (K₁.plug (performE (.val (opPayload m 0 v))))) Tb Q ρ := by
  refine ewp_step hTb (fun μ => Step1N.head (Head.hop μ m 0 (qualsVal [.lin]) hr
    (Val.pair c .unit) c v K₁ (clauseAt_one c) hK₁) rfl) ls Q ρ ?_
  rw [kappaAt_lin]
  have e : Expr.app (.val c) (.pair (.val v)
      (kappaCell false (hndVal m (qualsVal [Qual.lin]) hr (c.pair Val.unit)) K₁)) =
      (Kont.appR (.val c) (.pairR v .hole)).plug
        (kappaCell false (hndVal m (qualsVal [Qual.lin]) hr (c.pair Val.unit)) K₁) := rfl
  rw [e]
  exact ewp_kappaCell hTb false _ K₁ _ (fun ℓ σ₁ σ₂ hp hc => h ℓ σ₁ σ₂ hp hc)

section
variable {δ : LSub} {d m : UInt32} {Tout : OpTab} {en : OpEnt}
  (hmd : m ≠ d) (hm0 : m ≠ 0) (hTd : ∀ i, Tout d i = none) (hTm : ∀ i, Tout m i = none)
  (hLin : ∀ n i en', Tout n i = some en' → en'.q = .lin ∧ en'.abort = false)
  (heq : en.q = .lin) (hea : en.abort = false)
  (hr c : Val) (Nf : Val → Expr)
  (hc : ∀ v κ : Val, PureSteps (.app (.val c) (.val (Val.pair v κ))) ((resK κ).plug (Nf v)))
  {Qin Qout : List SRec → Val → WProp}
  (hN : ∀ ls v ρ, en.PA ls v ρ → cwp δ d Tout en.PB ls (Nf v) ρ)
  (hret : ∀ ls v ρ, Qin ls v ρ → cwp δ d Tout Qout ls (.app (.val hr) (.val v)) ρ)

/-- The handler value: one linear operation of `m`. -/
abbrev hndM (m : UInt32) (hr c : Val) : Val := hndVal m (qualsVal [.lin]) hr (Val.pair c .unit)

/-- The inner row: the rest of the row and `m`'s operation. -/
abbrev Tin (m : UInt32) (en : OpEnt) (Tout : OpTab) : OpTab := OpTab.ext m 0 en Tout

include hmd hm0 hTd hTm hLin heq hea hc hN hret in
/-- **`Closing` under the handler**: Core's `ewp_handle` at the closing tables; the clause's
`N v` is in `Closing`, and its answer resumes `κ`. -/
theorem handle_closing {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : Closing δ d (Tin m en Tout) Qin ls e ρ) :
    Closing δ d Tout Qout ls (hndE (hndM m hr c) e) ρ := by
  have hlinC : ∀ n i en', OpTab.ext d 0 (closeEnt δ d) Tout n i = some en' →
      en'.q = .lin ∧ en'.abort = false := by
    intro n i en' h
    rcases ext_some h with ⟨-, -, rfl⟩ | h
    · exact ⟨rfl, rfl⟩
    · exact hLin n i en' h
  refine ewp_handle (OpTab.ext d 0 (closeEnt δ d) (Tin m en Tout)) (OpTab.ext d 0 (closeEnt δ d) Tout)
    m hm0 ?_ (qualsVal [.lin]) hr (Val.pair c .unit) Qin Qout (fun _ => none) ?_ ?_
    (fun ls v ρ hv => closing_of_cwp (hTd 0) (hret ls v ρ hv)) ?_ h
  · intro n i hn
    simp only [OpTab.ext]
    by_cases h₁ : n = d ∧ i = 0
    · rw [if_pos h₁, if_pos h₁]
    · rw [if_neg h₁, if_neg h₁, if_neg (fun h => hn h.1)]
  · intro i en' h ha
    have h' : OpTab.ext m 0 en Tout m i = some en' := by
      simpa [OpTab.ext, hmd] using h
    rcases ext_some h' with ⟨-, rfl, rfl⟩ | h'
    · simp [capTag, qualsVal, Qual.tag, Val.pair, Val.i32, heq]
    · rw [hTm] at h'; cases h'
  · intro i en' h _ hq
    have h' : OpTab.ext m 0 en Tout m i = some en' := by
      simpa [OpTab.ext, hmd] using h
    rcases ext_some h' with ⟨-, rfl, rfl⟩ | h'
    · exact absurd heq hq
    · rw [hTm] at h'; cases h'
  · intro i en' h
    have h' : OpTab.ext m 0 en Tout m i = some en' := by
      simpa [OpTab.ext, hmd] using h
    rcases ext_some h' with ⟨-, rfl, rfl⟩ | h'
    swap
    · rw [hTm] at h'; cases h'
    refine ⟨c, clauseAt_one c, fun _ ls v κ ρ hv => ?_, fun ha' => absurd ha' (by simp [hea])⟩
    have hM := opTable_mono (OpTab.ext d 0 (closeEnt δ d) Tout)
    obtain ⟨ρa, ρk, hcak, hA, hK⟩ := hv
    refine ewp_pureSteps hM (hc v κ) _ _ ρ ?_
    refine ewp_frame_plain _ (resK κ) (resK_plain κ).1 (resK_plain κ).2
      (fun ls => KapRel (OpTab.ext d 0 (closeEnt δ d) Tout) Qout en' none ls κ)
      (fun ls ls' hs σ h => ⟨h.1, fun ls'' he => h.2 ls'' ((ext_of_same hs σ).trans he)⟩)
      (fun ls ls' σ he h => ⟨h.1, fun ls'' he' => h.2 ls'' (he.trans he')⟩)
      (fun n i en' h ha => absurd ha (by simp [(hlinC n i en' h).2]))
      (fun n i en' h hq => absurd hq (by simp [(hlinC n i en' h).1]))
      (fun n i en'' h _ hq => absurd (hlinC n i en'' h).1 hq) en'.PB Qout ?_
      (closing_of_cwp (hTd 0) (hN ls v ρa hA)) hK hcak
    rintro ls' w σ ⟨σ₁, σ₂, hcσ, hw, hk⟩
    exact ewp_pureSteps hM (resK_steps κ w) _ _ σ
      ((hk.2 ls' (Ext.refl ls' σ₂)).1 w σ₁ σ (by exact hw) (ResU.CompS.comm hcσ))

/-- `κ`'s resources in the resume frame: its cell, and its continuation's share, resumed at every
answer into `Φ`. -/
def frK (ℓ : Loc) (K₁ : Kont) (PB : List SRec → Val → WProp) (Φ : CPred) : List SRec → WProp :=
  fun ls σ => ∃ σc ρk, ResU.CompS σc ρk σ ∧ ptoOwn ℓ .unit σc ∧
    ∀ ls', Ext ls ls' ρk → ∀ w, (PB ls' w ─⋆ Φ ls' (K₁.plug (.val w))) ρk

theorem frK_same {ℓ : Loc} {K₁ : Kont} {PB : List SRec → Val → WProp} {Φ : CPred} :
    ∀ ls ls', (∀ x, x ∈ ls' ↔ x ∈ ls) → Entails (frK ℓ K₁ PB Φ ls) (frK ℓ K₁ PB Φ ls') :=
  fun _ _ hs _ ⟨σc, ρk, hc, hp, hk⟩ =>
    ⟨σc, ρk, hc, hp, fun ls'' he => hk ls'' ((ext_of_same hs ρk).trans he)⟩

theorem frK_ext {ℓ : Loc} {K₁ : Kont} {PB : List SRec → Val → WProp} {Φ : CPred} :
    ∀ ls ls' ρ, Ext ls ls' ρ → frK ℓ K₁ PB Φ ls ρ → frK ℓ K₁ PB Φ ls' ρ :=
  fun _ _ _ he ⟨σc, ρk, hc, hp, hk⟩ =>
    ⟨σc, ρk, hc, hp, fun ls'' he' => hk ls'' ((he.right hc).trans he')⟩

theorem frK_mono {ℓ : Loc} {K₁ : Kont} {PB : List SRec → Val → WProp} {Φ Φ' : CPred}
    (h : Φ.Le Φ') {ls : List SRec} {σ : WRes} (hf : frK ℓ K₁ PB Φ ls σ) : frK ℓ K₁ PB Φ' ls σ := by
  obtain ⟨σc, ρk, hc, hp, hk⟩ := hf
  exact ⟨σc, ρk, hc, hp, fun ls' he w τ₁ τ₂ hw hc' => h _ _ _ (hk ls' he w τ₁ τ₂ hw hc')⟩

/-- A resumed `κ` frees its cell and runs its continuation under the handler. -/
theorem frK_resume {Tb : Table} (hTb : Tb.Mono) {ℓ : Loc} {H : Val} {K₁ : Kont}
    {PB : List SRec → Val → WProp} {Φ : CPred} {Q : List SRec → Val → WProp}
    (hΦ : ∀ ls e ρ, Φ ls e ρ → ewpTS ls (hndE H e) Tb Q ρ) {ls : List SRec} {w : Val} {σ : WRes}
    (h : (PB ls w ⋆ frK ℓ K₁ PB Φ ls) σ) :
    ewpTS ls ((resK (kapV ℓ H K₁)).plug (.val w)) Tb Q σ := by
  obtain ⟨σw, σf, hc, hw, σc, ρk, hck, hp, hk⟩ := h
  refine ewp_pureSteps hTb (resK_steps _ w) _ _ σ ?_
  obtain ⟨z, hz, hcz⟩ := compS_lcomm hck hc
  exact ewp_kappaC_resume_in hTb .hole false ℓ H K₁ w ⟨σc, z, hcz, hp,
    hΦ _ _ _ (hk ls (Ext.refl ls ρk) w σw z hw (ResU.CompS.comm hz))⟩

include hmd hm0 hTd hTm hLin heq hea hc hN hret in
/-- **`[handle]` of another name, at a clause that resumes in tail position** (§4.1 unknown 1
item 1), by coinduction up to `cwp`. -/
theorem handle_tail {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : cwp δ d (Tin m en Tout) Qin ls e ρ) :
    cwp δ d Tout Qout ls (hndE (hndM m hr c) e) ρ := by
  have hTd' : (Tin m en Tout) d 0 = none := by
    simp [OpTab.ext, Ne.symm hmd, hTd]
  have hPC : Tout.PlainCancel := fun n i en' h _ hq => absurd (hLin n i en' h).1 hq
  have hClo : ∀ ls x ρ, Closing δ d (Tin m en Tout) Qin ls x ρ →
      Closing δ d Tout Qout ls (hndE (hndM m hr c) x) ρ :=
    fun _ _ _ h => handle_closing hmd hm0 hTd hTm hLin heq hea hr c Nf hc hN hret h
  let Ci : CPred := cwp δ d (Tin m en Tout) Qin
  let Fi : CPred := cwpF δ d (Tin m en Tout) Qin Ci
  let W₁ : CPred := fun ls x ρ => ∃ e, x = hndE (hndM m hr c) e ∧ Ci ls e ρ
  let W₂ : CPred := fun ls x ρ => ∃ ℓ K₁ y ρy ρf,
    x = (resK (kapV ℓ (hndM m hr c) K₁)).plug y ∧ cwp δ d Tout en.PB ls y ρy ∧
      frK ℓ K₁ en.PB Fi ls ρf ∧ ResU.CompS ρy ρf ρ
  let Y : CPred := fun ls x ρ => (W₁ ls x ρ ∨ W₂ ls x ρ) ∨ cwp δ d Tout Qout ls x ρ
  have hMY := divTab_mono δ d Tout Qout Y
  -- the resume frame, one segment, its continuation resumed into `Φ`
  have hframe : ∀ Φ : CPred, (∀ ls e ρ, Φ ls e ρ → cwpF δ d Tout Qout Y ls (hndE (hndM m hr c) e) ρ) →
      Φ.Le Fi → ∀ ℓ K₁ ls y ρy ρf ρ, cwp δ d Tout en.PB ls y ρy → frK ℓ K₁ en.PB Φ ls ρf →
      ResU.CompS ρy ρf ρ → cwpF δ d Tout Qout Y ls ((resK (kapV ℓ (hndM m hr c) K₁)).plug y) ρ := by
    intro Φ hΦ hΦF ℓ K₁ ls y ρy ρf ρ hy hf hcy
    exact cwpF_frame (hTd 0) (resK _) (resK_plain _).1 (resK_plain _).2 (frK ℓ K₁ en.PB Φ)
      frK_same frK_ext (fun n i en' h ha => absurd ha (by simp [(hLin n i en' h).2]))
      (fun n i en' h hq => absurd hq (by simp [(hLin n i en' h).1]))
      (fun n i en' h _ hq => absurd (hLin n i en' h).1 hq) en.PB Qout Y
      (fun ls y ρ ρ₂ ρ' hy hF hc => Or.inl (Or.inr ⟨ℓ, K₁, y, ρ, ρ₂, rfl, hy, frK_mono hΦF hF, hc⟩))
      (fun ls w σ hσ => frK_resume hMY hΦ hσ)
      (fun ls w σ hσ => frK_resume (opTable_mono _)
        (fun ls e ρ h => hClo _ _ _ (closing_of_cwpF hTd' (hΦF _ _ _ h))) hσ) hy hf hcy
  -- `W₁`, one segment, by induction on the inner segment
  have hA : ∀ ls e ρ, Ci ls e ρ → cwpF δ d Tout Qout Y ls (hndE (hndM m hr c) e) ρ := by
    intro ls e ρ he
    refine (ewp_ind (fun ls e ρ => cwpF δ d Tout Qout Y ls (hndE (hndM m hr c) e) ρ ∧ Fi ls e ρ)
      ?_ (cwp_out ls e ρ he)).1
    intro ls e ρ hs
    refine ⟨?_, ewp_fold (divTab_mono _ _ _ _ _) (ewpStep_mono (divTab_mono _ _ _ _ _)
      (fun _ _ _ h => h.2) hs)⟩
    refine ewp_fold hMY (wpG_bind (hndK (hndM m hr c)) e ls _ ρ (wpG_mono (fun ls' t σ ht => ?_) hs))
    rcases ht with ⟨v, rfl, hv⟩ | ht | ht
    · exact ewp_unfold hMY (ewp_step hMY (fun μ => Step1N.head (Head.hret μ m _ _ _ v) rfl) _ _ σ
        (cwpF_mono (fun _ _ _ h => Or.inr h) _ _ σ (cwp_out _ _ σ (hret ls' v σ hv))))
    · rcases ht with ⟨K₁, n, i, v, en', hp'⟩ | ⟨K₁, n, i, v, en', hp'⟩
      · obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρk, hcak, hPA, hu, hcont⟩ := pure_sep_iff.mp hp'
        rcases ext_some hT with ⟨rfl, rfl, rfl⟩ | hT'
        · -- an operation of `m`: the clause, `κ` given its cell, then `N v` under the resume frame
          refine ewp_unfold hMY (hnd_tick_like hMY n hr c K₁ hK₁ v fun ℓ σ₁ σ₂ hp hc' => ?_)
          refine ewp_pureSteps hMY (hc v _) _ _ σ₂ ?_
          obtain ⟨bc, hbc, hσ₂⟩ := compS_reassoc hcak hc'
          exact hframe (fun ls e ρ => cwpF δ d Tout Qout Y ls (hndE (hndM n hr c) e) ρ ∧ Fi ls e ρ)
            (fun _ _ _ h => h.1) (fun _ _ _ h => h.2) ℓ K₁ ls' (Nf v) ρa bc σ₂
            (hN ls' v ρa hPA) ⟨σ₁, ρk, ResU.CompS.comm hbc, hp, fun ls'' he => (hcont ls'' he).1⟩ hσ₂
        · -- another operation passes the handler
          exact wpG_here _ _ _ σ (Or.inr (Or.inl (hnd_fwd hTm hPC .hole (fun _ => rfl) (fun _ => rfl)
            rfl _ _ _ (Φ := fun ls e ρ => cwpF δ d Tout Qout Y ls (hndE (hndM m hr c) e) ρ ∧
              Fi ls e ρ) (fun _ _ _ h => h.1)
            (Or.inl ⟨K₁, n, i, v, en', pure_sep_mk ⟨rfl, hK₁, hT', ha⟩
              ⟨ρa, ρk, hcak, hPA, hu, hcont⟩⟩))))
      · obtain ⟨⟨rfl, hK₁, hT, ha⟩, -⟩ := pure_sep_iff.mp hp'
        rcases ext_some hT with ⟨-, -, rfl⟩ | hT'
        · exact absurd ha (by simp [hea])
        · exact absurd ha (by simp [(hLin _ _ _ hT').2])
    · -- a tick passes the handler: the coinductive case
      obtain ⟨K₁, n, i, v, en', hp'⟩ := ht
      obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρk, hcak, hPA, hu, hcont⟩ := pure_sep_iff.mp hp'
      obtain ⟨rfl, rfl, rfl⟩ := tickT_some hT
      refine wpG_here _ _ _ σ (Or.inr (Or.inr ⟨(hndK (hndM m hr c)).comp K₁, n, 0, v, tickEnt δ n,
        pure_sep_mk ⟨(Kont.plug_comp _ _ _).symm, ?_, hT, ha⟩
          ⟨ρa, ρk, hcak, hPA, And.intro (fun h => nomatch h) (fun ls'' he => And.intro
            (fun w τ₁ τ₂ hB hcτ => ?_) (fun h => absurd rfl h))⟩⟩))
      · rw [hasHnd_comp, hndK_hasHnd, hK₁]; simpa using hmd
      · have ho := (hcont ls'' he).1 w τ₁ τ₂ hB hcτ
        rw [Kont.plug_comp]
        exact ⟨Or.inl (Or.inl ⟨_, rfl, ho.1⟩), hClo _ _ _ ho.2⟩
  have hB : W₂.Le (cwpF δ d Tout Qout Y) := by
    rintro ls x ρ ⟨ℓ, K₁, y, ρy, ρf, rfl, hy, hF, hc⟩
    exact hframe Fi (fun ls e ρ h => hA ls e ρ (cwp_roll ls e ρ h)) (fun _ _ _ h => h)
      ℓ K₁ ls y ρy ρf ρ hy hF hc
  refine cwp_coind_up (W := fun ls x ρ => W₁ ls x ρ ∨ W₂ ls x ρ) ?_ ls _ ρ (Or.inl ⟨e, rfl, h⟩)
  rintro ls x ρ (⟨e, rfl, he⟩ | hx)
  · exact hA ls e ρ he
  · exact hB ls x ρ hx

end

/-- The relation of a resumption of `κ` at `cwp`: resumed at every answer, at every extension,
into the outer `cwp`. -/
def KapD (δ : LSub) (d : UInt32) (Tout : OpTab) (Qout : List SRec → Val → WProp) (en : OpEnt)
    (ls : List SRec) (κ : Val) : WProp := fun ρ =>
  ∀ ls', Ext ls ls' ρ → ∀ w, (en.PB ls' w ─⋆
    cwp δ d Tout Qout ls' (.app (.app (.val κ) (.val (Val.inj₁ .unit))) (.val w))) ρ

/-- **Not proved: `[handle]` of another name at a clause that is given `κ`** (`sorry`).

The clause `c` is opaque: its hypothesis `hop` is what the Fundamental Property gives a clause
of type `!U(A ⊗ K ⊸ F_{Σ, Div} R)`, at the relation of `cwp`.  The argument that works for
`handle_tail` does not go through here.  `κ` resumes into `hnd_m H K[w]`, the object the
coinduction is building.  `hop` asks `κ` to resume into `cwp` itself, and `hnd_m H K[w] ∈ cwp`
is the conclusion.  It is a candidate's member, not yet a member of `cwp`.

What it needs: `hop` at the coinduction's candidate `Y`, for `κ` resuming into `cwpF Y`.  This
is parametrized coinduction: the relation at a row holding `Div` carries an accumulator (Hur,
Neis, Dreyer, Vafeiadis, *The Power of Parameterization in Coinductive Proof*, POPL 2013).  Or
the relation is step-indexed at ticks, and `hop` is given at every index.  Either way the
parameter is in `𝒱⟦·⟧` at every thunk of a `Div` row, since `κ` is a value the clause may store.
The relation does not carry it today.  I have not derived this statement, and I have not
verified that any obstruction is real. -/
theorem handle_general {δ : LSub} {d m : UInt32} {Tout : OpTab} {en : OpEnt}
    (hmd : m ≠ d) (hm0 : m ≠ 0) (hTd : ∀ i, Tout d i = none) (hTm : ∀ i, Tout m i = none)
    (hLin : ∀ n i en', Tout n i = some en' → en'.q = .lin ∧ en'.abort = false)
    (heq : en.q = .lin) (hea : en.abort = false) (hr c : Val)
    {Qin Qout : List SRec → Val → WProp}
    (hop : ∀ ls v (κ : Val) ρ, (en.PA ls v ⋆ KapD δ d Tout Qout en ls κ) ρ →
      cwp δ d Tout Qout ls (.app (.val c) (.val (Val.pair v κ))) ρ)
    (hret : ∀ ls v ρ, Qin ls v ρ → cwp δ d Tout Qout ls (.app (.val hr) (.val v)) ρ)
    {ls : List SRec} {e : Expr} {ρ : WRes} (h : cwp δ d (Tin m en Tout) Qin ls e ρ) :
    cwp δ d Tout Qout ls (hndE (hndM m hr c) e) ρ := by
  sorry

end BoCa.Fig16.LogRel.Core.DivEffect

end
