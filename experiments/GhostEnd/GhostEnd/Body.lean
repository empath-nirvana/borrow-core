import GhostEnd.Chain

/-!
# GhostEnd — the borrower's run between stops, and composition

`Relend` (`Relend.lean`) asks of a callback: lent at a fresh `α`, it runs to its *final* answer or
to a stop. A borrower with loops and branches is built from pieces, and a piece's answer is not
the borrower's: control continues in the same lend. This file adds the open-ended form.

* `bodyAt Vw Q X α`: one run with the lend open at `α`. It answers in `Q α` with the lend still
  open, or stops with its share in `[α]`, hands the owner back, and owes `owner ⋆ X`.
* `Open Vw Q`: the least fixed point. At each unfolding the lend is taken at a fresh `α` below a
  fixed bound `β`, and the piece receives `Vw α`. `Vw` is the borrower's view (`viewP`) for a
  piece that holds `m`, and `emp` for one that does not.

**The measure.** `Relend` is a least fixed point, and the run after a re-lend is a different run
from the one the stop came from. `open_bind` composes a piece with the rest of the borrower by
induction on the piece's own `Open`. Its stops' continuations are `Open` again, and an `Open`
quantifies the lifetime of every later lend at its own unfolding. So the induction hypothesis
already covers the re-lent run, whatever lifetime is chosen there. No induction on an `ewpTS` at
a fixed lifetime is needed. The other measures a borrower needs are its syntax (`Typed.lean`) and
a loop's fuel (`Loop.lean`). Both are data of the term and do not mention a lifetime.

* `relend_of_open`: an `Open` piece whose answer hands the owner back is `Relend`;
* `open_step`, `open_fold`, `open_unfold`: pure steps, and one unfolding;
* `bodyAt_bind`, `open_bind`: a pure context around a piece, a frame carried through its stops;
* `open_yield`: a yield with the lend open, the view dropped at the stop and re-lent after.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace GhostEnd
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Kont Step1N Head performE opPayload)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- The borrower's view `ℓ ↦ M_α 𝒱⟦T⟧δ` at the list `ls`. -/
abbrev viewP (l : BoCa.Loc) (T : VTy) (δ : LSub) (α : Life) (ls : List SRec) : WProp :=
  ptoMutS l α ls (fun ls₀ => vC true T ls₀ δ)

/-- A stop with the lend open at `α`: the share is in `[α]`, and with the owner handed back the
table admits the stop, owing `owner ⋆ X` to the continuation. -/
def stopAt (Tb : Table) (l : BoCa.Loc) (T : VTy) (δ : LSub) (X : List SRec → Expr → WProp)
    (α : Life) : List SRec → Expr → WProp :=
  fun ls t => box α (all fun w => ptoOwn l w ─⋆ (vC true T ls δ w ─⋆
    Tb ls t (fun ls' e' => owner l T δ ls' ⋆ X ls' e')))

/-- One run with the lend open at `α`: an answer in `Q α`, the lend still open, or a stop. -/
def bodyAt (Tb : Table) (l : BoCa.Loc) (T : VTy) (δ : LSub)
    (Q : Life → List SRec → Val → WProp) (X : List SRec → Expr → WProp) (α : Life) :
    List SRec → Expr → WProp :=
  fun ls e => wpG ls e (fun ls'' t ρ => valPost (Q α) ls'' t ρ ∨ stopAt Tb l T δ X α ls'' t ρ)

/-- One unfolding: at every `α ⊏ β`, the share is in `[α]` and, given `Vw α`, runs at `α`. -/
def openF (Tb : Table) (l : BoCa.Loc) (T : VTy) (δ : LSub) (β : Life)
    (Vw : Life → List SRec → WProp) (Q : Life → List SRec → Val → WProp)
    (X : List SRec → Expr → WProp) : List SRec → Expr → WProp :=
  fun ls e ρ => ∀ α, α ⊏ β → box α (Vw α ls ─⋆ bodyAt Tb l T δ Q X α ls e) ρ

/-- A borrower piece: the least fixed point of `openF`, written in `Prop` as `ewpTS` is. -/
def Open (Tb : Table) (l : BoCa.Loc) (T : VTy) (δ : LSub) (β : Life)
    (Vw : Life → List SRec → WProp) (Q : Life → List SRec → Val → WProp)
    (ls : List SRec) (e : Expr) : WProp := fun ρ =>
  ∀ X : List SRec → Expr → WProp, (∀ ls e ρ, openF Tb l T δ β Vw Q X ls e ρ → X ls e ρ) →
    X ls e ρ

section
variable {Tb : Table} {l : BoCa.Loc} {T : VTy} {δ : LSub} {β : Life}
  {Vw : Life → List SRec → WProp} {Q : Life → List SRec → Val → WProp}

theorem stopAt_mono (hTb : Tb.Mono) {X X' : List SRec → Expr → WProp}
    (hX : ∀ ls e ρ, X ls e ρ → X' ls e ρ) {α : Life} {ls : List SRec} {t : Expr} :
    Entails (stopAt Tb l T δ X α ls t) (stopAt Tb l T δ X' α ls t) := by
  refine box_mono fun ρ h w ρa ρb ha hcab ρc ρd hc hccd => ?_
  exact hTb _ _ _ _ _ (fun _ _ _ ⟨τ₁, τ₂, hcτ, ho, hx⟩ => ⟨τ₁, τ₂, hcτ, ho, hX _ _ _ hx⟩)
    (h w ρa ρb ha hcab ρc ρd hc hccd)

theorem bodyAt_mono (hTb : Tb.Mono) {X X' : List SRec → Expr → WProp}
    (hX : ∀ ls e ρ, X ls e ρ → X' ls e ρ) {α : Life} {ls : List SRec} {e : Expr} :
    Entails (bodyAt Tb l T δ Q X α ls e) (bodyAt Tb l T δ Q X' α ls e) :=
  fun _ h => wpG_mono (fun _ _ _ hq => hq.imp id (stopAt_mono hTb hX _)) h

theorem openF_mono (hTb : Tb.Mono) {X X' : List SRec → Expr → WProp}
    (hX : ∀ ls e ρ, X ls e ρ → X' ls e ρ) {ls : List SRec} {e : Expr} :
    Entails (openF Tb l T δ β Vw Q X ls e) (openF Tb l T δ β Vw Q X' ls e) :=
  fun _ h α hα => box_mono (wand_mono_right (bodyAt_mono hTb hX)) _ (h α hα)

/-- One unfolding introduces `Open`. -/
theorem open_fold (hTb : Tb.Mono) {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : openF Tb l T δ β Vw Q (Open Tb l T δ β Vw Q) ls e ρ) : Open Tb l T δ β Vw Q ls e ρ :=
  fun X hX => hX ls e ρ (openF_mono hTb (fun _ _ _ h' => h' X hX) ρ h)

/-- `Open` unfolds once. -/
theorem open_unfold (hTb : Tb.Mono) {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : Open Tb l T δ β Vw Q ls e ρ) : openF Tb l T δ β Vw Q (Open Tb l T δ β Vw Q) ls e ρ :=
  h (fun ls e ρ => openF Tb l T δ β Vw Q (Open Tb l T δ β Vw Q) ls e ρ)
    (fun _ _ _ h' => openF_mono hTb (fun _ _ _ h'' => open_fold hTb h'') _ h')

/-- Induction on `Open`. -/
theorem open_ind (P : List SRec → Expr → WProp)
    (hP : ∀ ls e ρ, openF Tb l T δ β Vw Q P ls e ρ → P ls e ρ) {ls : List SRec} {e : Expr}
    {ρ : WRes} (h : Open Tb l T δ β Vw Q ls e ρ) : P ls e ρ :=
  h P hP

/-- `Open` is closed under a pure step in front. -/
theorem open_step (hTb : Tb.Mono) {ls : List SRec} {e e' : Expr}
    (hs : ∀ μ : Heap, Step1N μ e μ e') {ρ : WRes} (h : Open Tb l T δ β Vw Q ls e' ρ) :
    Open Tb l T δ β Vw Q ls e ρ := by
  refine open_fold hTb fun α hα => ?_
  exact box_mono (wand_mono_right (wpG_step hs ls _)) ρ (open_unfold hTb h α hα)

/-- A pure run answering in `Q α` is a run with the lend open at `α`. -/
theorem bodyAt_of_wpTS {X : List SRec → Expr → WProp} {α : Life} {ls : List SRec} {e : Expr}
    {ρ : WRes} (h : wpTS ls e (Q α) ρ) : bodyAt Tb l T δ Q X α ls e ρ :=
  wpG_mono (fun _ _ _ hq => Or.inl hq) ((wpTS_iff_wpG _ _ _ _).mp h)

/-- **`Open` gives `Relend`** when its answer hands the owner back: `Relend`'s value clause is
`Open`'s at `Q̃ α ls v = [α] ∀w. ℓ ↦ w ─⋆ 𝒱⟦T⟧(w) ─⋆ Q ls v`. -/
theorem relend_of_open (hTb : Tb.Mono) {Q₀ : List SRec → Val → WProp} {ls : List SRec}
    {e : Expr} {ρ : WRes}
    (h : Open Tb l T δ β (viewP l T δ)
      (fun α ls v => box α (all fun w => ptoOwn l w ─⋆ (vC true T ls δ w ─⋆ Q₀ ls v))) ls e ρ) :
    Relend Tb l T δ Q₀ ls e ρ := by
  refine open_ind (fun ls e ρ => Relend Tb l T δ Q₀ ls e ρ) (fun ls e ρ hF => ?_) h
  refine relend_fold hTb ⟨β, fun α hα => ?_⟩
  refine box_mono (wand_mono_right fun σ hw => wpG_mono (fun ls'' t τ hq => ?_) hw) ρ (hF α hα)
  rcases hq with ⟨v, rfl, hv⟩ | hs
  · exact ⟨fun w ρa ρb ha hcab ρc ρd hc hccd =>
      Or.inl ⟨v, rfl, hv.1 w ρa ρb ha hcab ρc ρd hc hccd⟩, hv.2⟩
  · exact ⟨fun w ρa ρb ha hcab ρc ρd hc hccd =>
      Or.inr (hs.1 w ρa ρb ha hcab ρc ρd hc hccd), hs.2⟩

end

/-! ### Stops under a pure context, with a frame -/

/-- Every operation of the table is linear and resumes: no `raise` stops, and no continuation is
cancelled. -/
def LinResume (Tab : OpTab) : Prop :=
  ∀ n i en, Tab n i = some en → en.abort = false ∧ en.q = .lin

/-- **A stop under a pure context, a frame joined to its continuation.** `K` holds no handler.
The continuation of `K[t]` is `K` around the continuation of `t`, and the frame `Fz` (Kripke
along `Ext`) joins its share. -/
theorem opTable_frame {Tab : OpTab} (hLR : LinResume Tab) (K : Kont)
    (hH : ∀ n, K.HasHnd n = false) (Fz : List SRec → WProp)
    (hFe : ∀ ls ls' ρ, Ext ls ls' ρ → Fz ls ρ → Fz ls' ρ)
    {Φ Φ' : List SRec → Expr → WProp}
    (hΦ : ∀ ls e ρ₁ ρz ρ, Φ ls e ρ₁ → Fz ls ρz → ResU.CompS ρ₁ ρz ρ → Φ' ls (K.plug e) ρ)
    {ls : List SRec} {t : Expr} {ρ₁ ρz ρ : WRes} (h : opTable Tab ls t Φ ρ₁) (hz : Fz ls ρz)
    (hc : ResU.CompS ρ₁ ρz ρ) : opTable Tab ls (K.plug t) Φ' ρ := by
  rcases h with ⟨K₁, n, i, v, en, hp⟩ | ⟨K₁, n, i, v, en, hp⟩
  · obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρk, hcak, hA, hu, hcont⟩ := pure_sep_iff.mp hp
    obtain ⟨ρk', hk', hcσ'⟩ := compS_reassoc hcak hc
    have hq := (hLR n i en hT).2
    refine Or.inl ⟨K.comp K₁, n, i, v, en, pure_sep_mk ⟨(Kont.plug_comp _ _ _).symm, ?_, hT, ha⟩
      ⟨ρa, ρk', hcσ', hA, fun hu' => absurd (hq.symm.trans hu') (by decide),
        fun ls'' he => ⟨?_, fun hq' => absurd hq hq'⟩⟩⟩
    · rw [hasHnd_comp, hH, hK₁]; rfl
    · intro w τ₁ τ₂ hB hcτ
      obtain ⟨z, hz', hcz⟩ := compS_exch hk' hcτ
      rw [Kont.plug_comp]
      exact hΦ _ _ _ _ _ ((hcont ls'' (he.left hk')).1 w τ₁ z hB hz')
        (hFe ls ls'' ρz (he.right hk') hz) hcz
  · obtain ⟨⟨-, -, hT, ha⟩, -⟩ := pure_sep_iff.mp hp
    rw [(hLR n i en hT).1] at ha; exact absurd ha (by decide)

section
variable {Tab : OpTab} {l : BoCa.Loc} {T : VTy} {δ : LSub} {β : Life}

/-- **Bind at one run.** `K` pure around a run with the lend open at `α`; the frame `Fr α`
(live at `α`) is carried through. At an answer the continuation `K[v]` runs at the same `α`
(`hk`). At a stop the frame is frozen (`hfz`: a part in `Fz`, in `[α]`, and garbage that owns
nothing: the frame's view, if it holds one), and joins the continuation, which `hX` turns from
the piece's into the whole's. -/
theorem bodyAt_bind (hLR : LinResume Tab) (K : Kont) (hH : ∀ n, K.HasHnd n = false)
    (Fr : Life → List SRec → WProp) (Fz : List SRec → WProp)
    (hFs : ∀ α ls ls', (∀ x, x ∈ ls' ↔ x ∈ ls) → Entails (Fr α ls) (Fr α ls'))
    (hFe : ∀ ls ls' ρ, Ext ls ls' ρ → Fz ls ρ → Fz ls' ρ)
    (hFo : ∀ ls ρ, Fz ls ρ → ∀ α, α ⊏ β → ρ.InStratum α)
    (hfz : ∀ α ls ρ, Fr α ls ρ → ∃ ρz ρn, ResU.CompS ρz ρn ρ ∧ Fz ls ρz ∧ NoOwn ρn)
    {Q₁ Q : Life → List SRec → Val → WProp} {X₁ X : List SRec → Expr → WProp}
    (hX : ∀ ls e ρ₁ ρz ρ, X₁ ls e ρ₁ → Fz ls ρz → ResU.CompS ρ₁ ρz ρ → X ls (K.plug e) ρ)
    {α : Life} (hα : α ⊏ β)
    (hk : ∀ ls v, Entails (Q₁ α ls v ⋆ Fr α ls)
      (bodyAt (opTable Tab) l T δ Q X α ls (K.plug (.val v))))
    {ls : List SRec} {e : Expr} {ρ₁ ρf ρ : WRes}
    (h : bodyAt (opTable Tab) l T δ Q₁ X₁ α ls e ρ₁) (hf : Fr α ls ρf)
    (hc : ResU.CompS ρ₁ ρf ρ) :
    bodyAt (opTable Tab) l T δ Q X α ls (K.plug e) ρ := by
  refine wpG_bind K e ls _ ρ ?_
  refine wpG_mono (fun ls' t σ ht => ?_) (wpG_frame (Fr α) (hFs α ls) ρ ⟨ρ₁, ρf, hc, h, hf⟩)
  obtain ⟨σ₁, σ₂, hcσ, hp, hF'⟩ := ht
  rcases hp with ⟨v, rfl, hv⟩ | hs
  · exact hk ls' v σ ⟨σ₁, σ₂, hcσ, hv, hF'⟩
  -- a stop: freeze the frame, drop its garbage, and join it to the continuation
  obtain ⟨ρz, ρn, hczn, hz, hn⟩ := hfz α ls' σ₂ hF'
  obtain ⟨s, hs₁, hcs⟩ := compS_reassoc' hczn hcσ
  refine wpG_garbage (wpG_here _ _ _ σ ⟨s, ρn, hcs, hn, Or.inr ?_⟩)
  refine ⟨fun w ρa ρb ha hcab ρc ρd hv hccd => ?_,
    (outlives_comp hs₁ α).mpr ⟨hs.2, hFo ls' ρz hz α hα⟩⟩
  -- the owner joins the piece's share; the frozen frame stays beside it
  obtain ⟨u, hu, hcu⟩ := compS_exch hs₁ hcab
  obtain ⟨u', hu', hcu'⟩ := compS_exch hcu hccd
  have hst := hs.1 w ρa u ha hu ρc u' hv hu'
  refine opTable_frame hLR K hH Fz hFe ?_ hst hz hcu'
  rintro ls₂ e₂ τ₁ τz τ ⟨τo, τx, hcox, ho, hx⟩ hz₂ hcτ
  obtain ⟨y, hy, hcy⟩ := compS_reassoc hcox hcτ
  exact ⟨τo, y, hcy, ho, hX _ _ _ _ _ hx hz₂ hy⟩

/-- **Bind.** A pure context `K` around a piece, the frozen frame `Fz` beside it. At each
unfolding the whole's `Vw₂ α` and the frozen frame give the piece's `Vw₁ α` and the live frame
`Fr α` (`hthaw`). By induction on the piece's `Open`. -/
theorem open_bind (hLR : LinResume Tab) (K : Kont) (hH : ∀ n, K.HasHnd n = false)
    {Vw₁ Vw₂ : Life → List SRec → WProp}
    (Fr : Life → List SRec → WProp) (Fz : List SRec → WProp)
    (hFs : ∀ α ls ls', (∀ x, x ∈ ls' ↔ x ∈ ls) → Entails (Fr α ls) (Fr α ls'))
    (hFe : ∀ ls ls' ρ, Ext ls ls' ρ → Fz ls ρ → Fz ls' ρ)
    (hFo : ∀ ls ρ, Fz ls ρ → ∀ α, α ⊏ β → ρ.InStratum α)
    (hfz : ∀ α ls ρ, Fr α ls ρ → ∃ ρz ρn, ResU.CompS ρz ρn ρ ∧ Fz ls ρz ∧ NoOwn ρn)
    (hthaw : ∀ α ls ρv ρz ρ, α ⊏ β → Vw₂ α ls ρv → Fz ls ρz → ResU.CompS ρv ρz ρ →
      ∃ ρ₁ ρ₂, ResU.CompS ρ₁ ρ₂ ρ ∧ Vw₁ α ls ρ₁ ∧ Fr α ls ρ₂)
    {Q₁ Q : Life → List SRec → Val → WProp}
    (hk : ∀ α, α ⊏ β → ∀ ls v, Entails (Q₁ α ls v ⋆ Fr α ls)
      (bodyAt (opTable Tab) l T δ Q (Open (opTable Tab) l T δ β Vw₂ Q) α ls (K.plug (.val v))))
    {ls : List SRec} {e : Expr} {ρ₁ ρz ρ : WRes}
    (h : Open (opTable Tab) l T δ β Vw₁ Q₁ ls e ρ₁) (hz : Fz ls ρz)
    (hc : ResU.CompS ρ₁ ρz ρ) :
    Open (opTable Tab) l T δ β Vw₂ Q ls (K.plug e) ρ := by
  have hTb := opTable_mono Tab
  revert ρz ρ
  refine open_ind (fun ls e ρ₁ => ∀ {ρz ρ : WRes}, Fz ls ρz → ResU.CompS ρ₁ ρz ρ →
    Open (opTable Tab) l T δ β Vw₂ Q ls (K.plug e) ρ) ?_ h
  intro ls e ρ₁ hF ρz ρ hz hc
  refine open_fold hTb fun α hα => ⟨fun ρv σ hv hcv => ?_,
    (outlives_comp hc α).mpr ⟨(hF α hα).2, hFo ls ρz hz α hα⟩⟩
  -- thaw: the whole's view and the frozen frame give the piece's view and the live frame
  obtain ⟨y, hy, hcy⟩ := compS_reassoc hc hcv
  obtain ⟨π₁, π₂, hcπ, hv₁, hfr⟩ := hthaw α ls ρv ρz y hα hv hz (ResU.CompS.comm hy)
  obtain ⟨y', hy', hcy'⟩ := compS_reassoc' hcπ hcy
  have hb := (hF α hα).1 π₁ y' hv₁ hy'
  exact bodyAt_bind hLR K hH Fr Fz hFs hFe hFo hfz
    (fun ls e τ₁ τz τ hx hz' hcτ => hx hz' hcτ) hα (hk α hα) hb hfr hcy'

end

/-! ### A yield with the lend open -/

/-- **A yield with the lend open.** The piece holds `Vw α` and a frame `Fr` in `[α]`. It stops
at once. The view is dropped (garbage: a `mut` cell owns nothing, `hVn`), the frame stays in the
share, and the owner handed back goes to the continuation. At the resumption the rest is `Open`
again, at a lifetime chosen afresh (`h`). The yield is linear, so the continuation is never
cancelled. -/
theorem open_yield {Tab : OpTab} (hLR : LinResume Tab) {n i : UInt32} {en : OpEnt}
    (hTn : Tab n i = some en)
    (hPB : ∀ ls w ρ, en.PB ls w ρ → w = Val.unit ∧ ρ = PMap.empty)
    {l : BoCa.Loc} {T : VTy} {δ : LSub} {β : Life} {Vw : Life → List SRec → WProp}
    (hVn : ∀ α ls ρ, Vw α ls ρ → NoOwn ρ)
    {Q : Life → List SRec → Val → WProp}
    (Fr : List SRec → WProp) (hFe : ∀ ls ls' ρ, Ext ls ls' ρ → Fr ls ρ → Fr ls' ρ)
    (hFo : ∀ ls ρ, Fr ls ρ → ∀ α, α ⊏ β → ρ.InStratum α)
    {y : Val} (hy : ∀ ls, en.PA ls y PMap.empty) {rest : Expr}
    (h : ∀ ls ρ, Fr ls ρ → Open (opTable Tab) l T δ β Vw Q ls rest ρ) (ls : List SRec)
    (ργ : WRes) (hF : Fr ls ργ) :
    Open (opTable Tab) l T δ β Vw Q ls (yieldSeq n i y rest) ργ := by
  have hTb := opTable_mono Tab
  obtain ⟨ha, hq⟩ := hLR n i en hTn
  refine open_fold hTb fun α hα => ⟨fun ρm ρ₂ hm hc => ?_, hFo ls ργ hF α hα⟩
  refine wpG_garbage (wpG_here _ _ _ ρ₂ ⟨ργ, ρm, hc, hVn α ls ρm hm, Or.inr ?_⟩)
  refine ⟨fun w ρa ρb hown hcab ρc ρd hv hccd => Or.inl ⟨.seq .hole rest, n, i, y, en,
    pure_sep_mk ⟨rfl, rfl, hTn, ha⟩ ⟨PMap.empty, ρd, compS_empty_left ρd, hy ls, ?_⟩⟩,
    hFo ls ργ hF α hα⟩
  obtain ⟨s, hs, hρs⟩ := compS_reassoc hcab hccd
  refine ⟨fun hu => absurd (hq.symm.trans hu) (by decide),
    fun ls' hext => ⟨fun w' τ₁ τ₂ hBw hcτ => ?_, fun hl => absurd hq hl⟩⟩
  obtain ⟨rfl, rfl⟩ := hPB _ _ _ hBw
  obtain rfl : τ₂ = ρd := ResU.CompS.functional hcτ (ResU.comp_empty_right ρd)
  refine ⟨s, ργ, ResU.CompS.comm hρs,
    ⟨w, ρa, ρc, hs, hown, vC_local true T ((hext.right hρs).right hs) hv⟩, ?_⟩
  exact open_step hTb (fun μ => Step1N.head (Head.seq μ rest) rfl)
    (h ls' ργ (hFe ls ls' ργ (hext.left hρs) hF))

end GhostEnd
