import GhostEnd.Table

/-!
# GhostEnd — pieces whose stops report the dropped cell, each lend below the last

`Body.lean`'s `Open` hands a piece the view at each lend if the piece holds `m` (`vwOf`), a flag
read off the context. A frame holding the lend inside a value (`z : Mut 'x T ⊗ D`) holds it
whether or not `m` is live, and a frame holding a `Mut 'x T` that is an outer view weakened to
`'x` does not hold it at all. So whether a piece needs the view at the next lend is a fact about
the resource it froze, not about its context. Two changes record it.

* **A stop reports what it dropped** (`stopAtD`). The share at a stop is `drop_d ⋆ [α](…)`, where
  `drop_true` is a single `mut` cell at `ℓ` (`dropC`) and `drop_false` is `emp`. The continuation
  owed is `X α d`: it needs the view at the next lend exactly when the stop dropped a cell. The
  dropped cell stays in the share, beside the part in `[α]`. It owns nothing, and the lender
  disposes of it (`relend_of_openD`). Two dropped cells cannot meet: both are `mut` at `ℓ`, and
  `●` composes only `imm` cells (`dropC_disj`).
* **Each lend is below the last** (`OpenD`). The share frozen at `α` is in `Res_α`. It holds
  views of cells recorded strictly above `α` (`TabAt`), outer views among them, so the next lend
  is taken below `α`, where those cells are still in its stratum. `fresh` (`[TR]` p. 6, row 18)
  lets each re-lend choose its own bound, and `relend_of_openD` passes `α` as that bound.

The rest is `Body.lean`'s argument, unchanged: `bodyAtD_bind` carries a frame through one run and
`openD_bind` composes a piece with the rest by induction on the piece's own `OpenD`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace GhostEnd
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Kont Step1N Head performE opPayload)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- What a stop dropped: a single `mut` cell at `ℓ`, or nothing. -/
def dropC (l : BoCa.Loc) : Bool → WProp
  | true => fun ρ => ∃ ψ, ρ = ResU.single l ψ ∧ ψ.kind = Kind.mut
  | false => emp

/-- The view a piece is handed at a lend: `ℓ ↦ M_α`, if its last stop dropped a cell. -/
def vwD (l : BoCa.Loc) (T : VTy) (δ : LSub) : Bool → Life → List SRec → WProp
  | true => viewP l T δ
  | false => fun _ _ => emp

theorem dropC_noOwn {l : BoCa.Loc} {d : Bool} {ρ : WRes} (h : dropC l d ρ) : NoOwn ρ := by
  cases d with
  | false => obtain ⟨rfl, -⟩ := h; exact noOwn_empty
  | true =>
      obtain ⟨ψ, rfl, hk⟩ := h
      exact ResU.restrict_single_other (by rw [hk]; simp)

theorem vwD_noOwn {l : BoCa.Loc} {T : VTy} {δ : LSub} {d : Bool} {α : Life} {ls : List SRec}
    {ρ : WRes} (h : vwD l T δ d α ls ρ) : NoOwn ρ := by
  cases d with
  | false => obtain ⟨rfl, -⟩ := h; exact noOwn_empty
  | true => exact noOwn_ptoMutS h

/-- The view is a dropped cell. -/
theorem dropC_of_view {l : BoCa.Loc} {T : VTy} {δ : LSub} {α : Life} {ls : List SRec}
    {ρ : WRes} (h : viewP l T δ α ls ρ) : dropC l true ρ := by
  obtain ⟨b, u, σ, hσ, Q, hw, ls₀, -, rfl, -⟩ := h
  exact ⟨_, rfl, rfl⟩

/-- A non-`imm` cell of a part is the composite's cell. -/
theorem get_of_part {ρ₁ ρ₂ ρ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ) {l : BoCa.Loc}
    {ψ : CellU BoCa.Loc BoCa.Val} (e : ρ₁.get l = some ψ) (hk : ψ.kind ≠ Kind.imm) :
    ρ.get l = some ψ :=
  (ResU.CompS.get_left_of_ne_imm hc e hk).2

/-- **Two dropped cells cannot meet**: both are `mut` at `ℓ`, and `●` composes only `imm`. -/
theorem dropC_disj {l : BoCa.Loc} {ρa ρb ρ₁ ρ₂ ρ x y : WRes}
    (ha : dropC l true ρa) (hb : dropC l true ρb) (h₁ : ResU.CompS ρa x ρ₁)
    (h₂ : ResU.CompS ρb y ρ₂) (hc : ResU.CompS ρ₁ ρ₂ ρ) : False := by
  obtain ⟨ψ, rfl, hk⟩ := ha
  obtain ⟨φ, rfl, hk'⟩ := hb
  have hne : ∀ {χ : CellU BoCa.Loc BoCa.Val}, χ.kind = Kind.mut → χ.kind ≠ Kind.imm :=
    fun h e => by rw [h] at e; exact absurd e (by decide)
  have e₁ := get_of_part h₁ (ResU.single_get_self l ψ) (hne hk)
  have e₂ := get_of_part h₂ (ResU.single_get_self l φ) (hne hk')
  have := (ResU.CompS.get_left_of_ne_imm hc e₁ (hne hk)).1
  rw [e₂] at this; exact absurd this (by simp)

/-- `(a ● b) ● (c ● d) = (a ● c) ● (b ● d)`. -/
theorem compS_four {a b c d ab cd x : WRes} (hab : ResU.CompS a b ab) (hcd : ResU.CompS c d cd)
    (hx : ResU.CompS ab cd x) :
    ∃ ac bd, ResU.CompS a c ac ∧ ResU.CompS b d bd ∧ ResU.CompS ac bd x := by
  obtain ⟨bcd, hbcd, hx₁⟩ := compS_reassoc hab hx
  obtain ⟨bd, hbd, hcbd⟩ := compS_lcomm hcd hbcd
  obtain ⟨ac, hac, hx₂⟩ := compS_reassoc' hcbd hx₁
  exact ⟨ac, bd, hac, hbd, hx₂⟩

/-- The two drops of a stop under a frame, joined: at most one is a cell. -/
theorem dropC_join {l : BoCa.Loc} {d₁ d₂ : Bool} (hd : ¬ (d₁ = true ∧ d₂ = true)) {ρa ρb ρ : WRes}
    (ha : dropC l d₁ ρa) (hb : dropC l d₂ ρb) (hc : ResU.CompS ρa ρb ρ) :
    dropC l (d₁ || d₂) ρ := by
  cases d₁ <;> cases d₂
  · obtain ⟨rfl, -⟩ := ha; obtain ⟨rfl, -⟩ := hb
    exact ⟨eq_of_compS_empty_left hc, trivial⟩
  · obtain ⟨rfl, -⟩ := ha; rw [eq_of_compS_empty_left hc]; exact hb
  · obtain ⟨rfl, -⟩ := hb
    rw [ResU.CompS.functional hc (ResU.comp_empty_right ρa)]; exact ha
  · exact absurd ⟨rfl, rfl⟩ hd

/-- A stop with the lend open at `α`: the dropped cell beside a share in `[α]` that, with the
owner handed back, the table admits, owing `owner ⋆ X α d`. -/
def stopAtD (Tb : Table) (l : BoCa.Loc) (T : VTy) (δ : LSub)
    (X : Life → Bool → List SRec → Expr → WProp) (α : Life) : List SRec → Expr → WProp :=
  fun ls t => ex fun d => dropC l d ⋆ box α (all fun w => ptoOwn l w ─⋆ (vC true T ls δ w ─⋆
    Tb ls t (fun ls' e' => owner l T δ ls' ⋆ X α d ls' e')))

/-- One run with the lend open at `α`: an answer in `Q α`, or a stop. -/
def bodyAtD (Tb : Table) (l : BoCa.Loc) (T : VTy) (δ : LSub)
    (Q : Life → List SRec → Val → WProp) (X : Life → Bool → List SRec → Expr → WProp)
    (α : Life) : List SRec → Expr → WProp :=
  fun ls e => wpG ls e (fun ls'' t ρ => valPost (Q α) ls'' t ρ ∨ stopAtD Tb l T δ X α ls'' t ρ)

/-- One unfolding below the bound `β`: at every `α ⊏ β`, the share is in `[α]` and, handed the
view if the last stop dropped one, runs at `α`. -/
def openFD (Tb : Table) (l : BoCa.Loc) (T : VTy) (δ : LSub) (Q : Life → List SRec → Val → WProp)
    (X : Life → Bool → List SRec → Expr → WProp) : Life → Bool → List SRec → Expr → WProp :=
  fun β d ls e ρ => ∀ α, α ⊏ β → box α (vwD l T δ d α ls ─⋆ bodyAtD Tb l T δ Q X α ls e) ρ

/-- A borrower piece: the least fixed point of `openFD`, over the bound and the drop. -/
def OpenD (Tb : Table) (l : BoCa.Loc) (T : VTy) (δ : LSub) (Q : Life → List SRec → Val → WProp)
    (β : Life) (d : Bool) (ls : List SRec) (e : Expr) : WProp := fun ρ =>
  ∀ X : Life → Bool → List SRec → Expr → WProp,
    (∀ β d ls e ρ, openFD Tb l T δ Q X β d ls e ρ → X β d ls e ρ) → X β d ls e ρ

section
variable {Tb : Table} {l : BoCa.Loc} {T : VTy} {δ : LSub} {Q : Life → List SRec → Val → WProp}

theorem stopAtD_mono (hTb : Tb.Mono) {X X' : Life → Bool → List SRec → Expr → WProp}
    (hX : ∀ β d ls e ρ, X β d ls e ρ → X' β d ls e ρ) {α : Life} {ls : List SRec} {t : Expr} :
    Entails (stopAtD Tb l T δ X α ls t) (stopAtD Tb l T δ X' α ls t) := by
  rintro ρ ⟨d, ρ₁, ρ₂, hc, hd, h⟩
  refine ⟨d, ρ₁, ρ₂, hc, hd, fun w ρa ρb ha hcab ρc ρd hv hccd => ?_, h.2⟩
  exact hTb _ _ _ _ _ (fun _ _ _ ⟨τ₁, τ₂, hcτ, ho, hx⟩ => ⟨τ₁, τ₂, hcτ, ho, hX _ _ _ _ _ hx⟩)
    (h.1 w ρa ρb ha hcab ρc ρd hv hccd)

theorem bodyAtD_mono (hTb : Tb.Mono) {X X' : Life → Bool → List SRec → Expr → WProp}
    (hX : ∀ β d ls e ρ, X β d ls e ρ → X' β d ls e ρ) {α : Life} {ls : List SRec} {e : Expr} :
    Entails (bodyAtD Tb l T δ Q X α ls e) (bodyAtD Tb l T δ Q X' α ls e) :=
  fun _ h => wpG_mono (fun _ _ _ hq => hq.imp id (stopAtD_mono hTb hX _)) h

theorem openFD_mono (hTb : Tb.Mono) {X X' : Life → Bool → List SRec → Expr → WProp}
    (hX : ∀ β d ls e ρ, X β d ls e ρ → X' β d ls e ρ) {β : Life} {d : Bool} {ls : List SRec}
    {e : Expr} : Entails (openFD Tb l T δ Q X β d ls e) (openFD Tb l T δ Q X' β d ls e) :=
  fun _ h α hα => box_mono (wand_mono_right (bodyAtD_mono hTb hX)) _ (h α hα)

theorem openD_fold (hTb : Tb.Mono) {β : Life} {d : Bool} {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : openFD Tb l T δ Q (OpenD Tb l T δ Q) β d ls e ρ) : OpenD Tb l T δ Q β d ls e ρ :=
  fun X hX => hX β d ls e ρ (openFD_mono hTb (fun _ _ _ _ _ h' => h' X hX) ρ h)

theorem openD_unfold (hTb : Tb.Mono) {β : Life} {d : Bool} {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : OpenD Tb l T δ Q β d ls e ρ) : openFD Tb l T δ Q (OpenD Tb l T δ Q) β d ls e ρ :=
  h (fun β d ls e ρ => openFD Tb l T δ Q (OpenD Tb l T δ Q) β d ls e ρ)
    (fun _ _ _ _ _ h' => openFD_mono hTb (fun _ _ _ _ _ h'' => openD_fold hTb h'') _ h')

theorem openD_ind (P : Life → Bool → List SRec → Expr → WProp)
    (hP : ∀ β d ls e ρ, openFD Tb l T δ Q P β d ls e ρ → P β d ls e ρ) {β : Life} {d : Bool}
    {ls : List SRec} {e : Expr} {ρ : WRes} (h : OpenD Tb l T δ Q β d ls e ρ) : P β d ls e ρ :=
  h P hP

/-- A pure run answering in `Q α` is a run with the lend open at `α`. -/
theorem bodyAtD_of_wpTS {X : Life → Bool → List SRec → Expr → WProp} {α : Life}
    {ls : List SRec} {e : Expr} {ρ : WRes} (h : wpTS ls e (Q α) ρ) :
    bodyAtD Tb l T δ Q X α ls e ρ :=
  wpG_mono (fun _ _ _ hq => Or.inl hq) ((wpTS_iff_wpG _ _ _ _).mp h)

/-- **`OpenD` gives `Relend`** when its answer hands the owner back. At each lend `Relend` hands
the view; a piece whose last stop dropped nothing leaves it behind. At a stop the dropped cell
is left behind too, and the continuation's bound is the lend just ended. -/
theorem relend_of_openD (hTb : Tb.Mono) {Q₀ : List SRec → Val → WProp} {β : Life} {d : Bool}
    {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : OpenD Tb l T δ
      (fun α ls v => box α (all fun w => ptoOwn l w ─⋆ (vC true T ls δ w ─⋆ Q₀ ls v))) β d ls e ρ) :
    Relend Tb l T δ Q₀ ls e ρ := by
  refine openD_ind (fun _ _ ls e ρ => Relend Tb l T δ Q₀ ls e ρ)
    (fun β d ls e ρ hF => ?_) h
  refine relend_fold hTb ⟨β, fun α hα => ⟨fun ρm σ hm hcm => ?_, (hF α hα).2⟩⟩
  -- the view: fed to the piece, or left behind
  have hb : wpG ls e (fun ls'' t => (fun τ => NoOwn τ) ⋆ fun ρ =>
      valPost (fun ls v => box α (all fun w => ptoOwn l w ─⋆ (vC true T ls δ w ─⋆ Q₀ ls v)))
        ls'' t ρ ∨ stopAtD Tb l T δ (fun _ _ ls e ρ => Relend Tb l T δ Q₀ ls e ρ) α ls'' t ρ)
      σ := by
    cases d with
    | true =>
        refine wpG_mono (fun _ _ τ hq => ⟨PMap.empty, τ, compS_empty_left τ, noOwn_empty, hq⟩) ?_
        exact (hF α hα).1 ρm σ hm hcm
    | false =>
        have hb₀ := (hF α hα).1 PMap.empty ρ ⟨rfl, trivial⟩ (ResU.comp_empty_right ρ)
        exact wpG_mono (fun _ _ _ ⟨τ₁, τ₂, hc, hq, hn⟩ => ⟨τ₂, τ₁, ResU.CompS.comm hc, hn, hq⟩)
          (wpG_frame (fun _ τ => NoOwn τ) (fun _ _ _ h => h) σ
            ⟨ρ, ρm, hcm, hb₀, noOwn_ptoMutS hm⟩)
  refine wpG_garbage (wpG_mono (fun ls'' t τ hq => ?_) hb)
  obtain ⟨τn, τq, hcτ, hn, hq⟩ := hq
  rcases hq with ⟨v, rfl, hv⟩ | ⟨d', τd, τs, hcd, hdd, hs⟩
  · exact ⟨τq, τn, ResU.CompS.comm hcτ, hn, fun w ρa ρb ha hcab ρc ρd hc hccd =>
      Or.inl ⟨v, rfl, hv.1 w ρa ρb ha hcab ρc ρd hc hccd⟩, hv.2⟩
  · -- the dropped cell joins the garbage
    obtain ⟨g, hg, hcg⟩ := compS_reassoc' hcd hcτ
    refine ⟨τs, g, ResU.CompS.comm hcg, ?_, fun w ρa ρb ha hcab ρc ρd hc hccd =>
      Or.inr (hs.1 w ρa ρb ha hcab ρc ρd hc hccd), hs.2⟩
    exact noOwn_compS hg hn (dropC_noOwn hdd)

end

/-! ### A pure context around a piece, a frame carried through its stops -/

section
variable {Tab : OpTab} {l : BoCa.Loc} {T : VTy} {δ : LSub}

/-- **Bind at one run.** `K` pure around a run with the lend open at `α`, the frame `Fr α`
carried. At an answer `K[v]` runs at the same `α` (`hk`). At a stop the frame freezes (`hfz`):
a part `Fz α d₂` in `Res_α`, and what it drops. The piece's drop and the frame's are joined, and
cannot both be cells (`dropC_disj`). The frozen frame joins the continuation (`hX`). -/
theorem bodyAtD_bind (hLR : LinResume Tab) (K : Kont) (hH : ∀ n, K.HasHnd n = false)
    (Fr : Life → List SRec → WProp) (Fz : Life → Bool → List SRec → WProp)
    (hFs : ∀ α ls ls', (∀ x, x ∈ ls' ↔ x ∈ ls) → Entails (Fr α ls) (Fr α ls'))
    (hFe : ∀ α d ls ls' ρ, Ext ls ls' ρ → Fz α d ls ρ → Fz α d ls' ρ)
    (hFo : ∀ α d ls ρ, Fz α d ls ρ → ρ.InStratum α)
    {Q₁ Q : Life → List SRec → Val → WProp} {X₁ X : Life → Bool → List SRec → Expr → WProp}
    {α : Life}
    (hfz : ∀ ls ρ, Fr α ls ρ → ∃ d ρz ρn, ResU.CompS ρz ρn ρ ∧ Fz α d ls ρz ∧ dropC l d ρn)
    (hX : ∀ d₁ d₂ ls e ρ₁ ρz ρ, ¬ (d₁ = true ∧ d₂ = true) → X₁ α d₁ ls e ρ₁ → Fz α d₂ ls ρz →
      ResU.CompS ρ₁ ρz ρ → X α (d₁ || d₂) ls (K.plug e) ρ)
    (hk : ∀ ls v, Entails (Q₁ α ls v ⋆ Fr α ls)
      (bodyAtD (opTable Tab) l T δ Q X α ls (K.plug (.val v))))
    {ls : List SRec} {e : Expr} {ρ₁ ρf ρ : WRes}
    (h : bodyAtD (opTable Tab) l T δ Q₁ X₁ α ls e ρ₁) (hf : Fr α ls ρf)
    (hc : ResU.CompS ρ₁ ρf ρ) :
    bodyAtD (opTable Tab) l T δ Q X α ls (K.plug e) ρ := by
  refine wpG_bind K e ls _ ρ ?_
  refine wpG_mono (fun ls' t σ ht => ?_) (wpG_frame (Fr α) (hFs α ls) ρ ⟨ρ₁, ρf, hc, h, hf⟩)
  obtain ⟨σ₁, σ₂, hcσ, hp, hF'⟩ := ht
  rcases hp with ⟨v, rfl, hv⟩ | ⟨d₁, ρa, σs, hca, hda, hs⟩
  · exact hk ls' v σ ⟨σ₁, σ₂, hcσ, hv, hF'⟩
  obtain ⟨d₂, ρz, ρn, hczn, hz, hdn⟩ := hfz ls' σ₂ hF'
  have hnd : ¬ (d₁ = true ∧ d₂ = true) := by
    rintro ⟨rfl, rfl⟩
    exact dropC_disj hda hdn hca (ResU.CompS.comm hczn) hcσ
  -- regroup: the two drops, and the share in `[α]` with the frozen frame
  obtain ⟨ρD, ρS, hcD, hcS, hcDS⟩ := compS_four hca (ResU.CompS.comm hczn) hcσ
  refine wpG_here _ _ _ σ (Or.inr ⟨d₁ || d₂, ρD, ρS, hcDS, dropC_join hnd hda hdn hcD, ?_,
    (outlives_comp hcS α).mpr ⟨hs.2, hFo α d₂ ls' ρz hz⟩⟩)
  intro w ρo ρb ho hcob ρt ρd hv hctd
  obtain ⟨u, hu, hcu⟩ := compS_exch hcS hcob
  obtain ⟨u', hu', hcu'⟩ := compS_exch hcu hctd
  have hst := hs.1 w ρo u ho hu ρt u' hv hu'
  refine opTable_frame hLR K hH (Fz α d₂) (hFe α d₂) ?_ hst hz hcu'
  rintro ls₂ e₂ τ₁ τz τ ⟨τo, τx, hcox, hoo, hx⟩ hz₂ hcτ
  obtain ⟨y, hy, hcy⟩ := compS_reassoc hcox hcτ
  exact ⟨τo, y, hcy, hoo, hX d₁ d₂ _ _ _ _ _ hnd hx hz₂ hy⟩

/-- **Bind.** A pure context `K` around a piece, the frozen frame `Fz β d₂` beside it, every lend
below a bound `B`. At each unfolding the whole's view goes to whichever dropped the cell, and the
frozen frame thaws to the live frame (`hthaw`). By induction on the piece's `OpenD`. -/
theorem openD_bind (hLR : LinResume Tab) (K : Kont) (hH : ∀ n, K.HasHnd n = false)
    (B : Life) (Fr : Life → List SRec → WProp) (Fz : Life → Bool → List SRec → WProp)
    (hFs : ∀ α ls ls', (∀ x, x ∈ ls' ↔ x ∈ ls) → Entails (Fr α ls) (Fr α ls'))
    (hFe : ∀ α d ls ls' ρ, Ext ls ls' ρ → Fz α d ls ρ → Fz α d ls' ρ)
    (hFo : ∀ α d ls ρ, Fz α d ls ρ → ρ.InStratum α)
    (hfz : ∀ α, α ⊏ B → ∀ ls ρ, Fr α ls ρ →
      ∃ d ρz ρn, ResU.CompS ρz ρn ρ ∧ Fz α d ls ρz ∧ dropC l d ρn)
    (hthaw : ∀ β α d₂ ls ρv ρz ρ, α ⊏ β → β ≤ B → vwD l T δ d₂ α ls ρv → Fz β d₂ ls ρz →
      ResU.CompS ρv ρz ρ → Fr α ls ρ)
    {Q₁ Q : Life → List SRec → Val → WProp}
    (hk : ∀ α, α ⊏ B → ∀ ls v, Entails (Q₁ α ls v ⋆ Fr α ls)
      (bodyAtD (opTable Tab) l T δ Q (OpenD (opTable Tab) l T δ Q) α ls (K.plug (.val v))))
    {β : Life} (hβ : β ≤ B) {d₁ d₂ : Bool} (hd : ¬ (d₁ = true ∧ d₂ = true))
    {ls : List SRec} {e : Expr} {ρ₁ ρz ρ : WRes}
    (h : OpenD (opTable Tab) l T δ Q₁ β d₁ ls e ρ₁) (hz : Fz β d₂ ls ρz)
    (hc : ResU.CompS ρ₁ ρz ρ) :
    OpenD (opTable Tab) l T δ Q β (d₁ || d₂) ls (K.plug e) ρ := by
  have hTb := opTable_mono Tab
  revert d₂ ρz ρ
  refine openD_ind (fun β d₁ ls e ρ₁ => β ≤ B → ∀ {d₂ : Bool}, ¬ (d₁ = true ∧ d₂ = true) →
    ∀ {ρz ρ : WRes}, Fz β d₂ ls ρz → ResU.CompS ρ₁ ρz ρ →
      OpenD (opTable Tab) l T δ Q β (d₁ || d₂) ls (K.plug e) ρ) ?_ h hβ
  intro β d₁ ls e ρ₁ hF hβ d₂ hd ρz ρ hz hc
  refine openD_fold hTb fun α hα => ⟨fun ρv σ hv hcv => ?_,
    (outlives_comp hc α).mpr ⟨(hF α hα).2, (hFo β d₂ ls ρz hz).mono (le_of_lt hα)⟩⟩
  have hαB : α ⊏ B := lt_of_lt_of_le hα hβ
  -- thaw: the whole's view goes to the piece or to the frame
  obtain ⟨y, hy, hcy⟩ := compS_reassoc hc hcv
  have hrun : ∀ {ρp ρq : WRes}, vwD l T δ d₁ α ls ρp → Fr α ls ρq →
      ∀ {σ' : WRes}, ResU.CompS ρ₁ ρp σ' → ResU.CompS σ' ρq σ →
      bodyAtD (opTable Tab) l T δ Q (OpenD (opTable Tab) l T δ Q) α ls (K.plug e) σ := by
    intro ρp ρq hp hq σ' h₁ h₂
    have hb := (hF α hα).1 ρp σ' hp h₁
    exact bodyAtD_bind hLR K hH Fr Fz hFs hFe hFo (hfz α hαB)
      (fun d₁' d₂' ls e τ₁ τz τ hdd hx hz' hcτ => hx (le_of_lt hαB) hdd hz' hcτ)
      (hk α hαB) hb hq h₂
  cases d₁ with
  | true =>
      obtain rfl : d₂ = false := by cases d₂ <;> simp_all
      have hfr := hthaw β α false ls PMap.empty ρz ρz hα hβ ⟨rfl, trivial⟩ hz (compS_empty_left ρz)
      obtain ⟨y', hy', hcy'⟩ := compS_exch hc hcv
      exact hrun hv hfr hy' hcy'
  | false =>
      have hfr := hthaw β α d₂ ls ρv ρz y hα hβ (by simpa using hv) hz (ResU.CompS.comm hy)
      exact hrun ⟨rfl, trivial⟩ hfr (ResU.comp_empty_right ρ₁) hcy

end

end GhostEnd
