import Support.Model.Tree.World.UpdAFrame
import Support.Model.Tree.World.StepKeep

/-!
# A run's mask is closed under its views' exclusive walks  `[spec §62]`

`RecMaskClosed` (`World/UpdAFrame.lean`): in a world meeting `RecInv`, a run's resource is
`ImmMaskClosed` at the masks of the records it owns (`recMaskClosed`). It is read off the world's
aliasable walk, not proved by induction on `TWNT`:

* **A view at depth shows in the aliasable walk** over its witness (`cellAt_imm_icp`), so a
  view `ζ` at a masked location `y` of the run's resource has the witness of the world's view
  `ψ = ag(W)(y)`.
* **The exclusive walk of a witness lies in its `ExDom`** (`ExDom.of_exRT`), and `ExDom` grows
  along `≤` and deletion (`ExDom.of_le`, `ExDom.of_del`).
* **At the lent location** `p.le`, `LeInvT` makes `ψ`'s witness `p.R`.
* **At a location of `p`'s escrow's exclusive part** a member `d` of `p`'s lineage holds a
  non-`imm` cell (`ExDom.linLoc`). `Coverage` classifies `ψ`:
  - a record `r`'s view at `r.le` over `r.R`. A record proper there would face `d`'s cell: an
    `own` cell is refused by `TIT`'s fourth clause, a `mut` cell by `NoMutT`. A sub-record sits
    at a `mut` cell of its parent's escrow, which is `d` (`ExclUniqueT`); so `r.R` is the witness
    of `d`'s `mut` cell, inside `ExDom d.R`.
  - a chain view of `r` at `y`. Chain positions hold `own` cells of `r.R` (`ChainT.own`), so `r`
    is `d` (`ExclUniqueT`), and the view's witness is a part of `d.R` (`chain_view_le`).
  Either way the witness's `ExDom` is inside `ExDom d.R ⊆ ExDom p.R` (`LinPathT.exDom`).

So the closure holds at every cell at depth (`CellAt`), not only along the walks; the case the
reborrow images raise (an image at a location of `ExDom p.R` over a chain view's witness) is the
chain-view case above.
-/

noncomputable section

namespace BoCa.Fig16.Tree.Wp
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree

variable {K : WCactus}

/-! ### `ExDom` and the exclusive walk at `○` -/

/-- **The exclusive walk at `○` lies in `ExDom`.** -/
theorem ExDom.of_exRT {ρ σ : TRes K} (h : ExRT ρ σ) :
    ∀ x (ψ : TCell K), σ.get x = some ψ → ExDom ρ x := by
  suffices key : ∀ x (ψ : TCell K), σ.get x = some ψ → ψ.kind ≠ Kind.imm → ExDom ρ x from
    fun x ψ e => key x ψ e (ExRT.immFree h x ψ e)
  refine G.ExW.rec
    (motive_1 := fun ρ σ _ => ∀ x (ψ : TCell K), σ.get x = some ψ → ψ.kind ≠ Kind.imm →
      ExDom ρ x)
    (motive_2 := fun ρ w _ => ∀ q ∈ w, ∀ x (ψ : TCell K), q.2.get x = some ψ →
      ψ.kind ≠ Kind.imm → ExDom ρ x)
    ?mk ?nil ?cons h
  case mk =>
    intro ρ' σ' nm b w hs hw hb hnm hσ ih x ψ e hk
    rcases back_kind hCR_kind hσ e hk with ⟨ψ₁, e₁, k₁, -⟩ | ⟨ψ₁, e₁, k₁, -⟩
    · rcases back_kind hCR_kind hnm e₁ (k₁ ▸ hk) with ⟨ψ₂, e₂, -, -⟩ | ⟨ψ₂, e₂, -, -⟩
      · obtain ⟨e₃, k₃⟩ := ResUT.restrict_eq_some.mp e₂
        exact .top e₃ (by rw [k₃]; simp)
      · obtain ⟨e₃, k₃⟩ := ResUT.restrict_eq_some.mp e₂
        exact .top e₃ (by rw [k₃]; simp)
    · obtain ⟨τ, hτ, ψ', e', k', -⟩ := bigComp_back_kind hCR_kind hb e₁ (k₁ ▸ hk)
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hτ
      exact ih q hq x ψ' e' (by rw [k', k₁]; exact hk)
  case nil => intro ρ' q hq; exact absurd hq (by simp)
  case cons =>
    intro ρ' e l w ψ hψ hk he hw ihe ihw q hq
    rcases List.mem_cons.mp hq with rfl | hq'
    · intro x φ ex kx
      exact .deep hψ hk (ihe x φ ex kx)
    · exact ihw q hq'

/-- `ExDom` grows along `≤`. -/
theorem ExDom.of_le {q R : TRes K} (hq : ResUT.Le q R) {x : BoCa.Loc} (h : ExDom q x) :
    ExDom R x := by
  obtain ⟨τ, hτ⟩ := hq
  cases h with
  | top e hk => exact .top (ResUT.CompS.get_left_of_ne_imm hτ e hk).2 hk
  | deep e hk h' =>
      exact .deep (ResUT.CompS.get_left_of_ne_imm hτ e (by rw [hk]; simp)).2 hk h'

/-- `ExDom` of a resource with a location deleted. -/
theorem ExDom.of_del {q : TRes K} {m x : BoCa.Loc} (h : ExDom (q.del m) x) : ExDom q x := by
  cases h with
  | @top _ _ ψ e hk =>
      by_cases hx : x = m
      · subst hx; rw [ResUT.del_get_self] at e; cases e
      · rw [ResUT.del_get_ne _ hx] at e; exact .top e hk
  | @deep _ _ y ψ e hk h' =>
      by_cases hy : y = m
      · subst hy; rw [ResUT.del_get_self] at e; cases e
      · rw [ResUT.del_get_ne _ hy] at e; exact .deep e hk h'

/-! ### A view at depth of a part of the world -/

/-- An `imm` cell at depth of a `●`-operand sits at depth of the composite over the same
witness. -/
theorem CellAt.imm_of_compS_right {a b c : TRes K} (hc : ResUT.CompS a b c) {y : BoCa.Loc}
    {ζ : TCell K} (h : CellAt b y ζ) (hk : ζ.kind = Kind.imm) :
    ∃ ζ', CellAt c y ζ' ∧ ζ'.kind = Kind.imm ∧ ζ'.wit = ζ.wit := by
  cases h with
  | top e =>
      obtain ⟨ζ', e', k', w', -⟩ := compS_get_right' hc e
      exact ⟨ζ', .top e', k'.trans hk, w'⟩
  | nest e h' =>
      obtain ⟨χ', e', -, w', -⟩ := compS_get_right' hc e
      exact ⟨ζ, .nest e' (w' ▸ h'), hk, rfl⟩

/-! ### The closure -/

/-- **`RecMaskClosed`.** A run's resource, a `●`-part of a world meeting `RecInv`, is closed at
the masks of the records it owns: a view at depth at a masked location has its witness's
exclusive walk masked. -/
theorem recMaskClosed : RecMaskClosed := by
  intro w fρ ρf ρ ps O psF ls hR hc hS y ζ hy hk hE ev hev x ξ hx
  obtain ⟨p, hpO, hpy⟩ := hE
  have hT := hR.1
  have hTI := hT.inv
  have hU := hT.exclUnique
  have hp : p ∈ ps := (hS.1 p).mpr (Or.inl hpO)
  have hprs : p ∈ rsOfT ls := (hTI.2.2.2.2.2.2.1 p).mpr ⟨p, hp, [], .nil p⟩
  obtain ⟨a, ha⟩ := agW_of_valid hT.valid
  -- the world's view at `y` has `ζ`'s witness
  obtain ⟨ζ', hζ', kζ', wζ'⟩ := CellAt.imm_of_compS_right hc hy hk
  obtain ⟨ψ, eψ, kψ, -, wψ, -⟩ := cellAt_imm_icp hζ' ha kζ'
  have hx' : ExDom ψ.wit x := by rw [wψ, wζ']; exact ExDom.of_exRT hev x ξ hx
  suffices hsub : ∀ x, ExDom ψ.wit x → ExDom p.R x from ⟨p, hpO, Or.inr (hsub x hx')⟩
  rcases hpy with rfl | hd
  · -- the lent location: the view is the record's, over its escrow
    obtain ⟨ψL, eL, -, -, wL⟩ := hTI.2.1 p hp a ha
    rw [eψ] at eL
    cases eL
    rw [wL]
    exact fun _ h => h
  · -- a location of the escrow's exclusive part: a lineage member holds a non-`imm` cell there
    obtain ⟨d, hpd, κ, eκ, kκ⟩ := hd.linLoc w.Θ p rfl (hTI.1.2.2.2.1 p hprs)
    have hdrs := hTI.desc_closed p hprs d hpd
    have hdp : ∀ x, ExDom d.R x → ExDom p.R x := fun x h => by
      obtain ⟨q, hq⟩ := hpd
      exact hq.exDom h
    rcases hTI.2.2.2.2.2.2.2 a ha y ψ eψ kψ with ⟨r, hr, hry, -, hwr⟩ |
        ⟨r, hr, p₀, S, u, hch⟩
    · -- a record's view at its location
      rw [hwr]
      obtain ⟨q, hq, hqr⟩ := (hTI.2.2.2.2.2.2.1 r).mp hr
      rcases hqr.cases with rfl | ⟨q', hq', hpath⟩
      · -- a record proper there would face `d`'s cell
        exfalso
        cases hkκ : κ.kind with
        | imm => exact kκ hkκ
        | own =>
            cases κ with
            | own u => exact hTI.2.2.2.1 r hr d hdrs u (hry ▸ eκ)
            | imm => cases hkκ
            | «mut» => cases hkκ
        | «mut» =>
            exact hTI.2.2.2.2.2.1.1 r hq
              (hry ▸ (hTI.recs_cellAt hT.valid hdrs _ _ eκ).mutAt hkκ)
      · -- a sub-record sits at its parent's `mut` cell, which is `d`'s
        obtain ⟨d', hd', hsubr⟩ := hpath.last hq'
        obtain ⟨-, ζr, eζr, kζr, -, wζr⟩ := hsubr
        have hqrs : q ∈ rsOfT ls := (hTI.2.2.2.2.2.2.1 q).mpr ⟨q, hq, [], .nil q⟩
        have hd'rs := hTI.desc_closed q hqrs d' hd'
        obtain rfl := hU d hdrs d' hd'rs y κ ζr eκ kκ (hry ▸ eζr) (by rw [kζr]; simp)
        intro x hx
        exact hdp x (.deep (hry ▸ eζr) kζr (wζr ▸ hx))
    · -- a chain view: its position holds an `own` cell of `r.R`, so `r` is `d`
      obtain rfl := hU d hdrs r hr y κ _ eκ kκ hch.own (by simp)
      obtain ⟨n, hn⟩ := hch.depth
      obtain ⟨q, hq, -, hw⟩ := chain_view_le hTI hr ha n p₀ y S u hn ψ eψ (by rw [kψ]; simp)
      intro x hx
      rw [hw] at hx
      exact hdp x (ExDom.of_le hq (ExDom.of_del hx))

end BoCa.Fig16.Tree.Wp

end
