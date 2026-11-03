import Support.Model.Tree.Port.ClosingSentence

/-!
# `Support/Model/Outlives.lean`'s step for `[TR]` 6.52, over the tree-stratified carrier

`[spec §62]`. From `Support/Model/Outlives.lean`, read at `CellUT K`. The printed
step is 6.52's *"there are no borrows, mutable or immutable, at any lifetime shorter than `α`,
so there cannot be any borrow that contains `ρ(ℓ)`"*. The chain reads "a borrow at a lifetime
shorter than `x`" as `@φ ⊏ x`. In the tree a cell carries a set of lifetimes, and a cell whose
witness holds a borrow carrying `x` has every member strictly below `x` (its witness lies in
its own stratum): `CellUT.Shorter φ x`. "No borrow shorter than `α`" is read as "in `Res_D`"
for `D = ↓α` (`WCactus.DownOf`, as in 6.27): `ResUT.not_shorter_of_down`.
-/

noncomputable section

namespace BoCa.Fig16.Tree
open BoCa.Fig16
variable {Loc Val : Type} {K : WCactus}

/-- `ψ` is a borrow strictly shorter than `x`: every lifetime of the cell is strictly below `x`. -/
def CellUT.Shorter (ψ : CellUT Loc Val K) (x : Life) : Prop :=
  ∃ t, ψ.lsOf = some t ∧ ∀ y ∈ t.set, K.lt y x

/-- A cell's witness is empty or lies in the cell's own stratum. -/
theorem CellUT.wit_cases (ψ : CellUT Loc Val K) :
    ψ.wit = PMap.empty ∨ ∃ t, ψ.lsOf = some t ∧ ψ.wit.InStratum t := by
  cases ψ with
  | own v => exact Or.inl rfl
  | imm i => exact Or.inr ⟨i.ls, rfl, CellUT.wit_inStratum_imm⟩
  | «mut» m => exact Or.inr ⟨m.ls, rfl, CellUT.wit_inStratum_mut⟩

/-- An `imm` cell with lifetime set `t′` lies in `Res_t` exactly when `t′` is above `t`. -/
theorem CellUT.above_of_lsOfI {ζ : CellUT Loc Val K} {t t' : TSet} (h : ζ.lsOfI = some t')
    (hi : ζ.InStratum t) : K.Above t t' := by
  cases ζ with
  | own v => simp [CellUT.lsOfI] at h
  | imm i => cases Option.some.inj h; exact hi
  | «mut» m => simp [CellUT.lsOfI] at h

theorem CellUT.kind_of_lsOfI {ζ : CellUT Loc Val K} {t : TSet} (h : ζ.lsOfI = some t) :
    ζ.kind = Kind.imm := by
  cases ζ with
  | own v => simp [CellUT.lsOfI] at h
  | imm i => rfl
  | «mut» m => simp [CellUT.lsOfI] at h

/-- A borrow carrying `x` nested in the witness of `ψ` makes `ψ` shorter than `x`. -/
theorem CellUT.shorter_of_nested {ψ : CellUT Loc Val K} {r : ResUT Loc Val K}
    (hr : ∀ T, ψ.wit.InStratum T → r.InStratum T) {l : Loc} {ξ : CellUT Loc Val K}
    (e : r.get l = some ξ) {t'' : TSet} (ht : ξ.lsOfI = some t'') {x : Life}
    (hx : x ∈ t''.set) : ψ.Shorter x := by
  rcases CellUT.wit_cases ψ with hw | ⟨t, hls, hin⟩
  · have := CellUT.above_of_lsOfI ht
      (hr (TSet.single x) (hw ▸ fun _ _ e => by simp at e) l ξ e)
    exact absurd (this x (by simp) x hx) (Cactus.lt_irrefl _ x)
  · exact ⟨t, hls, fun y hy => CellUT.above_of_lsOfI ht (hr t hin l ξ e) y hy x hx⟩

/-- A lifetime of a `○` composite is a lifetime of one of the operands. -/
theorem CellUT.CompR.lsOf_inv {ψ₁ ψ₂ ψ : CellUT Loc Val K} (h : CellUT.CompR ψ₁ ψ₂ ψ)
    {s : TSet} (hs : ψ.lsOfI = some s) {x : Life} (hx : x ∈ s.set) :
    (∃ t, ψ₁.lsOfI = some t ∧ x ∈ t.set) ∨ (∃ t, ψ₂.lsOfI = some t ∧ x ∈ t.set) := by
  cases h with
  | same ζ => exact Or.inl ⟨s, hs, hx⟩
  | strict k =>
      obtain ⟨t₁, t₂, w, τ, k₁, k₂, k₃, f₁, f₂, f₃⟩ := CellUT.compS_spec _ _ k
      rw [f₃] at hs
      have hxx : x ∈ (t₁ ∪ t₂).set := by
        rw [show t₁ ∪ t₂ = s from Option.some.inj hs]; exact hx
      rcases Finset.mem_union.mp hxx with hxx | hxx
      · exact Or.inl ⟨t₁, by rw [f₁]; rfl, hxx⟩
      · exact Or.inr ⟨t₂, by rw [f₂]; rfl, hxx⟩
  | mutMut => exact absurd hs (by simp [CellUT.mutOf, CellUT.lsOfI])
  | mutOwn => exact absurd hs (by simp [CellUT.mutOf, CellUT.lsOfI])
  | ownMut => exact absurd hs (by simp [CellUT.mutOf, CellUT.lsOfI])
  | immOwn => exact Or.inl ⟨s, hs, hx⟩
  | ownImm => exact Or.inr ⟨s, hs, hx⟩
  | immMut => exact Or.inl ⟨s, hs, hx⟩
  | mutImm => exact Or.inr ⟨s, hs, hx⟩

/-- The same at a location of a `○`. -/
theorem ResUT.CompR.lsOf_inv {ρ₁ ρ₂ ρ : ResUT Loc Val K} (h : ResUT.CompR ρ₁ ρ₂ ρ)
    {l : Loc} {ζ : CellUT Loc Val K} (hg : ρ.get l = some ζ) {s : TSet}
    (hs : ζ.lsOfI = some s) {x : Life} (hx : x ∈ s.set) :
    (∃ ξ t, ρ₁.get l = some ξ ∧ ξ.lsOfI = some t ∧ x ∈ t.set) ∨
    (∃ ξ t, ρ₂.get l = some ξ ∧ ξ.lsOfI = some t ∧ x ∈ t.set) := by
  rcases ResUT.Comp.get h l with ⟨-, -, e⟩ | ⟨ξ, e₁, -, e⟩ | ⟨ξ, -, e₂, e⟩ |
      ⟨ξ₁, ξ₂, ξ, e₁, e₂, e, hC⟩
  · rw [e] at hg; exact absurd hg (by simp)
  · rw [show ζ = ξ from Option.some.inj (hg.symm.trans e)] at hs
    exact Or.inl ⟨ξ, s, e₁, hs, hx⟩
  · rw [show ζ = ξ from Option.some.inj (hg.symm.trans e)] at hs
    exact Or.inr ⟨ξ, s, e₂, hs, hx⟩
  · rw [show ζ = ξ from Option.some.inj (hg.symm.trans e)] at hs
    rcases CellUT.CompR.lsOf_inv hC hs hx with ⟨t, ht, hxt⟩ | ⟨t, ht, hxt⟩
    · exact Or.inl ⟨ξ₁, t, e₁, ht, hxt⟩
    · exact Or.inr ⟨ξ₂, t, e₂, ht, hxt⟩

/-- The same along `⨀`. -/
theorem BigCompT.lsOf_inv :
    ∀ {L : List (ResUT Loc Val K)} {b : ResUT Loc Val K},
      BigCompT CellUT.CompatR CellUT.CompR L b →
      ∀ {l : Loc} {ζ : CellUT Loc Val K}, b.get l = some ζ →
      ∀ {s : TSet}, ζ.lsOfI = some s → ∀ {x : Life}, x ∈ s.set →
      ∃ σ ∈ L, ∃ ξ t, σ.get l = some ξ ∧ ξ.lsOfI = some t ∧ x ∈ t.set := by
  intro L
  induction L with
  | nil => intro b h l ζ hg s hs x hx; cases h; exact absurd hg (by simp)
  | cons σ L' ih =>
      intro b h l ζ hg s hs x hx
      cases h with
      | cons hrest hc =>
          rcases ResUT.CompR.lsOf_inv hc hg hs hx with
            ⟨ξ, t, e, ht, hxt⟩ | ⟨ξ, t, e, ht, hxt⟩
          · exact ⟨σ, List.mem_cons_self, ξ, t, e, ht, hxt⟩
          · obtain ⟨σ', hm, ξ', t', e', ht', hxt'⟩ := ih hrest e ht hxt
            exact ⟨σ', List.mem_cons_of_mem _ hm, ξ', t', e', ht', hxt'⟩

/-- A cell `ag(X)` raises to a location `X` does not cover sits strictly inside a borrow of
`X`: `[TR]` 6.52's *"there cannot be any borrow that contains `ρ(ℓ)`"*, read as a statement
about lifetimes. -/
theorem AgWT.lsOf_source {X a : ResUT BoCa.Loc BoCa.Val K} (h : AgWT X a)
    {l : BoCa.Loc} {ζ : CellUT BoCa.Loc BoCa.Val K} (hg : a.get l = some ζ)
    {s : TSet} (hs : ζ.lsOfI = some s) {x : Life} (hx : x ∈ s.set) :
    (∃ φ t, X.get l = some φ ∧ φ.lsOfI = some t ∧ x ∈ t.set) ∨
      (∃ m φ, X.get m = some φ ∧ φ.Shorter x) := by
  cases h with
  | mk hsm hsi hwm hwi hbm hbi ha hσ =>
      rcases ResUT.CompR.lsOf_inv hσ hg hs hx with ⟨ξ, t, e, ht, hxt⟩ | ⟨ξ, t, e, ht, hxt⟩
      · rcases ResUT.CompR.lsOf_inv ha e ht hxt with
          ⟨ξ', t', e', ht', hxt'⟩ | ⟨ξ', t', e', ht', hxt'⟩
        · exact Or.inl ⟨ξ', t', (ResUT.restrict_eq_some.mp e').1, ht', hxt'⟩
        · obtain ⟨σ, hm, ξ'', t'', e'', ht'', hxt''⟩ := BigCompT.lsOf_inv hbm e' ht' hxt'
          obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
          obtain ⟨ψq, hψq, hagq⟩ := AgWitsMT.mem hwm q hq
          exact Or.inr ⟨q.1, ψq, hψq, CellUT.shorter_of_nested
            (fun T hT => BoLo.AgWT.inStratum hagq T hT) e'' ht'' hxt''⟩
      · obtain ⟨σ, hm, ξ'', t'', e'', ht'', hxt''⟩ := BigCompT.lsOf_inv hbi e ht hxt
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
        obtain ⟨ψq, ev, av, hψq, hexq, hagq, hcq⟩ := AgWitsIT.mem hwi q hq
        exact Or.inr ⟨q.1, ψq, hψq, CellUT.shorter_of_nested
          (fun T hT => BoLo.inStratum_comp (BoLo.compR_hC T) hcq
            (BoLo.ExWT.inStratum BoLo.compR_hC hexq T hT)
            (BoLo.AgWT.inStratum hagq T hT)) e'' ht'' hxt''⟩

/-- If no borrow of `X` is shorter than `α`, then a cell of `⦇X⦈` carrying `α` among its
lifetimes is at a location `X` covers. -/
theorem ResUT.flat_imm_at_top_of_no_shorter {X σ : ResUT BoCa.Loc BoCa.Val K}
    {α : Life} (hσ : ResUT.Flat X σ) {l : BoCa.Loc}
    {ζ : CellUT BoCa.Loc BoCa.Val K} (hl : σ.get l = some ζ) {s : TSet}
    (hs : ζ.lsOfI = some s) (hmem : α ∈ s.set)
    (hnb : ∀ m φ, X.get m = some φ → ¬ φ.Shorter α) :
    ∃ φ t, X.get l = some φ ∧ φ.lsOfI = some t ∧ α ∈ t.set := by
  obtain ⟨ex, ag, hex, hag, hc⟩ := hσ
  refine (?_ : (∃ φ t, X.get l = some φ ∧ φ.lsOfI = some t ∧ α ∈ t.set) ∨
      (∃ m φ, X.get m = some φ ∧ φ.Shorter α)).resolve_right ?_
  · exact (by
      have hkζ : ζ.kind = Kind.imm := CellUT.kind_of_lsOfI hs
      have hexl : ex.get l = none := by
        cases f : ex.get l with
        | none => rfl
        | some ξ =>
            have hknz : ξ.kind ≠ Kind.imm := ExST.immFree hex l ξ f
            have hh := (ResUT.CompS.get_left_of_ne_imm hc f hknz).2
            rw [hl] at hh
            cases Option.some.inj hh
            exact absurd hkζ hknz
      have hagl : ag.get l = some ζ := by
        have hp := hc.2 l
        rw [hexl] at hp
        cases hag' : ag.get l with
        | none => rw [hag'] at hp; rw [hp] at hl; exact absurd hl (by simp)
        | some ψ =>
            rw [hag'] at hp
            exact congrArg some (Option.some.inj (hp.symm.trans hl))
      exact AgWT.lsOf_source hag hagl hs hmem)
  · rintro ⟨m, φ, hφ, hlt⟩; exact hnb m φ hφ hlt

/-- **"No borrow shorter than `α`" read as `Res_{↓α}`**: a resource in `Res_D`, `D = ↓α`,
carries no cell shorter than `α`. -/
theorem ResUT.not_shorter_of_down {α : Life} {D : TSet} (hD : K.DownOf D (TSet.single α))
    {X : ResUT Loc Val K} (h : X.InStratum D) :
    ∀ m φ, X.get m = some φ → ¬ φ.Shorter α := by
  rintro m φ e ⟨t, ht, hlt⟩
  obtain ⟨y, hy⟩ := t.ne
  have hφ := h m φ e
  have habove : K.Above D t := by
    cases φ with
    | own v => simp [CellUT.lsOf] at ht
    | imm i => cases Option.some.inj ht; exact hφ
    | «mut» n => cases Option.some.inj ht; exact hφ
  have hle : K.le α y := hD.2 y (fun d hd => habove d hd y hy) α (by simp)
  exact (hlt y hy).2 (K.antisymm (hlt y hy).1 hle)

/-- `@(ρ ⊟ ρ′) ⊐ α`: `[TR]` 6.52's second conclusion. `hoff` is the printed *"all parts of
the resource outlive `α`"*, off `dom(ρ′)`; `hon` is the printed exception *"except for the
locations in `ρ` that are mut or own in `ρ′ᵢ`"*. `ρ ∈ Res_{↓α}` is read through `hD`. -/
theorem ResUT.Sub.inStratum {ρ ρ' χ : ResUT Loc Val K} {α : Life} {D : TSet}
    (hD : K.DownOf D (TSet.single α))
    (h : ResUT.Sub ρ ρ' χ) (hd : ρ.InStratum D)
    (hoff : ∀ (l : Loc) (φ : CellUT Loc Val K), ρ'.get l = none →
        ρ.get l = some φ → φ.InStratum (TSet.single α))
    (hon : ∀ (l : Loc) (ζ : CellUT Loc Val K), ρ'.get l = some ζ →
        ∃ (s s' : TSet) (v : Val) (w : ResUT Loc Val K)
          (hs : w.InStratum s) (hs' : w.InStratum s'),
          ρ.get l = some (CellUT.immOf s v w hs) ∧
          ζ = CellUT.immOf s' v w hs' ∧ α ∈ s'.set) :
    χ.InStratum (TSet.single α) := by
  classical
  obtain ⟨ρ'', -, hle, -, hclause, hcomp⟩ := h
  intro l ψ hψ
  refine ResUT.inStratum_comp_at (CellUT.compS_hC (TSet.single α)) hcomp ?_ ?_ hψ
  · -- `ρ|own,mut`: at a location `ρ′` covers, `ρ`'s cell is `imm`
    intro φ hφ
    obtain ⟨hφg, hφk⟩ := ResUT.exclPart_eq_some.mp hφ
    cases hl : ρ'.get l with
    | none => exact hoff l φ hl hφg
    | some ζ =>
        obtain ⟨s, s', v, w, hs, hs', hρl, -, -⟩ := hon l ζ hl
        rw [show φ = CellUT.immOf s v w hs from Option.some.inj (hφg.symm.trans hρl)] at hφk
        exact absurd (CellUT.kind_immOf s v w hs) hφk
  · -- `ρ″`
    intro φ hφ
    cases hl : ρ'.get l with
    | none =>
        obtain ⟨f, hf⟩ := hle
        refine ResUT.CompS.inStratum_left_at hf (fun ω hω => ?_) hφ
        exact hoff l ω hl (ResUT.restrict_eq_some.mp hω).1
    | some ζ =>
        obtain ⟨s, s', v, w, hs, hs', hρl, hζ, hα⟩ := hon l ζ hl
        obtain ⟨hempty, hdiff⟩ :=
          hclause l s s' v w hs hs' hρl (hl.trans (congrArg some hζ))
        by_cases he : TSet.DiffEmpty s s'
        · rw [hempty he] at hφ; exact absurd hφ (by simp)
        · obtain ⟨u, hu⟩ := TSet.exists_diff he
          obtain ⟨hu', hgot⟩ := hdiff u hu he
          rw [show φ = CellUT.immOf u v w hu' from Option.some.inj (hφ.symm.trans hgot)]
          intro a ha z hz
          simp only [TSet.single_set, Finset.mem_singleton] at ha
          subst ha
          obtain ⟨hzs, hzn⟩ := (hu z).mp hz
          have hsD : K.Above D s := hd l _ hρl
          have hle' : K.le a z := hD.2 z (fun d hd' => hsD d hd' z hzs) a (by simp)
          exact ⟨hle', fun e => hzn (e ▸ hα)⟩

/-- `ρ|dom(ρ′ᵢ|mut,own)` carries `imm` cells only. -/
theorem ResUT.reb_restrictDom_exclPart_empty {α : Life} {ρ'i ρ : ResUT Loc Val K}
    (hreb : ResUT.Reb α ρ'i ρ) :
    (ρ.restrictDom ρ'i.exclPart).exclPart = PMap.empty := by
  refine PMap.ext fun m => ?_
  have hnone : (ρ.restrictDom ρ'i.exclPart).exclPart.get m = none := by
    cases f : (ρ.restrictDom ρ'i.exclPart).exclPart.get m with
    | none => rfl
    | some ξ =>
        obtain ⟨g1, g2⟩ := ResUT.exclPart_eq_some.mp f
        exact absurd (ResUT.reb_imm_image hreb (ResUT.restrictDom_get_inv g1)) g2
  rw [hnone]; rfl

end BoCa.Fig16.Tree

end
