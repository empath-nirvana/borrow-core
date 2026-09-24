import Paper.S1_Syntax.Definitions
import Paper.S5_Model.Definitions
import Paper.S6_1_StandardLemmas.Lemmas
import Paper.S6_2_NonStandardLemmas.Definitions
import Support.Model.Algebra
import Support.Model.AlgebraInstances
import Support.Model.Ancestors
import Support.Model.CellFacts
import Support.Model.Cells
import Support.Model.Composition
import Support.Model.Flattening
import Support.Model.FlatteningCells
import Support.Model.Lifetimes
import Support.Model.Outlives
import Support.Model.Prelude
import Support.Model.Reborrow
import Support.Model.Singletons
import Support.Model.Update
import Support.Model.WalkSplitting

/-!
# Support — Model — Surgery

`[about ours]`.  The steps of the surgery lemmas 6.21–6.29, 6.34, 6.38 and 6.39: the normal forms of `⦇ρ ● ℓ ↦ own(v) ● ρ_v⦈` and `⦇ρ ● ℓ ↦ imm(α, v, ρ_v)⦈`, and the `mut` cell against `ρ_v ● ℓ ↦ own(v)`.
-/

noncomputable section

namespace BoCa.Fig16
variable {Loc Val : Type}

/-- `⨀_●` is `⨀_○` on the same list: 6.31 at every step of the fold. -/
theorem BigComp.toR {L : List (ResU Loc Val)} {b : ResU Loc Val}
    (h : BigComp CellU.CompatS CellU.CompS L b) :
    BigComp CellU.CompatR CellU.CompR L b := by
  induction h with
  | nil => exact BigComp.nil
  | cons _ hc ih => exact BigComp.cons ih (ResU.CompS.toCompR hc)

/-- `○` drops no lifetime from an `imm` operand.
`[about ours: the set half of "`ag(ρ)` keeps every `imm` cell of `ρ`"]` -/
theorem CellU.CompR.ls_imm {ψ₁ ψ₂ ψ : CellU Loc Val} (hc : CellU.CompR ψ₁ ψ₂ ψ)
    {s₁ : LSet} {v₁ : Val} {χ₁ : ResU Loc Val} {h₁ : χ₁.InStratum s₁.join}
    (e₁ : ψ₁ = CellU.immOf s₁ v₁ χ₁ h₁)
    {s : LSet} {v : Val} {χ : ResU Loc Val} {h : χ.InStratum s.join}
    (e : ψ = CellU.immOf s v χ h) {x : Life} (hx : s₁.mem x) : s.mem x := by
  cases hc with
  | same χ' =>
      obtain ⟨hs, -, -⟩ := CellU.immOf_inj (e₁.symm.trans e)
      exact hs ▸ hx
  | strict k =>
      obtain ⟨t₁, t₂, w, τ, k₁, k₂, k₃, f₁, f₂, f₃⟩ := CellU.compS_spec _ _ k
      obtain ⟨ht₁, -, -⟩ := CellU.immOf_inj (e₁.symm.trans f₁)
      obtain ⟨ht, -, -⟩ := CellU.immOf_inj (f₃.symm.trans e)
      exact ht ▸ Or.inl (ht₁ ▸ hx)
  | mutMut a b w τ ha hb P Q hP hQ => exact absurd e₁.symm CellU.immOf_ne_mutOf
  | mutOwn a w τ ha P hP => exact absurd e₁.symm CellU.immOf_ne_mutOf
  | ownMut a w τ ha P hP => exact absurd e₁ CellU.ownOf_ne_immOf
  | immOwn t w τ ht =>
      obtain ⟨hs, -, -⟩ := CellU.immOf_inj (e₁.symm.trans e)
      exact hs ▸ hx
  | ownImm t w τ ht => exact absurd e₁ CellU.ownOf_ne_immOf
  | immMut t w τ ht b hb P hP =>
      obtain ⟨hs, -, -⟩ := CellU.immOf_inj (e₁.symm.trans e)
      exact hs ▸ hx
  | mutImm t w τ ht b hb P hP => exact absurd e₁.symm CellU.immOf_ne_mutOf

/-- The same at a location of a `○`. -/
theorem ResU.CompR.get_ls_imm {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompR ρ₁ ρ₂ ρ)
    {l : Loc} {s₁ : LSet} {v₁ : Val} {χ₁ : ResU Loc Val} {h₁ : χ₁.InStratum s₁.join}
    (e₁ : ρ₁.get l = some (CellU.immOf s₁ v₁ χ₁ h₁))
    {s : LSet} {v : Val} {χ : ResU Loc Val} {hh : χ.InStratum s.join}
    (e : ρ.get l = some (CellU.immOf s v χ hh)) {x : Life} (hx : s₁.mem x) : s.mem x := by
  rcases h.get l with ⟨f₁, -, -⟩ | ⟨ζ, f₁, -, f⟩ | ⟨ζ, f₁, -, -⟩ | ⟨ζ₁, ζ₂, ζ, f₁, -, f, hC⟩
  · rw [e₁] at f₁; exact absurd f₁ (by simp)
  · rw [e₁] at f₁
    rw [← Option.some.inj f₁] at f
    obtain ⟨hs, -, -⟩ := CellU.immOf_inj (Option.some.inj (f.symm.trans e))
    exact hs ▸ hx
  · rw [e₁] at f₁; exact absurd f₁ (by simp)
  · rw [e₁] at f₁
    exact CellU.CompR.ls_imm hC (Option.some.inj f₁).symm
      (Option.some.inj (f.symm.trans e)) hx

/-- The same through `ag`. -/
theorem AgW.get_ls_imm {ρ σ : ResU Loc Val} (h : AgW ρ σ)
    {l : Loc} {s₁ : LSet} {v₁ : Val} {χ₁ : ResU Loc Val} {h₁ : χ₁.InStratum s₁.join}
    (e₁ : ρ.get l = some (CellU.immOf s₁ v₁ χ₁ h₁))
    {s : LSet} {v : Val} {χ : ResU Loc Val} {hh : χ.InStratum s.join}
    (e : σ.get l = some (CellU.immOf s v χ hh)) {x : Life} (hx : s₁.mem x) : s.mem x := by
  cases h with
  | mk hsm hsi hwm hwi hbm hbi ha hσ =>
      have hk₁ : (CellU.immOf s₁ v₁ χ₁ h₁).kind = Kind.imm := CellU.kind_immOf _ _ _ _
      obtain ⟨ζ, hζ, hkζ, -, -⟩ :=
        ResU.CompR.get_imm_left ha (ResU.restrict_get_some e₁ hk₁) hk₁
      obtain ⟨t, ht, hetaζ⟩ := CellU.imm_eta hkζ
      refine ResU.CompR.get_ls_imm hσ (hζ.trans (congrArg some hetaζ)) e ?_
      exact ResU.CompR.get_ls_imm ha (ResU.restrict_get_some e₁ hk₁)
        (hζ.trans (congrArg some hetaζ)) hx

/-- The same through `⦇−⦈`. -/
theorem ResU.Flat.get_ls_imm {ρ σ : ResU Loc Val} (h : ResU.Flat ρ σ)
    {l : Loc} {s₁ : LSet} {v₁ : Val} {χ₁ : ResU Loc Val} {h₁ : χ₁.InStratum s₁.join}
    (e₁ : ρ.get l = some (CellU.immOf s₁ v₁ χ₁ h₁))
    {s : LSet} {v : Val} {χ : ResU Loc Val} {hh : χ.InStratum s.join}
    (e : σ.get l = some (CellU.immOf s v χ hh)) {x : Life} (hx : s₁.mem x) : s.mem x := by
  obtain ⟨ex, ag, hex, hag, hc⟩ := h
  have hk₁ : (CellU.immOf s₁ v₁ χ₁ h₁).kind = Kind.imm := CellU.kind_immOf _ _ _ _
  obtain ⟨ζ, hζ, hkζ, -, -⟩ := AgW.get_imm hag e₁ hk₁
  have : σ.get l = some ζ := ResU.CompS.get_right_of_immFree hc (ExS.immFree hex) hζ
  rw [e] at this
  obtain rfl : ζ = CellU.immOf s v χ hh := (Option.some.inj this).symm
  exact AgW.get_ls_imm hag e₁ hζ hx

/-- If `⦇X⦈` carries an `imm` cell at `ℓ` one of whose lifetimes is `α`, and
every other cell of the flattening lies in `Res_α`, then `X` carries a cell at
`ℓ`: `[TR]` 6.29's (p. 11) *"all borrows in `⦇ρ′⦈` other than `ρᵢ` must be
disjoint from `α`, which by well-formedness of the resource `ρ′` implies that
the cell … cannot be in any `ρ″` …"*, repeated in 6.52 (p. 17).
*"Well-formedness"* is Fig. 16's typing of the borrow cells' witnesses, which
are arguments of `CellU.immOf` and `CellU.mutOf`.
`[about ours: the step of `[TR]` 6.29's and 6.52's proofs]` -/
theorem ResU.flat_imm_at_top {X σ : ResU BoCa.Loc BoCa.Val} {α : Life}
    (hσ : ResU.Flat X σ) {l : BoCa.Loc} {s : LSet} {v : BoCa.Val}
    {χ : ResU BoCa.Loc BoCa.Val} {h : χ.InStratum s.join}
    (hl : σ.get l = some (CellU.immOf s v χ h)) (hmem : s.mem α)
    (hoff : ∀ m, m ≠ l → ∀ ψ, σ.get m = some ψ → ψ.InStratum α) :
    ∃ φ, X.get l = some φ := by
  obtain ⟨ex', ag', hex', hag', hc'⟩ := hσ
  have hpoint : ∀ m, (∀ ζ, σ.get m = some ζ → ζ.InStratum α) →
      ∀ ψ, X.get m = some ψ → ψ.InStratum α := by
    intro m hstr ψ hm
    by_cases hk : ψ.kind = Kind.imm
    · obtain ⟨ζ, hζ, hkζ, hle⟩ := BoLo.agW_get_at hag' hm hk
      have hσm : σ.get m = some ζ :=
        ResU.CompS.get_right_of_immFree hc' (ExS.immFree hex') hζ
      exact BoLo.cell_inStratum_of_at (lt_of_lt_of_le
        (BoLo.cell_at_of_inStratum (by rw [hkζ]; simp) (hstr ζ hσm)) hle)
    · exact hstr ψ (ResU.CompS.get_left_of_ne_imm hc'
        (ExS.get_of_ne_imm hex' hm hk) hk).2
  cases hg : X.get l with
  | some φ => exact ⟨φ, rfl⟩
  | none =>
      exfalso
      have hin : X.InStratum α := by
        intro m ψ hm
        by_cases hml : m = l
        · subst hml; rw [hg] at hm; exact absurd hm (by simp)
        · exact hpoint m (fun ζ hζ => hoff m hml ζ hζ) ψ hm
      have hbad := BoLo.flat_inStratum ⟨ex', ag', hex', hag', hc'⟩ hin l _ hl
      rw [CellU.inStratum_immOf] at hbad
      exact absurd (s.meet_least α hmem) (not_le_of_gt hbad)

/-- `○` at two `imm` cells over one value and one witness unions the lifetime
sets: the *"by the definition of `○` and `●`"* of `[TR]` 6.51's proof. -/
theorem CellU.CompR.imm_union {ψ₁ ψ₂ ζ : CellU Loc Val} (h : CellU.CompR ψ₁ ψ₂ ζ)
    {a b : LSet} {v : Val} {χ : ResU Loc Val}
    {ha : χ.InStratum a.join} {hb : χ.InStratum b.join}
    (e₁ : ψ₁ = CellU.immOf a v χ ha) (e₂ : ψ₂ = CellU.immOf b v χ hb) :
    ∃ h' : χ.InStratum (a ∪ b).join, ζ = CellU.immOf (a ∪ b) v χ h' := by
  cases h with
  | same ψ =>
      obtain ⟨hab, -, -⟩ := CellU.immOf_inj (e₁.symm.trans e₂)
      subst hab
      refine ⟨by rw [LSet.union_self]; exact ha, ?_⟩
      rw [e₁]
      exact CellU.immOf_congr (LSet.union_self a).symm rfl rfl ha _
  | strict k =>
      obtain ⟨s₁, s₂, w, τ, k₁, k₂, k₃, f₁, f₂, f₃⟩ := CellU.compS_spec _ _ k
      rw [e₁] at f₁; rw [e₂] at f₂
      obtain ⟨hs₁, hv₁, hχ₁⟩ := CellU.immOf_inj f₁
      obtain ⟨hs₂, -, -⟩ := CellU.immOf_inj f₂
      subst hs₁; subst hv₁; subst hχ₁; subst hs₂
      exact ⟨k₃, f₃⟩
  | mutMut p q w τ hp hq P Q hP hQ => exact absurd e₁.symm CellU.immOf_ne_mutOf
  | mutOwn p w τ hp P hP => exact absurd e₁.symm CellU.immOf_ne_mutOf
  | ownMut p w τ hp P hP => exact absurd e₁ CellU.ownOf_ne_immOf
  | immOwn s w τ hh => exact absurd e₂ CellU.ownOf_ne_immOf
  | ownImm s w τ hh => exact absurd e₁ CellU.ownOf_ne_immOf
  | immMut s w τ hh p hp P hP => exact absurd e₂.symm CellU.immOf_ne_mutOf
  | mutImm s w τ hh p hp P hP => exact absurd e₁.symm CellU.immOf_ne_mutOf

end BoCa.Fig16

namespace BoCa.Fig16
variable {Loc Val : Type}
variable {Loc Val : Type}

/-- `σ` and `K` agree away from `ℓ` when `σ = ℓ ↦ ψ ● K`. -/
theorem ResU.compS_single_get_ne {l l' : Loc} {ψ : CellU Loc Val}
    {K σ : ResU Loc Val} (h : ResU.CompS (ResU.single l ψ) K σ) (hne : l' ≠ l) :
    σ.get l' = K.get l' := by
  rcases ResU.Comp.get h l' with ⟨e₁, e₂, e⟩ | ⟨ζ, e₁, e₂, e⟩ | ⟨ζ, e₁, e₂, e⟩ |
      ⟨ζ₁, ζ₂, ζ, e₁, e₂, e, -⟩
  · rw [e, e₂]
  · rw [ResU.single_get_ne ψ hne] at e₁; exact absurd e₁ (by simp)
  · rw [e, e₂]
  · rw [ResU.single_get_ne ψ hne] at e₁; exact absurd e₁ (by simp)

/-- At `ℓ`, `σ = ℓ ↦ ψ ● K` carries `ψ` and `K` is undefined. -/
theorem ResU.compS_single_get_self {l : Loc} {ψ : CellU Loc Val}
    {K σ : ResU Loc Val} (h : ResU.CompS (ResU.single l ψ) K σ)
    (hn : K.get l = none) : σ.get l = some ψ := by
  rcases ResU.Comp.get h l with ⟨e₁, -, -⟩ | ⟨ζ, e₁, -, e⟩ | ⟨ζ, -, e₂, -⟩ |
      ⟨ζ₁, ζ₂, ζ, -, e₂, -, -⟩
  · exact absurd (e₁.symm.trans (ResU.single_get_self l ψ)) (by simp)
  · rw [e, ← ResU.single_get_self l ψ, e₁]
  · exact absurd (hn.symm.trans e₂) (by simp)
  · exact absurd (hn.symm.trans e₂) (by simp)

/-- The `own` normal form, `[TR]` 6.39's first display, lines 2–4:

```
⦇ρ ● ℓ↦own(v) ● ρ_v⦈ = ex(ρ)_● ● ex(ℓ↦own(v))_● ● ex(ρ_v)_●
                        ● (ag(ρ) ○ ag(ℓ↦own(v)) ○ ag(ρ_v))
                     = ℓ↦own(v) ● ex(ρ)_● ● ex(ρ_v)_● ● (ag(ρ) ○ ag(ρ_v))
```

`[about ours: `[TR]` 6.39's first display, as a graph — G4]` -/
theorem ResU.flat_own_normal {l : Loc} {v : Val} {ρ ρv ov w σ : ResU Loc Val}
    (hov : ResU.CompS (ResU.single l (CellU.ownOf v)) ρv ov)
    (hw : ResU.CompS ρ ov w) (hflat : ResU.Flat w σ) :
    ∃ e₁ e₂ EX a₁ a₂ AG K,
      ExS ρ e₁ ∧ ExS ρv e₂ ∧ ResU.CompS e₁ e₂ EX ∧
      AgW ρ a₁ ∧ AgW ρv a₂ ∧ ResU.CompR a₁ a₂ AG ∧
      ResU.CompS EX AG K ∧
      ResU.CompS (ResU.single l (CellU.ownOf v)) K σ := by
  obtain ⟨e₁, e₂', e, a₁, a₂', a, he₁, he₂', hec, ha₁, ha₂', hac, hσ⟩ :=
    (ResU.Flat.split hw).mp hflat
  obtain ⟨f₁, f₂, hf₁, hf₂, hfc⟩ := (ExS.split hov).mp he₂'
  obtain ⟨g₁, g₂, hg₁, hg₂, hgc⟩ := (AgW.split hov).mp ha₂'
  rw [ExS.functional hf₁ (ExW.single_own l v)] at hfc
  rw [AgW.functional hg₁ (AgW.single_own l v)] at hgc
  rw [ResU.CompR.functional hgc (ResU.comp_empty_left g₂)] at hac
  obtain ⟨y, hy₁, hy₂⟩ :=
    (ResU.CompS.assoc e₁ (ResU.single l (CellU.ownOf v)) f₂ e).mp ⟨_, hfc, hec⟩
  obtain ⟨EX, hEX, hle⟩ :=
    (ResU.CompS.assoc (ResU.single l (CellU.ownOf v)) e₁ f₂ e).mpr
      ⟨y, ResU.CompS.comm hy₁, hy₂⟩
  obtain ⟨K, hK, hKσ⟩ :=
    (ResU.CompS.assoc (ResU.single l (CellU.ownOf v)) EX a σ).mpr ⟨e, hle, hσ⟩
  exact ⟨e₁, f₂, EX, a₁, g₂, a, K, he₁, hf₂, hEX, ha₁, hg₂, hac, hK, hKσ⟩

/-- `ag` at a singleton `imm` cell, forwards.
`[about ours: `ag`'s printed row evaluated at one `imm` cell]` -/
theorem AgW.single_imm {l : Loc} {s : LSet} {v : Val} {χ p σ : ResU Loc Val}
    {hstr : χ.InStratum s.join} (hp : ResU.FlatR χ p)
    (hσ : ResU.CompR (ResU.single l (CellU.immOf s v χ hstr)) p σ) :
    AgW (ResU.single l (CellU.immOf s v χ hstr)) σ := by
  obtain ⟨a, e, ha, he, hae⟩ := hp
  have hk : (CellU.immOf s v χ hstr).kind = Kind.imm := CellU.kind_immOf _ _ _ _
  refine AgW.mk (wm := []) (wi := [(l, p)])
    (a := ResU.single l (CellU.immOf s v χ hstr)) (bm := PMap.empty) (bi := p)
    (ResU.sites_single_other (by rw [hk]; exact fun c => Kind.noConfusion c))
    (ResU.sites_single_self hk) AgWitsM.nil ?_ BigComp.nil (BigComp.single p) ?_ hσ
  · refine AgWitsI.cons (CellU.immOf s v χ hstr) (ResU.single_get_self _ _) hk e a
      ?_ ?_ (ResU.CompR.comm hae) AgWitsI.nil
    · rwa [CellU.wit_immOf]
    · rwa [CellU.wit_immOf]
  · rw [ResU.restrict_single_self hk]
    exact ResU.comp_empty_right _

/-- The four walks of `ρ` and `ρ_v` are undefined at `ℓ`: `[TR]` Lemma 6.34's
*"Unfolding these, we have `ℓ ∉ dom(⦇ρ ● ρ_v⦈)`"*.
`[about ours: the step `[TR]` Lemma 6.34's proof reads off the printed `#`, at
the walks; `[TR]` Lemma 6.29's proof reads the same one]` -/
theorem ResU.walks_none_of_hash_own {l : Loc} {v : Val}
    {ρ ρv W e a ev av : ResU Loc Val}
    (hW : ResU.CompS ρv (ResU.single l (CellU.ownOf v)) W) (hh : ResU.Hash ρ W)
    (he : ExS ρ e) (ha : AgW ρ a) (hev : ExS ρv ev) (hav : AgW ρv av) :
    e.get l = none ∧ a.get l = none ∧ ev.get l = none ∧ av.get l = none := by
  obtain ⟨-, T, hT, σT, eT, aT, hexT, hagT, hcT⟩ := hh
  obtain ⟨e₁, e₂, he₁, he₂, hec⟩ := (ExS.split hT).mp hexT
  obtain ⟨a₁, a₂, ha₁, ha₂, hac⟩ := (AgW.split hT).mp hagT
  obtain ⟨f₁, f₂, hf₁, hf₂, hfc⟩ := (ExS.split hW).mp he₂
  obtain ⟨b₁, b₂, hb₁, hb₂, hbc⟩ := (AgW.split hW).mp ha₂
  cases ExS.functional he₁ he
  cases AgW.functional ha₁ ha
  cases ExS.functional hf₁ hev
  cases AgW.functional hb₁ hav
  have hownk : (CellU.ownOf (Loc := Loc) v).kind ≠ Kind.imm := by simp
  have hf₂l : f₂.get l = some (CellU.ownOf v) := by
    rw [ExS.functional hf₂ (ExW.single_own l v)]
    exact ResU.single_get_self _ _
  have hevl : ev.get l = none :=
    ResU.CompatS.right_eq_none (ResU.CompatS.symm hfc.1) hf₂l hownk
  have he₂l : e₂.get l = some (CellU.ownOf v) := by
    have := hfc.2 l; rw [hevl, hf₂l] at this; exact this
  have hel : e.get l = none :=
    ResU.CompatS.right_eq_none (ResU.CompatS.symm hec.1) he₂l hownk
  have heTl : eT.get l = some (CellU.ownOf v) := by
    have := hec.2 l; rw [hel, he₂l] at this; exact this
  have haTl : aT.get l = none :=
    ResU.CompatS.right_eq_none hcT.1 heTl hownk
  have hal : a.get l = none := ((ResU.Comp.eq_none_iff hac l).mp haTl).1
  have ha₂l : a₂.get l = none := ((ResU.Comp.eq_none_iff hac l).mp haTl).2
  exact ⟨hel, hal, hevl, ((ResU.Comp.eq_none_iff hbc l).mp ha₂l).1⟩

end BoCa.Fig16

namespace BoCa.Fig16
variable {Loc Val : Type}

/-- `[TR]` Lemma 6.38 (p. 12), as a proposition.
`[as printed]` (the `●`s as graphs, G4; the conclusion's `ρ′ ● ρ⁺/ℓ` asserted to
exist) -/
def ResU.SixThirtyEight : Prop :=
  ∀ {α : Life} {l : BoCa.Loc} {v : BoCa.Val}
    {ρ ρv ρ' ρp W ρρi ρ'ρp : ResU BoCa.Loc BoCa.Val}
    {hv : ρv.InStratum (LSet.singleton α).join},
    ResU.CompS ρv (ResU.single l (CellU.ownOf v)) W →
    ResU.Hash ρ W →
    ResU.Hash ρ' ρp →
    ρ.InStratum α →
    ρ'.InStratum α →
    ρp.restrict Kind.own = PMap.empty →
    ResU.CompS ρ (ResU.single l (CellU.immOf (LSet.singleton α) v ρv hv)) ρρi →
    ResU.CompS ρ' ρp ρ'ρp →
    ResU.UpdV ρρi ρ'ρp →
    ∃ G, ResU.CompS ρ' (ρp.del l) G ∧ ResU.Hash G W

/-- `[TR]` Lemma 6.38's step 2, *"By H4 and H7"*, the half about `ρ′`:
`ℓ ∉ dom(ρ′)`.
`[about ours: the step `[TR]` Lemma 6.38's proof takes at "By H4 and H7"]` -/
theorem ResU.six38_no_borrow_in_frame {α : Life} {l : BoCa.Loc} {v : BoCa.Val}
    {ρv ρ' ρp ρ'ρp : ResU BoCa.Loc BoCa.Val}
    {hv : ρv.InStratum (LSet.singleton α).join}
    (h4 : ρ'.InStratum α) (hpp : ResU.CompS ρ' ρp ρ'ρp)
    (hcl : ρ'ρp.get l = some (CellU.immOf (LSet.singleton α) v ρv hv)) :
    ρ'.get l = none := by
  classical
  have key : ∀ (s : LSet) (w : BoCa.Val) (χ : ResU BoCa.Loc BoCa.Val)
      (hc : χ.InStratum s.join),
      (CellU.immOf s w χ hc).InStratum α → s.mem α → False := by
    intro s w χ hc hin hmem
    exact absurd (s.meet_least α hmem)
      (not_le_of_gt ((CellU.inStratum_immOf α s w χ hc).mp hin))
  cases hg : ρ'.get l with
  | none => rfl
  | some φ =>
      exfalso
      have hφα : φ.InStratum α := h4 l φ hg
      rcases ResU.Comp.get hpp l with ⟨e₁, -, -⟩ | ⟨ψ, e₁, -, e⟩ |
          ⟨ψ, e₁, -, -⟩ | ⟨ψ₁, ψ₂, ψ, e₁, -, e, hC⟩
      · rw [hg] at e₁; exact absurd e₁ (by simp)
      · rw [hg] at e₁
        cases Option.some.inj e₁
        have hφ : φ = CellU.immOf (LSet.singleton α) v ρv hv :=
          Option.some.inj (e.symm.trans hcl)
        subst hφ
        exact key _ v ρv hv hφα rfl
      · rw [hg] at e₁; exact absurd e₁ (by simp)
      · rw [hg] at e₁
        cases Option.some.inj e₁
        obtain ⟨s₁, s₂, w, χ, k₁, k₂, k₃, f₁, f₂, f₃⟩ := hC
        subst f₁
        obtain ⟨hs, -, -⟩ :=
          CellU.immOf_inj (Option.some.inj ((f₃ ▸ e).symm.trans hcl))
        have hjoin : s₁.join = α := by
          have hm : (s₁.union s₂).mem s₁.join := Or.inl s₁.join_mem
          rw [hs] at hm; exact hm
        exact key _ w χ k₁ hφα (hjoin ▸ s₁.join_mem)

/-- `[TR]` Lemma 6.38 from its third sentence on: the printed hypotheses still in
use, what the first two sentences deliver, and the printed conclusion.
`[about ours: `[TR]` Lemma 6.38's proof from "Then in order to show G1" on]` -/
def ResU.SixThirtyEightResidual : Prop :=
  ∀ {α : Life} {l : BoCa.Loc} {v : BoCa.Val}
    {ρ ρv ρ' ρp W ρρi ρ'ρp G : ResU BoCa.Loc BoCa.Val}
    {hv : ρv.InStratum (LSet.singleton α).join},
    ResU.CompS ρv (ResU.single l (CellU.ownOf v)) W →
    ResU.Hash ρ W →
    ρ.InStratum α →
    ρ'.InStratum α →
    ρp.restrict Kind.own = PMap.empty →
    ResU.CompS ρ (ResU.single l (CellU.immOf (LSet.singleton α) v ρv hv)) ρρi →
    ResU.CompS ρ' ρp ρ'ρp →
    ResU.UpdV ρρi ρ'ρp →
    ResU.CompS ρ' (ρp.del l) G →
    ResU.Hash G (ResU.single l (CellU.immOf (LSet.singleton α) v ρv hv)) →
    ResU.CompS G (ResU.single l (CellU.immOf (LSet.singleton α) v ρv hv)) ρ'ρp →
    ResU.Hash G W

end BoCa.Fig16

namespace BoCa.Fig16
variable {Loc Val : Type}
variable {Loc Val : Type}

/-- `ρ ◐ ∅ = σ` determines `σ`, at any cell-level operation.
`[about ours: the schema-level converse of `[TR]` 6.4, for the walks,
whose operator is a parameter]` -/
theorem ResU.eq_of_comp_empty_right {R : CellU Loc Val → CellU Loc Val → Prop}
    {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop} {ρ σ : ResU Loc Val}
    (h : ResU.Comp R C ρ PMap.empty σ) : ρ = σ := by
  refine PMap.ext fun l => ?_
  have hl := h.2 l
  have he : (PMap.empty : ResU Loc Val).get l = none := rfl
  rw [he] at hl
  cases e : ρ.get l with
  | none => rw [e] at hl; exact (show σ.get l = none from hl).symm
  | some ψ => rw [e] at hl; exact (show σ.get l = some ψ from hl).symm

/-- `∅ ◐ ρ = σ` determines `σ`.
`[about ours: the schema-level converse of `[TR]` 6.4, for the walks]` -/
theorem ResU.eq_of_comp_empty_left {R : CellU Loc Val → CellU Loc Val → Prop}
    {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop} {ρ σ : ResU Loc Val}
    (h : ResU.Comp R C PMap.empty ρ σ) : ρ = σ := by
  refine PMap.ext fun l => ?_
  have hl := h.2 l
  have he : (PMap.empty : ResU Loc Val).get l = none := rfl
  rw [he] at hl
  cases e : ρ.get l with
  | none => rw [e] at hl; exact (show σ.get l = none from hl).symm
  | some ψ => rw [e] at hl; exact (show σ.get l = some ψ from hl).symm

/-- `ex` at a singleton `mut` cell, read backwards: the cell composed with the
witness's walk.
`[about ours: `ex`'s printed row evaluated at one `mut` cell]` -/
theorem ExW.single_mut_inv {R : CellU Loc Val → CellU Loc Val → Prop}
    {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop}
    {l : Loc} {b : Life} {v : Val} {χ : ResU Loc Val} {hstr : ResU.InStratum b χ}
    {P : Val → SPropS Loc Val b} {hw : P v ⟨χ, hstr⟩} {σ : ResU Loc Val}
    (h : ExW R C (ResU.single l (CellU.mutOf b v χ hstr P hw)) σ) :
    ∃ e, ExW R C χ e ∧
      ResU.Comp R C (ResU.single l (CellU.mutOf b v χ hstr P hw)) e σ := by
  have hk : (CellU.mutOf b v χ hstr P hw).kind = Kind.mut :=
    CellU.kind_mutOf _ _ _ _ _ _
  cases h with
  | mk hs hwts hb hnm hσ =>
      rename_i nm bb w
      have hfst : w.map Prod.fst = [l] := by
        refine ResU.sites_singleton_of hs (fun x => ⟨?_, ?_⟩)
        · rintro ⟨ψ, hg, -⟩
          exact (ResU.single_get_eq_some hg).1
        · rintro rfl
          exact ⟨_, ResU.single_get_self _ _, hk⟩
      cases w with
      | nil => simp at hfst
      | cons q t =>
          obtain ⟨x, e⟩ := q
          simp only [List.map_cons, List.cons.injEq] at hfst
          obtain ⟨-, ht⟩ := hfst
          obtain rfl : t = [] := by
            cases t with
            | nil => rfl
            | cons c t' => simp at ht
          cases hwts with
          | cons ψ hψ hkψ he hwts' =>
              obtain ⟨-, rfl⟩ := ResU.single_get_eq_some hψ
              rw [CellU.wit_mutOf] at he
              have hbe : e = bb := by
                cases hb with
                | cons hnil hcomp =>
                    rename_i τ
                    obtain rfl : τ = (PMap.empty : ResU Loc Val) := BigComp.nil_inv hnil
                    exact ResU.eq_of_comp_empty_right hcomp
              rw [ResU.restrict_single_other (k := Kind.own)
                    (by rw [hk]; exact fun c => Kind.noConfusion c),
                  ResU.restrict_single_self hk] at hnm
              have hnmeq := ResU.eq_of_comp_empty_left hnm
              refine ⟨e, he, ?_⟩
              rw [hnmeq, hbe]
              exact hσ

/-- `ag` at a singleton `mut` cell, read backwards: the witness's own `ag`.
`[about ours: `ag`'s printed row evaluated at one `mut` cell]` -/
theorem AgW.single_mut_inv {l : Loc} {b : Life} {v : Val} {χ : ResU Loc Val}
    {hstr : ResU.InStratum b χ} {P : Val → SPropS Loc Val b} {hw : P v ⟨χ, hstr⟩}
    {σ : ResU Loc Val}
    (h : AgW (ResU.single l (CellU.mutOf b v χ hstr P hw)) σ) : AgW χ σ := by
  have hk : (CellU.mutOf b v χ hstr P hw).kind = Kind.mut :=
    CellU.kind_mutOf _ _ _ _ _ _
  cases h with
  | mk hsm hsi hwm hwi hbm hbi ha hσ =>
      rename_i a bm bi wm wi
      obtain rfl : wi = [] := by
        have hnil : wi.map Prod.fst = [] :=
          ResU.sites_nil_of_none hsi (by
            intro m ψ hg
            obtain ⟨-, rfl⟩ := ResU.single_get_eq_some hg
            rw [hk]; exact fun c => Kind.noConfusion c)
        cases wi with
        | nil => rfl
        | cons q t => simp at hnil
      obtain rfl : bi = (PMap.empty : ResU Loc Val) := BigComp.nil_inv hbi
      have hfst : wm.map Prod.fst = [l] := by
        refine ResU.sites_singleton_of hsm (fun x => ⟨?_, ?_⟩)
        · rintro ⟨ψ, hg, -⟩
          exact (ResU.single_get_eq_some hg).1
        · rintro rfl
          exact ⟨_, ResU.single_get_self _ _, hk⟩
      cases wm with
      | nil => simp at hfst
      | cons q t =>
          obtain ⟨x, am⟩ := q
          simp only [List.map_cons, List.cons.injEq] at hfst
          obtain ⟨-, ht⟩ := hfst
          obtain rfl : t = [] := by
            cases t with
            | nil => rfl
            | cons c t' => simp at ht
          cases hwm with
          | cons ψ hψ hkψ hag hwm' =>
              obtain ⟨-, rfl⟩ := ResU.single_get_eq_some hψ
              rw [CellU.wit_mutOf] at hag
              have hbe : am = bm := by
                cases hbm with
                | cons hnil hcomp =>
                    rename_i τ
                    obtain rfl : τ = (PMap.empty : ResU Loc Val) := BigComp.nil_inv hnil
                    exact ResU.eq_of_comp_empty_right hcomp
              rw [ResU.restrict_single_other (k := Kind.imm)
                    (by rw [hk]; exact fun c => Kind.noConfusion c)] at ha
              have haeq := ResU.eq_of_comp_empty_left ha
              have hσeq := ResU.eq_of_comp_empty_right hσ
              rw [← hσeq, ← haeq, ← hbe]
              exact hag

/-- Two resources that agree off `ℓ` and carry an exclusive cell at `ℓ` have
the same `▸◂` partners: `[TR]` 6.22's *"Since `ρ_o` contains a single `own`
cell, this composite is well-defined if and only if the same composite is defined
when `ρ_o` is replaced by `ρ_m`"*, which 6.23's proof reuses.
`[about ours: the sentence `[TR]` 6.22 and 6.23 close on, as a lemma]` -/
theorem ResU.compatS_congr_of_excl {l : Loc} {s s' A : ResU Loc Val}
    (hoff : ∀ x, x ≠ l → s'.get x = s.get x)
    {ψ : CellU Loc Val} (hg : s.get l = some ψ) (hk : ψ.kind ≠ Kind.imm)
    (hc : ResU.CompatS s A) : ResU.CompatS s' A := by
  intro x χ₁ χ₂ e₁ e₂
  by_cases hx : x = l
  · subst hx
    rw [ResU.CompatS.right_eq_none hc hg hk] at e₂
    exact absurd e₂ (by simp)
  · exact hc x χ₁ χ₂ (by rw [← hoff x hx]; exact e₁) e₂

/-- Two composites over the same left operand agree wherever their right
operands do. -/
theorem ResU.compS_agree_off_right {l : Loc} {ρ₁ ρ₂ ρ₂' ρ ρ' : ResU Loc Val}
    (h : ResU.CompS ρ₁ ρ₂ ρ) (h' : ResU.CompS ρ₁ ρ₂' ρ')
    (hoff : ∀ x, x ≠ l → ρ₂'.get x = ρ₂.get x) :
    ∀ x, x ≠ l → ρ'.get x = ρ.get x := by
  intro x hx
  have h1 := h.2 x
  have h2 := h'.2 x
  rw [hoff x hx] at h2
  cases e₁ : ρ₁.get x <;> cases e₂ : ρ₂.get x <;> rw [e₁, e₂] at h1 h2
  · rw [h1, h2]
  · rw [h1, h2]
  · rw [h1, h2]
  · obtain ⟨ψa, ha, hCa⟩ := h1
    obtain ⟨ψb, hb, hCb⟩ := h2
    rw [ha, hb, CellU.CompS.functional hCa hCb]

/-- `ex` at a singleton `mut` cell, forwards.
`[about ours: `ex`'s printed row evaluated at one `mut` cell]` -/
theorem ExW.single_mut {R : CellU Loc Val → CellU Loc Val → Prop}
    {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop}
    {l : Loc} {b : Life} {v : Val} {χ : ResU Loc Val} {hstr : ResU.InStratum b χ}
    {P : Val → SPropS Loc Val b} {hw : P v ⟨χ, hstr⟩} {e σ : ResU Loc Val}
    (he : ExW R C χ e)
    (hσ : ResU.Comp R C (ResU.single l (CellU.mutOf b v χ hstr P hw)) e σ) :
    ExW R C (ResU.single l (CellU.mutOf b v χ hstr P hw)) σ := by
  have hk : (CellU.mutOf b v χ hstr P hw).kind = Kind.mut :=
    CellU.kind_mutOf _ _ _ _ _ _
  refine ExW.mk (w := [(l, e)]) (b := e)
    (nm := ResU.single l (CellU.mutOf b v χ hstr P hw))
    (ResU.sites_single_self hk) ?_ (BigComp.single e) ?_ hσ
  · exact ExWits.cons (CellU.mutOf b v χ hstr P hw) (ResU.single_get_self _ _) hk
      (by rwa [CellU.wit_mutOf]) ExWits.nil
  · rw [ResU.restrict_single_other (k := Kind.own)
        (by rw [hk]; exact fun c => Kind.noConfusion c),
      ResU.restrict_single_self hk]
    exact ResU.comp_empty_left _

/-- `ag` at a singleton `mut` cell, forwards.
`[about ours: `ag`'s printed row evaluated at one `mut` cell]` -/
theorem AgW.single_mut {l : Loc} {b : Life} {v : Val} {χ : ResU Loc Val}
    {hstr : ResU.InStratum b χ} {P : Val → SPropS Loc Val b} {hw : P v ⟨χ, hstr⟩}
    {a : ResU Loc Val} (ha : AgW χ a) :
    AgW (ResU.single l (CellU.mutOf b v χ hstr P hw)) a := by
  have hk : (CellU.mutOf b v χ hstr P hw).kind = Kind.mut :=
    CellU.kind_mutOf _ _ _ _ _ _
  refine AgW.mk (wm := [(l, a)]) (wi := []) (a := a) (bm := a) (bi := PMap.empty)
    (ResU.sites_single_self hk)
    (ResU.sites_single_other (by rw [hk]; exact fun c => Kind.noConfusion c))
    ?_ AgWitsI.nil (BigComp.single a) BigComp.nil ?_ (ResU.comp_empty_right _)
  · exact AgWitsM.cons (CellU.mutOf b v χ hstr P hw) (ResU.single_get_self _ _) hk
      (by rwa [CellU.wit_mutOf]) AgWitsM.nil
  · rw [ResU.restrict_single_other (k := Kind.imm)
        (by rw [hk]; exact fun c => Kind.noConfusion c)]
    exact ResU.comp_empty_left _

end BoCa.Fig16

namespace BoCa.Fig16
variable {Loc Val : Type}

/-- `↭` keeps the stratum.
`[about ours: `[TR]` Lemma 6.50 read as a statement about `Res_α`]` -/
theorem ResU.updV_inStratum {ρ ρ' : ResU BoCa.Loc BoCa.Val} {α : Life}
    (hd : ρ.InStratum α) (hu : ResU.UpdV ρ ρ') : ρ'.InStratum α := by
  obtain ⟨σ, hσ⟩ := hu.2.1
  obtain ⟨σ', hσ'⟩ := hu.2.2
  have hσα : σ.InStratum α := BoLo.flat_inStratum hσ hd
  refine BoLo.flat_inStratum_inv hσ' ?_
  intro m χ hχ
  rcases CellU.rep χ with ⟨w, rfl⟩ | ⟨s, w, ξ, hξ, rfl⟩ | ⟨b, w, ξ, hξ, P, hP, rfl⟩
  · exact trivial
  · obtain ⟨τ, hτ, hgg⟩ := (hu.1.1 m s w ξ hξ).mpr ⟨σ', hσ', hχ⟩
    cases ResU.Flat.functional hτ hσ
    exact hσα m _ hgg
  · obtain ⟨w₀, ξ₀, hξ₀, hP₀, τ, hτ, hgg⟩ :=
      (hu.1.2 m b P).mpr ⟨w, ξ, hξ, hP, ⟨σ', hσ', hχ⟩⟩
    cases ResU.Flat.functional hτ hσ
    exact (hσα m _ hgg : b ⊐ α)

/-- An `own` or a `mut` cell sits in its own flattening unchanged.  `[about ours:
the step `[TR]` 6.27's proof reads off `⦇−⦈` at an exclusive cell]` -/
theorem ResU.flat_get_of_ne_imm {Loc Val : Type} {ρ σ : ResU Loc Val}
    (h : ρ.Flat σ) {l : Loc} {ψ : CellU Loc Val}
    (hg : ρ.get l = some ψ) (hk : ψ.kind ≠ Kind.imm) : σ.get l = some ψ := by
  obtain ⟨e, a, he, ha, hc⟩ := h
  exact (ResU.CompS.get_left_of_ne_imm hc (ExS.get_of_ne_imm he hg hk) hk).2

end BoCa.Fig16

end
