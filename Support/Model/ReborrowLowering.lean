import Paper.S5_Model.Definitions
import Paper.S6_1_StandardLemmas.Lemmas
import Support.Model.Algebra
import Support.Model.AlgebraInstances
import Support.Model.Ancestors
import Support.Model.Cells
import Support.Model.Compatibility
import Support.Model.Composition
import Support.Model.FlatteningCells
import Support.Model.Lifetimes
import Support.Model.Prelude
import Support.Model.Reborrow
import Support.Model.ReborrowFrame
import Support.Model.Restriction
import Support.Model.Singletons
import Support.Model.WalkSplitting
import Support.Model.Walks

/-!
# Support — Model — ReborrowLowering

`[about ours]`.  The steps of Lemmas 6.56–6.58: absorption at `○` and the domains of reborrows.
-/

noncomputable section

namespace BoCa.Fig16
variable {Loc Val : Type}

/-- A `○`-factor absorbs: `X ○ (X ○ Y) = X ○ Y`.
`[about ours: `[TR]` 6.3 and 6.19 at `○`, in the form `[TR]` 6.57's display
uses them]` -/
theorem ResU.CompR.absorb {X Y Z : ResU Loc Val} (h : ResU.CompR X Y Z) :
    ResU.CompR X Z Z := by
  have hR : ∀ ψ₁ ψ₂ ψ : CellU Loc Val, CellU.CompR ψ₁ ψ₂ ψ → CellU.CompatR ψ₁ ψ₂ :=
    fun _ _ ψ hc => ⟨ψ, hc⟩
  obtain ⟨χ, hχ, hZ⟩ :=
    (ResU.CompR.assoc X X Y Z).mpr ⟨X, ResU.compR_self X, h⟩
  rwa [ResU.CompR.functional hχ h] at hZ

/-- `ρ ≼ σ` gives `ρ ○ σ = σ`. -/
theorem ResU.LeR.absorb {ρ σ : ResU Loc Val} (h : ResU.LeR ρ σ) :
    ResU.CompR ρ σ σ := ResU.CompR.absorb h.choose_spec

/-- If two operands both absorb `Z`, so does their `○` composite. -/
theorem ResU.CompR.absorb_comp {X Y W Z : ResU Loc Val} (h : ResU.CompR X Y W)
    (hX : ResU.CompR X Z Z) (hY : ResU.CompR Y Z Z) : ResU.CompR W Z Z := by
  obtain ⟨y, hy, hw⟩ := (ResU.CompR.assoc X Y Z Z).mp ⟨Z, hY, hX⟩
  rwa [ResU.CompR.functional hy h] at hw

/-- The same along `⨀`. -/
theorem BigComp.absorb {Z : ResU Loc Val} :
    ∀ {L : List (ResU Loc Val)} {b : ResU Loc Val},
      BigComp CellU.CompatR CellU.CompR L b →
        (∀ τ ∈ L, ResU.CompR τ Z Z) → ResU.CompR b Z Z := by
  intro L
  induction L with
  | nil => intro b h _; cases h; exact ResU.CompR.comm (ResU.comp_empty_right Z)
  | cons x L₀ ih =>
      intro b h hs
      cases h with
      | cons hrest hcx =>
          exact ResU.CompR.absorb_comp hcx (hs x List.mem_cons_self)
            (ih hrest (fun τ hm => hs τ (List.mem_cons_of_mem _ hm)))

/-- A location of `ρ|dom(σ)` is a location of `σ`. -/
theorem ResU.restrictDom_dom {ρ σ : ResU Loc Val} {l : Loc} {ζ : CellU Loc Val}
    (h : (ρ.restrictDom σ).get l = some ζ) : ∃ φ, σ.get l = some φ := by
  cases e : σ.get l with
  | none => rw [ResU.restrictDom_get_of_none e] at h; exact absurd h (by simp)
  | some φ => exact ⟨φ, rfl⟩

/-- `imm(t̄, v, χ) ○ imm(s̄, v, χ) = imm(s̄, v, χ)` when `t̄ ⊆ s̄`. -/
theorem CellU.compR_imm_sub {s t : LSet} {v : Val} {χ : ResU Loc Val}
    {hs : χ.InStratum s.join} {ht : χ.InStratum t.join}
    (hts : ∀ x, t.mem x → s.mem x) :
    CellU.CompR (CellU.immOf t v χ ht) (CellU.immOf s v χ hs) (CellU.immOf s v χ hs) := by
  have hc : CellU.CompatS (CellU.immOf t v χ ht) (CellU.immOf s v χ hs) :=
    CellU.compatS_iff.mpr ⟨by simp, by simp, by simp, by simp⟩
  have e : t ∪ s = s := LSet.ext fun x => ⟨fun h => h.elim (hts x) id, Or.inr⟩
  have h₃ : χ.InStratum (t ∪ s).join := by rw [e]; exact hs
  have := CellU.CompR.strict hc
  rw [CellU.compS_immOf hc h₃] at this
  have e' : CellU.immOf (t ∪ s) v χ h₃ = CellU.immOf s v χ hs := by
    clear this; revert h₃; rw [e]; intro h₃; rfl
  rwa [e'] at this

/-- `ρ|dom(ρ′|imm) ≤ ρ′|imm`, at `○`.
`[about ours: `[TR]` 6.57's *"by unfolding reb, we have that
`ρ|dom(ρ′ᵢ|imm) ≤ ρ′ᵢ|imm`"* (p. 18), at `○`]` -/
theorem ResU.restrictDom_compR_restrict {β : Life} {ρ' ρ : ResU Loc Val}
    (hreb : ResU.Reb β ρ' ρ) (k : Kind) :
    ResU.CompR ((ρ.restrictDom (ρ'.restrict Kind.imm)).restrict k)
      (ρ'.restrict Kind.imm) (ρ'.restrict Kind.imm) := by
  have hcell : ∀ l ζ,
      ((ρ.restrictDom (ρ'.restrict Kind.imm)).restrict k).get l = some ζ →
      ∃ φ, (ρ'.restrict Kind.imm).get l = some φ ∧ CellU.CompR ζ φ φ := by
    intro l ζ he
    obtain ⟨hD, -⟩ := ResU.restrict_eq_some.mp he
    obtain ⟨φ, hφ⟩ := ResU.restrictDom_dom hD
    obtain ⟨hφ', hφk⟩ := ResU.restrict_eq_some.mp hφ
    have hρ : ρ.get l = some ζ := ResU.restrictDom_get_inv hD
    refine ⟨φ, hφ, ?_⟩
    rcases CellU.rep φ with ⟨w, rfl⟩ | ⟨s, w, χ, hs, rfl⟩ | ⟨b, w, χ, hb, P, hw, rfl⟩
    · exact absurd hφk (by simp)
    · obtain ⟨t, ht, hts, rfl⟩ := ResU.reb_imm_cell_sub hreb hρ hφ'
      exact CellU.compR_imm_sub hts
    · exact absurd hφk (by simp)
  refine ⟨fun l ζ₁ ζ₂ e₁ e₂ => ?_, fun l => ?_⟩
  · obtain ⟨φ, hφ, hC⟩ := hcell l ζ₁ e₁
    rw [hφ] at e₂
    obtain rfl := Option.some.inj e₂
    exact ⟨_, hC⟩
  · cases e : ((ρ.restrictDom (ρ'.restrict Kind.imm)).restrict k).get l with
    | none =>
        cases hf : (ρ'.restrict Kind.imm).get l with
        | none => rfl
        | some φ => rfl
    | some ζ =>
        obtain ⟨φ, hφ, hC⟩ := hcell l ζ e
        rw [hφ]
        exact ⟨φ, rfl, hC⟩

/-- `ag(ρ|dom(ρ′ᵢ|imm))` absorbs `ag(ρᵢ)`: `[TR]` 6.57's display at the
aliasable walk, as 6.59's *"it suffices to show `ρ|dom(ρ′ᵢ|imm) ● ρᵢ ● ρ_b ↭ …`"*
uses it.
`[about ours: `[TR]` 6.57's display at `ag`, with `ag(ρ|D)` given]` -/
theorem ResU.reb_immPart_ag_absorbs {β : Life} {ρ'i ρ aD a₂ : ResU Loc Val}
    {l₀ : Loc} {s : LSet} {v : Val} {hs : ρ'i.InStratum s.join}
    (hreb : ResU.Reb β ρ'i ρ)
    (haD : AgW (ρ.restrictDom (ρ'i.restrict Kind.imm)) aD)
    (ha₂ : AgW (ResU.single l₀ (CellU.immOf s v ρ'i hs)) a₂) :
    ResU.CompR aD a₂ a₂ := by
  have hR : ∀ ψ₁ ψ₂ ψ : CellU Loc Val, CellU.CompR ψ₁ ψ₂ ψ → CellU.CompatR ψ₁ ψ₂ :=
    fun _ _ ψ hc => ⟨ψ, hc⟩
  obtain ⟨ev, av, p, hev, hav, hf, hagi⟩ := AgW.single_imm_inv ha₂
  have hchain : ∀ Y : ResU Loc Val, (∃ z, ResU.CompR Y z av) →
      ResU.CompR Y a₂ a₂ := by
    rintro Y ⟨z, hz⟩
    obtain ⟨z₁, hz₁⟩ :=
      ResU.Comp.factor_trans hR ResU.compLawsR hz (ResU.CompR.comm hf)
    obtain ⟨z₂, hz₂⟩ :=
      ResU.Comp.factor_trans hR ResU.compLawsR hz₁ (ResU.CompR.comm hagi)
    exact ResU.CompR.absorb hz₂
  have hfacImm : ∃ z, ResU.CompR (ρ'i.restrict Kind.imm) z av := by
    cases hav with
    | mk hsm' hsi' hwm' hwi' hbm' hbi' ha' hσ' =>
        exact ResU.Comp.factor_trans hR ResU.compLawsR ha' hσ'
  cases haD with
  | mk hsm hsi hwm hwi hbm hbi ha hσ =>
      rename_i aa bm bi wm wi
      have hwmnil : wm = [] := by
        have h0 : wm.map Prod.fst = [] :=
          ResU.sites_nil_of_none hsm (fun m χ hχ => by
            rw [ResU.reb_imm_image hreb (ResU.restrictDom_get_inv hχ)]
            exact fun c => Kind.noConfusion c)
        cases wm with
        | nil => rfl
        | cons q t => simp at h0
      subst hwmnil
      obtain rfl : bm = (PMap.empty : ResU Loc Val) := BigComp.nil_inv hbm
      obtain ⟨z, hz⟩ := hfacImm
      have hDabs : ResU.CompR
          ((ρ.restrictDom (ρ'i.restrict Kind.imm)).restrict Kind.imm) a₂ a₂ :=
        hchain _ (ResU.Comp.factor_trans hR ResU.compLawsR
          (ResU.restrictDom_compR_restrict hreb Kind.imm) hz)
      have haaabs : ResU.CompR aa a₂ a₂ :=
        ResU.CompR.absorb_comp ha hDabs (ResU.CompR.comm (ResU.comp_empty_right a₂))
      have hbiabs : ResU.CompR bi a₂ a₂ := by
        refine BigComp.absorb hbi (fun τ hm => ?_)
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
        obtain ⟨χq, evq, avq, hχq, hexq, hagq, hcq⟩ := AgWitsI.mem hwi q hq
        obtain ⟨φ, hφ⟩ := ResU.restrictDom_dom hχq
        obtain ⟨hφ', hφk⟩ := ResU.restrict_eq_some.mp hφ
        have hρq : ρ.get q.1 = some χq := ResU.restrictDom_get_inv hχq
        obtain ⟨-, -, hkw, -⟩ := ResU.reb_imm_cell_kw hreb hρq hφ' hφk
        rw [hkw] at hexq hagq
        obtain ⟨ev', av', p', z', hex', hag', hc', hz'⟩ := AgW.imm_wit_le hav hφ' hφk
        obtain rfl : ev' = evq := ExR.functional hex' hexq
        obtain rfl : av' = avq := AgW.functional hag' hagq
        obtain rfl : p' = q.2 := ResU.CompR.functional hc' hcq
        exact hchain _ ⟨z', hz'⟩
      exact ResU.CompR.absorb_comp hσ haaabs hbiabs

/-- `ρ = ρ|dom(ρ′|imm) ● ρ|dom(ρ′|mut,own)`, using `[TR]` 6.58's *"note
`dom(ρ) ⊆ dom(ρ′ᵢ)` by unfolding reb"*.
`[about ours: the splitting `[TR]` 6.58's and 6.59's proofs open with]` -/
theorem ResU.restrictDom_split {α : Life} {ρ' ρ : ResU Loc Val}
    (hreb : ResU.Reb α ρ' ρ) :
    ResU.CompS (ρ.restrictDom (ρ'.restrict Kind.imm)) (ρ.restrictDom ρ'.exclPart) ρ := by
  have hcase : ∀ l,
      ((ρ.restrictDom (ρ'.restrict Kind.imm)).get l = ρ.get l ∧
        (ρ.restrictDom ρ'.exclPart).get l = none) ∨
      ((ρ.restrictDom (ρ'.restrict Kind.imm)).get l = none ∧
        (ρ.restrictDom ρ'.exclPart).get l = ρ.get l) := by
    intro l
    cases e : ρ'.get l with
    | none =>
        have hρ : ρ.get l = none := by
          cases f : ρ.get l with
          | none => rfl
          | some ζ =>
              obtain ⟨φ, hφ⟩ := ResU.reb_dom_subset hreb f
              rw [e] at hφ; exact absurd hφ (by simp)
        refine Or.inl ⟨?_, ?_⟩
        · rw [ResU.restrictDom_get_of_none (ResU.restrict_get_none e), hρ]
        · refine ResU.restrictDom_get_of_none ?_
          show (ρ'.get l).bind _ = none
          rw [e]; rfl
    | some φ =>
        by_cases hk : φ.kind = Kind.imm
        · refine Or.inl ⟨ResU.restrictDom_get_of_some (ResU.restrict_get_some e hk), ?_⟩
          refine ResU.restrictDom_get_of_none ?_
          show (ρ'.get l).bind _ = none
          rw [e]
          simp [hk]
        · refine Or.inr ⟨ResU.restrictDom_get_of_none (ResU.restrict_get_ne e hk), ?_⟩
          refine ResU.restrictDom_get_of_some (ResU.restrictOn_eq_some.mpr ⟨e, ?_⟩)
          simp [hk]
  refine ⟨ResU.Compat.of_disjoint (fun l => ?_), fun l => ?_⟩
  · rcases hcase l with ⟨-, h⟩ | ⟨h, -⟩
    · exact Or.inr h
    · exact Or.inl h
  · show OptComp CellU.CompS ((ρ.restrictDom (ρ'.restrict Kind.imm)).get l)
      ((ρ.restrictDom ρ'.exclPart).get l) (ρ.get l)
    rcases hcase l with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> rw [h₁, h₂] <;>
      cases ρ.get l with
      | none => rfl
      | some ζ => rfl

/-- `[TR]` Lemma 6.8 with the hypothesis `⟦ρ₂⟧ = ⟦ρ₃⟧` as a Kleene equality
(`↔` between the two graphs).
`[about ours: `[TR]` 6.8 with its printed hypothesis in the Kleene shape]` -/
theorem ResU.lower_congr_iff {ρ₁ ρ₂ ρ₃ ρ₁₂ ρ₁₃ : ResU Loc Val}
    (heq : ∀ m, ResU.Lower ρ₂ m ↔ ResU.Lower ρ₃ m)
    (h₁₂ : ResU.CompS ρ₁ ρ₂ ρ₁₂) (hh₂ : ResU.Hash ρ₁ ρ₂)
    (h₁₃ : ResU.CompS ρ₁ ρ₃ ρ₁₃) (hh₃ : ResU.Hash ρ₁ ρ₃) :
    ∀ w, ResU.Lower ρ₁₂ w ↔ ResU.Lower ρ₁₃ w := by
  obtain ⟨τ, hτ, hv⟩ := hh₂.2
  obtain ⟨σ₂, hσ₂⟩ := (ResU.Valid.split hτ hv).2
  have hm₂ : ResU.Lower ρ₂ (fun l => (σ₂.get l).map CellU.erase) :=
    ⟨σ₂, hσ₂, fun _ => rfl⟩
  exact fun w => ResU.Lower.congr hm₂ ((heq _).mp hm₂) h₁₂ hh₂ h₁₃ hh₃ (w := w)

end BoCa.Fig16

end
