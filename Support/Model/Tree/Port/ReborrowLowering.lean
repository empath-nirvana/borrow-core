import Support.Model.Tree.Port.ReborrowFrame

/-!
# The printed source over the tree-stratified carrier

`[spec §62]`. `Support/Model/Restriction.lean`, `Support/Model/ReborrowLowering.lean`, read at `CellUT K`, by the printed proofs.
-/

noncomputable section

/-!
# Support — Model — Restriction

`[about ours]`.  `ρ∣dom(σ)` and `ρ/dom(σ)`, the restriction `[TR]` §6 uses and neither document defines.
-/



namespace BoCa.Fig16.Tree
open BoCa.Fig16
variable {Loc Val : Type} {K : WCactus}
theorem ResUT.restrictDom_get_of_some {ρ σ : ResUT Loc Val K} {l : Loc}
    {ζ : CellUT Loc Val K} (h : σ.get l = some ζ) :
    (ρ.restrictDom σ).get l = ρ.get l := by
  show (if (σ.get l).isSome then ρ.get l else none) = ρ.get l
  rw [h]; rfl

theorem ResUT.restrictDom_get_of_none {ρ σ : ResUT Loc Val K} {l : Loc}
    (h : σ.get l = none) : (ρ.restrictDom σ).get l = none := by
  show (if (σ.get l).isSome then ρ.get l else none) = none
  rw [h]; rfl

theorem ResUT.delDom_get_of_some {ρ σ : ResUT Loc Val K} {l : Loc}
    {ζ : CellUT Loc Val K} (h : σ.get l = some ζ) : (ρ.delDom σ).get l = none := by
  show (if (σ.get l).isSome then none else ρ.get l) = none
  rw [h]; rfl

theorem ResUT.delDom_get_of_none {ρ σ : ResUT Loc Val K} {l : Loc}
    (h : σ.get l = none) : (ρ.delDom σ).get l = ρ.get l := by
  show (if (σ.get l).isSome then none else ρ.get l) = ρ.get l
  rw [h]; rfl

/-- A cell of `ρ|dom(σ)` is a cell of `ρ`. -/
theorem ResUT.restrictDom_get_inv {ρ σ : ResUT Loc Val K} {l : Loc} {ζ : CellUT Loc Val K}
    (h : (ρ.restrictDom σ).get l = some ζ) : ρ.get l = some ζ := by
  cases e : σ.get l with
  | none => rw [ResUT.restrictDom_get_of_none e] at h; exact absurd h (by simp)
  | some χ => rw [ResUT.restrictDom_get_of_some e] at h; exact h

/-- `ρ = ρ|dom(σ) ● ρ/dom(σ)`, the splitting `[TR]` 6.56's appeal to 6.11
needs. -/
theorem ResUT.restrictDom_compS (ρ σ : ResUT Loc Val K) :
    ResUT.CompS (ρ.restrictDom σ) (ρ.delDom σ) ρ := by
  refine ⟨ResUT.Compat.of_disjoint (fun l => ?_), fun l => ?_⟩
  · cases e : σ.get l with
    | none => exact Or.inl (ResUT.restrictDom_get_of_none e)
    | some χ => exact Or.inr (ResUT.delDom_get_of_some e)
  · cases e : σ.get l with
    | none =>
        show OptCompT CellUT.CompS ((ρ.restrictDom σ).get l) ((ρ.delDom σ).get l) (ρ.get l)
        rw [ResUT.restrictDom_get_of_none e, ResUT.delDom_get_of_none e]
        cases ρ.get l with
        | none => rfl
        | some χ => rfl
    | some χ =>
        show OptCompT CellUT.CompS ((ρ.restrictDom σ).get l) ((ρ.delDom σ).get l) (ρ.get l)
        rw [ResUT.restrictDom_get_of_some e, ResUT.delDom_get_of_some e]
        cases ρ.get l with
        | none => rfl
        | some ζ => rfl

end BoCa.Fig16.Tree
/-!
# Support — Model — ReborrowLowering

`[about ours]`.  The steps of Lemmas 6.56–6.58: absorption at `○` and the domains of reborrows.
-/



namespace BoCa.Fig16.Tree
open BoCa.Fig16
variable {Loc Val : Type} {K : WCactus}
/-- A `○`-factor absorbs: `X ○ (X ○ Y) = X ○ Y`.
`[about ours: `[TR]` 6.3 and 6.19 at `○`, in the form `[TR]` 6.57's display
uses them]` -/
theorem ResUT.CompR.absorb {X Y Z : ResUT Loc Val K} (h : ResUT.CompR X Y Z) :
    ResUT.CompR X Z Z := by
  have hR : ∀ ψ₁ ψ₂ ψ : CellUT Loc Val K, CellUT.CompR ψ₁ ψ₂ ψ → CellUT.CompatR ψ₁ ψ₂ :=
    fun _ _ ψ hc => ⟨ψ, hc⟩
  obtain ⟨χ, hχ, hZ⟩ :=
    (ResUT.CompR.assoc X X Y Z).mpr ⟨X, ResUT.compR_self X, h⟩
  rwa [ResUT.CompR.functional hχ h] at hZ

/-- `ρ ≼ σ` gives `ρ ○ σ = σ`. -/
theorem ResUT.LeR.absorb {ρ σ : ResUT Loc Val K} (h : ResUT.LeR ρ σ) :
    ResUT.CompR ρ σ σ := ResUT.CompR.absorb h.choose_spec

/-- If two operands both absorb `Z`, so does their `○` composite. -/
theorem ResUT.CompR.absorb_comp {X Y W Z : ResUT Loc Val K} (h : ResUT.CompR X Y W)
    (hX : ResUT.CompR X Z Z) (hY : ResUT.CompR Y Z Z) : ResUT.CompR W Z Z := by
  obtain ⟨y, hy, hw⟩ := (ResUT.CompR.assoc X Y Z Z).mp ⟨Z, hY, hX⟩
  rwa [ResUT.CompR.functional hy h] at hw

/-- The same along `⨀`. -/
theorem BigCompT.absorb {Z : ResUT Loc Val K} :
    ∀ {L : List (ResUT Loc Val K)} {b : ResUT Loc Val K},
      BigCompT CellUT.CompatR CellUT.CompR L b →
        (∀ τ ∈ L, ResUT.CompR τ Z Z) → ResUT.CompR b Z Z := by
  intro L
  induction L with
  | nil => intro b h _; cases h; exact ResUT.CompR.comm (ResUT.comp_empty_right Z)
  | cons x L₀ ih =>
      intro b h hs
      cases h with
      | cons hrest hcx =>
          exact ResUT.CompR.absorb_comp hcx (hs x List.mem_cons_self)
            (ih hrest (fun τ hm => hs τ (List.mem_cons_of_mem _ hm)))

/-- A location of `ρ|dom(σ)` is a location of `σ`. -/
theorem ResUT.restrictDom_dom {ρ σ : ResUT Loc Val K} {l : Loc} {ζ : CellUT Loc Val K}
    (h : (ρ.restrictDom σ).get l = some ζ) : ∃ φ, σ.get l = some φ := by
  cases e : σ.get l with
  | none => rw [ResUT.restrictDom_get_of_none e] at h; exact absurd h (by simp)
  | some φ => exact ⟨φ, rfl⟩

/-- `imm(t̄, v, χ) ○ imm(s̄, v, χ) = imm(s̄, v, χ)` when `t̄ ⊆ s̄`. -/
theorem CellUT.compR_imm_sub {s t : TSet} {v : Val} {χ : ResUT Loc Val K}
    {hs : χ.InStratum s} {ht : χ.InStratum t}
    (hts : t.set ⊆ s.set) :
    CellUT.CompR (CellUT.immOf t v χ ht) (CellUT.immOf s v χ hs) (CellUT.immOf s v χ hs) := by
  have hc : CellUT.CompatS (CellUT.immOf t v χ ht) (CellUT.immOf s v χ hs) :=
    CellUT.compatS_iff.mpr ⟨by simp, by simp, by simp, by simp⟩
  have e : t ∪ s = s := TSet.ext (Finset.union_eq_right.mpr hts)
  have h₃ : χ.InStratum (t ∪ s) := by rw [e]; exact hs
  have := CellUT.CompR.strict hc
  rw [CellUT.compS_immOf hc h₃] at this
  have e' : CellUT.immOf (t ∪ s) v χ h₃ = CellUT.immOf s v χ hs := by
    clear this; revert h₃; rw [e]; intro h₃; rfl
  rwa [e'] at this

/-- `ρ|dom(ρ′|imm) ≤ ρ′|imm`, at `○`.
`[about ours: `[TR]` 6.57's *"by unfolding reb, we have that
`ρ|dom(ρ′ᵢ|imm) ≤ ρ′ᵢ|imm`"* (p. 18), at `○`]` -/
theorem ResUT.restrictDom_compR_restrict {β : Life} {ρ' ρ : ResUT Loc Val K}
    (hreb : ResUT.Reb β ρ' ρ) (k : Kind) :
    ResUT.CompR (G.restrict CellUT.kind (ρ.restrictDom (ρ'.restrict Kind.imm)) k)
      (G.restrict CellUT.kind ρ' Kind.imm) (G.restrict CellUT.kind ρ' Kind.imm) := by
  have hcell : ∀ l ζ,
      (G.restrict CellUT.kind (ρ.restrictDom (ρ'.restrict Kind.imm)) k).get l = some ζ →
      ∃ φ, (G.restrict CellUT.kind ρ' Kind.imm).get l = some φ ∧ CellUT.CompR ζ φ φ := by
    intro l ζ he
    obtain ⟨hD, -⟩ := ResUT.restrict_eq_some.mp he
    obtain ⟨φ, hφ⟩ := ResUT.restrictDom_dom hD
    obtain ⟨hφ', hφk⟩ := ResUT.restrict_eq_some.mp hφ
    have hρ : ρ.get l = some ζ := ResUT.restrictDom_get_inv hD
    refine ⟨φ, hφ, ?_⟩
    rcases CellUT.rep' φ with ⟨w, rfl⟩ | ⟨s, w, χ, hs, rfl⟩ | ⟨b, _, w, χ, hb, P, hw, rfl⟩
    · exact absurd hφk (by simp)
    · obtain ⟨t, ht, hts, rfl⟩ := ResUT.reb_imm_cell_sub hreb hρ hφ'
      exact CellUT.compR_imm_sub hts
    · exact absurd hφk (by simp)
  refine ⟨fun l ζ₁ ζ₂ e₁ e₂ => ?_, fun l => ?_⟩
  · obtain ⟨φ, hφ, hC⟩ := hcell l ζ₁ e₁
    rw [hφ] at e₂
    obtain rfl := Option.some.inj e₂
    exact ⟨_, hC⟩
  · cases e : (G.restrict CellUT.kind (ρ.restrictDom (ρ'.restrict Kind.imm)) k).get l with
    | none =>
        cases hf : (G.restrict CellUT.kind ρ' Kind.imm).get l with
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
theorem ResUT.reb_immPart_ag_absorbs {β : Life} {ρ'i ρ aD a₂ : ResUT Loc Val K}
    {l₀ : Loc} {s : TSet} {v : Val} {hs : ρ'i.InStratum s}
    (hreb : ResUT.Reb β ρ'i ρ)
    (haD : AgWT (ρ.restrictDom (G.restrict CellUT.kind ρ'i Kind.imm)) aD)
    (ha₂ : AgWT (ResUT.single l₀ (CellUT.immOf s v ρ'i hs)) a₂) :
    ResUT.CompR aD a₂ a₂ := by
  have hR : ∀ ψ₁ ψ₂ ψ : CellUT Loc Val K, CellUT.CompR ψ₁ ψ₂ ψ → CellUT.CompatR ψ₁ ψ₂ :=
    fun _ _ ψ hc => ⟨ψ, hc⟩
  obtain ⟨ev, av, p, hev, hav, hf, hagi⟩ := AgWT.single_imm_inv ha₂
  have hchain : ∀ Y : ResUT Loc Val K, (∃ z, ResUT.CompR Y z av) →
      ResUT.CompR Y a₂ a₂ := by
    rintro Y ⟨z, hz⟩
    obtain ⟨z₁, hz₁⟩ :=
      ResUT.Comp.factor_trans hR ResUT.compLawsR hz (ResUT.CompR.comm hf)
    obtain ⟨z₂, hz₂⟩ :=
      ResUT.Comp.factor_trans hR ResUT.compLawsR hz₁ (ResUT.CompR.comm hagi)
    exact ResUT.CompR.absorb hz₂
  have hfacImm : ∃ z, ResUT.CompR (G.restrict CellUT.kind ρ'i Kind.imm) z av := by
    cases hav with
    | mk hsm' hsi' hwm' hwi' hbm' hbi' ha' hσ' =>
        exact ResUT.Comp.factor_trans hR ResUT.compLawsR ha' hσ'
  cases haD with
  | mk hsm hsi hwm hwi hbm hbi ha hσ =>
      rename_i aa bm bi wm wi
      have hwmnil : wm = [] := by
        have h0 : wm.map Prod.fst = [] :=
          ResUT.sites_nil_of_none hsm (fun m χ hχ => by
            rw [ResUT.reb_imm_image hreb (ResUT.restrictDom_get_inv hχ)]
            exact fun c => Kind.noConfusion c)
        cases wm with
        | nil => rfl
        | cons q t => simp at h0
      subst hwmnil
      obtain rfl : bm = (PMap.empty : ResUT Loc Val K) := BigCompT.nil_inv hbm
      obtain ⟨z, hz⟩ := hfacImm
      have hDabs : ResUT.CompR
          (G.restrict CellUT.kind (ρ.restrictDom (ρ'i.restrict Kind.imm)) Kind.imm) a₂ a₂ :=
        hchain _ (ResUT.Comp.factor_trans hR ResUT.compLawsR
          (ResUT.restrictDom_compR_restrict hreb Kind.imm) hz)
      have haaabs : ResUT.CompR aa a₂ a₂ :=
        ResUT.CompR.absorb_comp ha hDabs (ResUT.CompR.comm (ResUT.comp_empty_right a₂))
      have hbiabs : ResUT.CompR bi a₂ a₂ := by
        refine BigCompT.absorb hbi (fun τ hm => ?_)
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
        obtain ⟨χq, evq, avq, hχq, hexq, hagq, hcq⟩ := AgWitsIT.mem hwi q hq
        obtain ⟨φ, hφ⟩ := ResUT.restrictDom_dom hχq
        obtain ⟨hφ', hφk⟩ := ResUT.restrict_eq_some.mp hφ
        have hρq : ρ.get q.1 = some χq := ResUT.restrictDom_get_inv hχq
        obtain ⟨-, -, hkw, -⟩ := ResUT.reb_imm_cell_kw hreb hρq hφ' hφk
        rw [hkw] at hexq hagq
        obtain ⟨ev', av', p', z', hex', hag', hc', hz'⟩ := AgWT.imm_wit_le hav hφ' hφk
        obtain rfl : ev' = evq := ExRT.functional hex' hexq
        obtain rfl : av' = avq := AgWT.functional hag' hagq
        obtain rfl : p' = q.2 := ResUT.CompR.functional hc' hcq
        exact hchain _ ⟨z', hz'⟩
      exact ResUT.CompR.absorb_comp hσ haaabs hbiabs

/-- `ρ = ρ|dom(ρ′|imm) ● ρ|dom(ρ′|mut,own)`, using `[TR]` 6.58's *"note
`dom(ρ) ⊆ dom(ρ′ᵢ)` by unfolding reb"*.
`[about ours: the splitting `[TR]` 6.58's and 6.59's proofs open with]` -/
theorem ResUT.restrictDom_split {α : Life} {ρ' ρ : ResUT Loc Val K}
    (hreb : ResUT.Reb α ρ' ρ) :
    ResUT.CompS (ρ.restrictDom (G.restrict CellUT.kind ρ' Kind.imm)) (ρ.restrictDom ρ'.exclPart) ρ := by
  have hcase : ∀ l,
      ((ρ.restrictDom (G.restrict CellUT.kind ρ' Kind.imm)).get l = ρ.get l ∧
        (ρ.restrictDom ρ'.exclPart).get l = none) ∨
      ((ρ.restrictDom (G.restrict CellUT.kind ρ' Kind.imm)).get l = none ∧
        (ρ.restrictDom ρ'.exclPart).get l = ρ.get l) := by
    intro l
    cases e : ρ'.get l with
    | none =>
        have hρ : ρ.get l = none := by
          cases f : ρ.get l with
          | none => rfl
          | some ζ =>
              obtain ⟨φ, hφ⟩ := ResUT.reb_dom_subset hreb f
              rw [e] at hφ; exact absurd hφ (by simp)
        refine Or.inl ⟨?_, ?_⟩
        · rw [ResUT.restrictDom_get_of_none (ResUT.restrict_get_none e), hρ]
        · refine ResUT.restrictDom_get_of_none ?_
          show (ρ'.get l).bind _ = none
          rw [e]; rfl
    | some φ =>
        by_cases hk : φ.kind = Kind.imm
        · refine Or.inl ⟨ResUT.restrictDom_get_of_some (ResUT.restrict_get_some e hk), ?_⟩
          refine ResUT.restrictDom_get_of_none ?_
          show (ρ'.get l).bind _ = none
          rw [e]
          simp [hk]
        · refine Or.inr ⟨ResUT.restrictDom_get_of_none (ResUT.restrict_get_ne e hk), ?_⟩
          refine ResUT.restrictDom_get_of_some (ResUT.restrictOn_eq_some.mpr ⟨e, ?_⟩)
          simp [hk]
  refine ⟨ResUT.Compat.of_disjoint (fun l => ?_), fun l => ?_⟩
  · rcases hcase l with ⟨-, h⟩ | ⟨h, -⟩
    · exact Or.inr h
    · exact Or.inl h
  · show OptCompT CellUT.CompS ((ρ.restrictDom (G.restrict CellUT.kind ρ' Kind.imm)).get l)
      ((ρ.restrictDom ρ'.exclPart).get l) (ρ.get l)
    rcases hcase l with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> rw [h₁, h₂] <;>
      cases ρ.get l with
      | none => rfl
      | some ζ => rfl

/-- `[TR]` Lemma 6.8 with the hypothesis `⟦ρ₂⟧ = ⟦ρ₃⟧` as a Kleene equality
(`↔` between the two graphs).
`[about ours: `[TR]` 6.8 with its printed hypothesis in the Kleene shape]` -/
theorem ResUT.lower_congr_iff {ρ₁ ρ₂ ρ₃ ρ₁₂ ρ₁₃ : ResUT Loc Val K}
    (heq : ∀ m, ResUT.Lower ρ₂ m ↔ ResUT.Lower ρ₃ m)
    (h₁₂ : ResUT.CompS ρ₁ ρ₂ ρ₁₂) (hh₂ : ResUT.Hash ρ₁ ρ₂)
    (h₁₃ : ResUT.CompS ρ₁ ρ₃ ρ₁₃) (hh₃ : ResUT.Hash ρ₁ ρ₃) :
    ∀ w, ResUT.Lower ρ₁₂ w ↔ ResUT.Lower ρ₁₃ w := by
  obtain ⟨τ, hτ, hv⟩ := hh₂.2
  obtain ⟨σ₂, hσ₂⟩ := (ResUT.Valid.split hτ hv).2
  have hm₂ : ResUT.Lower ρ₂ (fun l => (σ₂.get l).map CellUT.erase) :=
    ⟨σ₂, hσ₂, fun _ => rfl⟩
  exact fun w => ResUT.Lower.congr hm₂ ((heq _).mp hm₂) h₁₂ hh₂ h₁₃ hh₃ (w := w)

end BoCa.Fig16.Tree

end
