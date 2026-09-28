import Paper.S1_Syntax.Definitions
import Paper.S2_Statics.Definitions
import Paper.S5_Model.Definitions
import Paper.S6_4_StandardEntailments.Lemmas
import Paper.S6_5_NonStandardEntailments.Lemmas
import Paper.S6_6_ReborrowingEntailments.Lemmas
import Support.Lifetimes.Interpretation
import Support.LogicalRelation.ClosingSubstitutions
import Support.Model.Propositions
import Support.Model.Strata
import Core.Images
import Core.World

/-!
# Core — ReborrowShapes  `[spec §3]`

`Support/TypedWorld`'s layer `ReborrowShapes`, with records typed at `VTy`.  `[TR]` Lemmas 6.131 and 6.132 at the shape relation `vShape`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- `↺_α` distributes over a range: a range whose every leaf reborrows, at `α`, reborrows.
`[spec §9]` -/
theorem reborrow_sepRange {α : Life} {P Q : BoCa.Loc → WProp}
    (h : ∀ m ρ, P m ρ → BoLo.Outlives ρ α → reborrow α (Q m) ρ) :
    ∀ {ℓ : BoCa.Loc} {n : Nat} {ρ : WRes}, sepRange P ℓ n ρ → BoLo.Outlives ρ α →
      reborrow α (sepRange Q ℓ n) ρ
  | _, 0, ρ, hs, _ => reborrow_pure α True ρ hs
  | _, _ + 1, ρ, ⟨ρ₁, ρ₂, hc, h₁, h₂⟩, ho => by
      obtain ⟨o₁, o₂⟩ := (outlives_comp hc α).mp ho
      exact BoLo.reborrow_star α _ _ ρ ⟨ρ₁, ρ₂, hc, h _ _ h₁ o₁, reborrow_sepRange h h₂ o₂⟩

/-! ### Lemma 6.131 (↺V₁) at the typed world; record in `Paper/S6_6_ReborrowingEntailments/Lemmas.lean` -/
/-- `[TR]` Lemma 6.131 (`↺V₁`, p. 34) at the shape relation:
`[α] vShape⟦T⟧δ(v) ⊨ ↺_α vShape⟦Imm̲ 'a T⟧δ(v)` where `δ('a) = α`, at every `T`.
The proof is `reborrow_vDen`'s, bullet for bullet.  `[about ours: 6.131 at our shape
relation; the `Ref` bullet as `reborrow_vDen` takes it]` -/
theorem reborrow_vShape {α : Life} {x : LifeVar} {δ : LSub}
    (hδ : (Lifetime.Life.var x).interp δ = some α) :
    ∀ (T : VTy) (v : Val),
      box α (vShape T δ v) ⊨ reborrow α (vShape (T.immReborrow (.var x)) δ v) := by
  intro T v ρ hρ
  refine vShape_ind δ (fun T v ρ => BoLo.Outlives ρ α →
      reborrow α (vShape (T.immReborrow (.var x)) δ v) ρ) ?_ T v ρ hρ.1 hρ.2
  intro T v ρ h hout
  have hρ := (⟨h, hout⟩ : box α _ ρ)
  cases T with
  | unit =>
      exact Entails.trans (box_L α _) (reborrow_pure α _) ρ hρ
  | int w =>
      exact Entails.trans (box_L α _) (reborrow_pure α _) ρ hρ
  | sum T₁ T₂ =>
      rcases (box_or α _ _).1 ρ hρ with h | h
      · obtain ⟨v₁, h⟩ := (box_ex α _).2 ρ h
        obtain ⟨σ₀, σ, hc, hp, hA⟩ := (box_sep α _ _).1 ρ h
        exact (reborrow_or α _ _).1 ρ (or_R₁ _ _ ρ ((reborrow_ex α _).1 ρ
          (ex_R v₁ (Entails.refl _) ρ (reborrow_star_pure α _ _ ρ
            ⟨σ₀, σ, hc, box_L α _ σ₀ hp, hA.1.2 hA.2⟩))))
      · obtain ⟨v₂, h⟩ := (box_ex α _).2 ρ h
        obtain ⟨σ₀, σ, hc, hp, hA⟩ := (box_sep α _ _).1 ρ h
        exact (reborrow_or α _ _).1 ρ (or_R₂ _ _ ρ ((reborrow_ex α _).1 ρ
          (ex_R v₂ (Entails.refl _) ρ (reborrow_star_pure α _ _ ρ
            ⟨σ₀, σ, hc, box_L α _ σ₀ hp, hA.1.2 hA.2⟩))))
  | tensor T₁ T₂ =>
      obtain ⟨v₁, hρ⟩ := (box_ex α _).2 ρ hρ
      obtain ⟨v₂, hρ⟩ := (box_ex α _).2 ρ hρ
      obtain ⟨σ₀, σ, hc, hp, hrest⟩ := (box_sep α _ _).1 ρ hρ
      obtain ⟨σ₁, σ₂, hc', h₁, h₂⟩ := (box_sep α _ _).1 σ hrest
      exact (reborrow_ex α _).1 ρ (ex_R v₁ (Entails.refl _) ρ
        ((reborrow_ex α _).1 ρ (ex_R v₂ (Entails.refl _) ρ
          (reborrow_star_pure α _ _ ρ ⟨σ₀, σ, hc, box_L α _ σ₀ hp,
            BoLo.reborrow_star α _ _ σ
              ⟨σ₁, σ₂, hc', h₁.1.2 h₁.2, h₂.1.2 h₂.2⟩⟩))))
  | thunk _ =>
      exact reborrow_emp_box α _ ρ hρ
  | opq _ =>
      exact reborrow_emp_box α _ ρ hρ
  | zero =>
      exact False.elim hρ.1
  | box a T =>
      obtain ⟨⟨β, -, hb⟩, ho⟩ := hρ
      exact hb.1.2 ho
  | ref T =>
      obtain ⟨ℓ, hρ⟩ := (box_ex α _).2 ρ hρ
      obtain ⟨v', hρ⟩ := (box_ex α _).2 ρ hρ
      obtain ⟨σ₀, σ, hc, hp, hrest⟩ := (box_sep α _ _).1 ρ hρ
      obtain ⟨σ₁, σ₂, hc', hown, hpay⟩ := (box_sep α _ _).1 σ hrest
      obtain ⟨χ, hr, hχ⟩ := reborrow_star_pure α _ _ ρ
          ⟨σ₀, σ, hc, box_L α _ σ₀ hp,
            reborrow_ptoOwn ℓ v' (vShape T δ) σ
              ⟨σ₁, σ₂, hc', box_L α _ σ₁ hown, ⟨hpay.1.1, hpay.2⟩⟩⟩
      exact ⟨χ, hr, α, hδ, ℓ, hχ⟩
  | bang T =>
    exact reborrow_emp_box α _ ρ hρ
  | imm a T =>
      obtain ⟨⟨γ, hγ, hb⟩, ho⟩ := hρ
      obtain ⟨ℓ, hbox⟩ := (box_ex α _).2 ρ (show box α _ ρ from ⟨hb, ho⟩)
      obtain ⟨σ₀, σ, hc, hp, hcell⟩ := (box_sep α _ _).1 ρ hbox
      have hcell' : box α (ptoImm ℓ γ (vShape T δ)) σ :=
        ⟨ptoImm_mono (fun u σ' h => h.1) σ hcell.1, hcell.2⟩
      obtain ⟨χ, hr, hχ⟩ := reborrow_star_pure α _ _ ρ
          ⟨σ₀, σ, hc, box_L α _ σ₀ hp, reborrow_ptoImm ℓ (vShape T δ) σ hcell'⟩
      exact ⟨χ, hr, γ, hγ, ℓ, hχ⟩
  | «mut» a T =>
      obtain ⟨⟨γ, hγ, hb⟩, ho⟩ := hρ
      obtain ⟨ℓ, hbox⟩ := (box_ex α _).2 ρ (show box α _ ρ from ⟨hb, ho⟩)
      obtain ⟨σ₀, σ, hc, hp, hcell⟩ := (box_sep α _ _).1 ρ hbox
      obtain ⟨⟨P, hpto, hPsh⟩, hoσ⟩ := hcell
      obtain ⟨χ, hr, hχ⟩ := reborrow_star_pure α _ _ ρ
          ⟨σ₀, σ, hc, box_L α _ σ₀ hp,
            reborrow_mono (ptoImm_mono (fun u σ' h => (hPsh u σ' h).1)) σ
              (reborrow_ptoMut ℓ P σ ⟨hpto, hoσ⟩)⟩
      -- `↺∃` and the fold of `vShape⟦Imm 'a T′⟧`
      exact ⟨χ, hr, α, hδ, ℓ, hχ⟩
  | unk =>
      exact reborrow_emp_box α _ ρ hρ
  | tvar _ => exact hρ.1.elim
  | fam L =>
      obtain ⟨ℓ, n, σ₀, σ, hc, hp, hs⟩ := h
      obtain ⟨-, o₂⟩ := (outlives_comp hc α).mp hout
      obtain ⟨χ, hr, hχ⟩ := reborrow_star_pure α _ _ ρ ⟨σ₀, σ, hc, hp,
        reborrow_sepRange (fun m σ' hm ho => hm.2 ho) hs o₂⟩
      exact ⟨χ, hr, ℓ, n, hχ⟩
  | mu A =>
      obtain ⟨hcl, hG⟩ := h
      exact reborrow_mono (fun σ hσ => (vShape_immReborrow_mu_iff (show A.Cl 1 from hcl) _ δ v σ).mpr hσ)
        ρ (hG.2 hout)

/-! ### Lemma 6.132 (↺V₂) at the typed world; record in `Paper/S6_6_ReborrowingEntailments/Lemmas.lean` -/
/-- `[TR]` Lemma 6.132 (`↺V₂`, p. 35) at the shape relation, at one `β`:
`vShape⟦T⟧δ(v) ⊨ [β] … ⊨ ↺_β vShape⟦Imm̲ 'a T⟧δ['a↦β](v)` for `ρ ∈ Res_β` — the printed
proof's steps after "fix `α ⊏ δ` arbitrary": `[]R`, `'a ∉ FV(T)`, `↺V₁`.
`[about ours: 6.132 at the shape relation, at a fixed lifetime of the `И`]` -/
theorem six132_shape {x : LifeVar} {T : VTy} (hx : ¬ VFree x T) (δ : LSub) (β : Life) (v : Val)
    {ρ : WRes} (h : vShape T δ v ρ) (hρ : ρ.InStratum β) :
    reborrow β (vShape (T.immReborrow (.var x)) (δ.extend x β) v) ρ := by
  have h' : box β (vShape T (δ.extend x β) v) ρ := by
    rw [vShape_extend_of_not_free hx]; exact ⟨h, hρ⟩
  exact reborrow_vShape (interp_ext_self δ x β) T v ρ h'

/-- `[TR]` Lemma 6.132 at the shape relation, with its `И`: every `β` below the stratum of
the resource.  `[about ours: 6.132 at our shape relation]` -/
theorem six132_shape_fresh {x : LifeVar} {T : VTy} (hx : ¬ VFree x T) (δ : LSub) (v : Val) :
    vShape T δ v ⊨ fresh (fun β => reborrow β (vShape (T.immReborrow (.var x)) (δ.extend x β) v)) := by
  intro ρ h
  obtain ⟨γ, hγ⟩ := ResU.exists_stratum ρ
  refine ⟨γ, fun β hβ => ⟨six132_shape hx δ β v h (hγ.mono (le_of_lt hβ)), ?_⟩⟩
  exact hγ.mono (le_of_lt hβ)

end BoCa.Fig16.LogRel.Core

end
