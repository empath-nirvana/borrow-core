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
import Support.TypedWorld.Images
import Support.TypedWorld.World

/-!
# Support — TypedWorld — ReborrowShapes

`[about ours]`.  `[TR]` Lemmas 6.131 and 6.132 at the shape relation `vShape`.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Typed
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### Lemma 6.131 (↺V₁) at the typed world; record in `Paper/S6_6_ReborrowingEntailments/Lemmas.lean` -/
/-- `[TR]` Lemma 6.131 (`↺V₁`, p. 34) at the shape relation:
`[α] vShape⟦T⟧δ(v) ⊨ ↺_α vShape⟦Imm̲ 'a T⟧δ(v)` where `δ('a) = α`, at every `T`.
The proof is `reborrow_vDen`'s, bullet for bullet.  `[about ours: 6.131 at our shape
relation; the `Ref` bullet as `reborrow_vDen` takes it]` -/
theorem reborrow_vShape {α : Life} {x : LifeVar} {δ : LSub}
    (hδ : (Lifetime.Life.var x).interp δ = some α) :
    ∀ (T : Ty) (v : Val),
      box α (vShape T δ v) ⊨ reborrow α (vShape (T.immReborrow (.var x)) δ v) := by
  intro T
  induction T with
  | unit =>
      intro v
      exact Entails.trans (box_L α _) (reborrow_pure α _)
  | sum T₁ T₂ ih₁ ih₂ =>
      intro v ρ hρ
      rcases (box_or α _ _).1 ρ hρ with h | h
      · obtain ⟨v₁, h⟩ := (box_ex α _).2 ρ h
        obtain ⟨σ₀, σ, hc, hp, hA⟩ := (box_sep α _ _).1 ρ h
        exact (reborrow_or α _ _).1 ρ (or_R₁ _ _ ρ ((reborrow_ex α _).1 ρ
          (ex_R v₁ (Entails.refl _) ρ (reborrow_star_pure α _ _ ρ
            ⟨σ₀, σ, hc, box_L α _ σ₀ hp, ih₁ v₁ σ hA⟩))))
      · obtain ⟨v₂, h⟩ := (box_ex α _).2 ρ h
        obtain ⟨σ₀, σ, hc, hp, hA⟩ := (box_sep α _ _).1 ρ h
        exact (reborrow_or α _ _).1 ρ (or_R₂ _ _ ρ ((reborrow_ex α _).1 ρ
          (ex_R v₂ (Entails.refl _) ρ (reborrow_star_pure α _ _ ρ
            ⟨σ₀, σ, hc, box_L α _ σ₀ hp, ih₂ v₂ σ hA⟩))))
  | tensor T₁ T₂ ih₁ ih₂ =>
      intro v ρ hρ
      obtain ⟨v₁, hρ⟩ := (box_ex α _).2 ρ hρ
      obtain ⟨v₂, hρ⟩ := (box_ex α _).2 ρ hρ
      obtain ⟨σ₀, σ, hc, hp, hrest⟩ := (box_sep α _ _).1 ρ hρ
      obtain ⟨σ₁, σ₂, hc', h₁, h₂⟩ := (box_sep α _ _).1 σ hrest
      exact (reborrow_ex α _).1 ρ (ex_R v₁ (Entails.refl _) ρ
        ((reborrow_ex α _).1 ρ (ex_R v₂ (Entails.refl _) ρ
          (reborrow_star_pure α _ _ ρ ⟨σ₀, σ, hc, box_L α _ σ₀ hp,
            BoLo.reborrow_star α _ _ σ
              ⟨σ₁, σ₂, hc', ih₁ v₁ σ₁ h₁, ih₂ v₂ σ₂ h₂⟩⟩))))
  | lolli T₁ T₂ _ _ =>
      intro v
      exact reborrow_emp_box α _
  | fn T₁ T₂ _ _ =>
      intro v
      exact reborrow_emp_box α _
  | all y c T _ =>
      intro v
      exact reborrow_emp_box α _
  | box a T ih =>
      intro v
      refine Entails.trans (box_mono ?_) (ih v)
      intro ρ hρ
      obtain ⟨β, -, hb⟩ := hρ
      exact box_L β _ ρ hb
  | ref T _ =>
      intro v ρ hρ
      obtain ⟨ℓ, hρ⟩ := (box_ex α _).2 ρ hρ
      obtain ⟨v', hρ⟩ := (box_ex α _).2 ρ hρ
      obtain ⟨σ₀, σ, hc, hp, hrest⟩ := (box_sep α _ _).1 ρ hρ
      obtain ⟨σ₁, σ₂, hc', hown, hpay⟩ := (box_sep α _ _).1 σ hrest
      obtain ⟨χ, hr, hχ⟩ := reborrow_star_pure α _ _ ρ
          ⟨σ₀, σ, hc, box_L α _ σ₀ hp,
            reborrow_ptoOwn ℓ v' (vShape T δ) σ
              ⟨σ₁, σ₂, hc', box_L α _ σ₁ hown, hpay⟩⟩
      exact ⟨χ, hr, α, hδ, ℓ, hχ⟩
  | imm a T _ =>
      intro v ρ hρ
      obtain ⟨⟨γ, hγ, hb⟩, ho⟩ := hρ
      obtain ⟨ℓ, hbox⟩ := (box_ex α _).2 ρ (show box α _ ρ from ⟨hb, ho⟩)
      obtain ⟨σ₀, σ, hc, hp, hcell⟩ := (box_sep α _ _).1 ρ hbox
      obtain ⟨χ, hr, hχ⟩ := reborrow_star_pure α _ _ ρ
          ⟨σ₀, σ, hc, box_L α _ σ₀ hp, reborrow_ptoImm ℓ (vShape T δ) σ hcell⟩
      exact ⟨χ, hr, γ, hγ, ℓ, hχ⟩
  | «mut» a T _ =>
      intro v ρ hρ
      obtain ⟨⟨γ, hγ, hb⟩, ho⟩ := hρ
      obtain ⟨ℓ, hbox⟩ := (box_ex α _).2 ρ (show box α _ ρ from ⟨hb, ho⟩)
      obtain ⟨σ₀, σ, hc, hp, hcell⟩ := (box_sep α _ _).1 ρ hbox
      obtain ⟨⟨P, hpto, hPsh⟩, hoσ⟩ := hcell
      obtain ⟨χ, hr, hχ⟩ := reborrow_star_pure α _ _ ρ
          ⟨σ₀, σ, hc, box_L α _ σ₀ hp,
            reborrow_mono (ptoImm_mono (fun u => hPsh u)) σ
              (reborrow_ptoMut ℓ P σ ⟨hpto, hoσ⟩)⟩
      -- `↺∃` and the fold of `vShape⟦Imm 'a T′⟧`
      exact ⟨χ, hr, α, hδ, ℓ, hχ⟩
  | unk =>
      intro v
      exact reborrow_emp_box α _

/-! ### Lemma 6.132 (↺V₂) at the typed world; record in `Paper/S6_6_ReborrowingEntailments/Lemmas.lean` -/
/-- `[TR]` Lemma 6.132 (`↺V₂`, p. 35) at the shape relation, at one `β`:
`vShape⟦T⟧δ(v) ⊨ [β] … ⊨ ↺_β vShape⟦Imm̲ 'a T⟧δ['a↦β](v)` for `ρ ∈ Res_β` — the printed
proof's steps after "fix `α ⊏ δ` arbitrary": `[]R`, `'a ∉ FV(T)`, `↺V₁`.
`[about ours: 6.132 at the shape relation, at a fixed lifetime of the `И`]` -/
theorem six132_shape {x : LifeVar} {T : Ty} (hx : ¬ LFree x T) (δ : LSub) (β : Life) (v : Val)
    {ρ : WRes} (h : vShape T δ v ρ) (hρ : ρ.InStratum β) :
    reborrow β (vShape (T.immReborrow (.var x)) (δ.extend x β) v) ρ := by
  have h' : box β (vShape T (δ.extend x β) v) ρ := by
    rw [vShape_extend_of_not_free hx]; exact ⟨h, hρ⟩
  exact reborrow_vShape (interp_ext_self δ x β) T v ρ h'

/-- `[TR]` Lemma 6.132 at the shape relation, with its `И`: every `β` below the stratum of
the resource.  `[about ours: 6.132 at our shape relation]` -/
theorem six132_shape_fresh {x : LifeVar} {T : Ty} (hx : ¬ LFree x T) (δ : LSub) (v : Val) :
    vShape T δ v ⊨ fresh (fun β => reborrow β (vShape (T.immReborrow (.var x)) (δ.extend x β) v)) := by
  intro ρ h
  obtain ⟨γ, hγ⟩ := ResU.exists_stratum ρ
  refine ⟨γ, fun β hβ => ⟨six132_shape hx δ β v h (hγ.mono (le_of_lt hβ)), ?_⟩⟩
  exact hγ.mono (le_of_lt hβ)

end BoCa.Fig16.LogRel.Typed

end
