import Law2.Kappa

/-!
# Law2 — re-lending at `∀` and at `F`, for what typing builds

Re-lending a computation pointwise, at every configuration the relation relates, has two cases
that read more than the computation (`DenseCarrier`, *Re-lending*):

* **`∀`**: one re-make has to serve every instance of the quantifier at the moved reading,
  including instances no re-making of an old one reaches (a re-making other than the identity is
  not onto, `DenseCarrier`'s `exists_gap`);
* **`F`**: `wpTS` at the moved reading quantifies over the frames of the moved world, and a frame
  holding a cell where the re-making left a gap is the re-make of no old frame
  (`Restrat`'s `frame_outside_image`), so the old run cannot be sent there.

For a term Core's typing derives, and for a typed segment over a hereditarily typed context,
neither is asked: the fundamental property is applied **at** the moved reading. Its `∀` clause
quantifies over every instance of the moved reading, and its `wpTS` over every frame of the moved
world, after the re-make is chosen.

* `relend_all`: at `∀'y ⊏ c. C`, one re-make of the context serves every instance `α'` of the
  moved reading below the moved bound, in the gap or not.
* `relend_ret`: at `F A`, the re-made context runs to `𝒱⟦A⟧` at the moved reading under every
  frame of the moved world.
* `htv_relend_all`, `htv_relend_ret`: the same for a closure a typed program builds, forced.

Pointwise, for every configuration the relation relates at `∀` or `F`: not derived, and no
obstruction verified.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Law2
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Kont Head)
open BoCa.Lifetime (LifeVar LifeCtx LSub)

section
variable {c : Life} (θ : Restrat.Emb c)

/-- **`∀`: one re-make serves every instance.** A typed segment at `∀'y ⊏ b. C` over a
hereditarily typed context has one re-made context at which, plugged with any answer related at
the moved reading, it is related at **every** instance `α'` of the moved reading strictly below the
moved bound. -/
theorem relend_all {K : Kont} {Δ : LifeCtx} {Γ : Ctx VTy} {B : VTy} {y : LifeVar}
    {b : Lifetime.Life} {C : CTy} {γ : List Val} (hK : TypedSeg K Δ Γ B (.all y b C) γ)
    {δ : LSub} {ρ : WRes} (hδ : Δ.Models δ) (hlive : Ctx.LiveWithin Γ γ)
    (hg : HTG (ℍ := ℍ) Γ δ γ ρ) :
    ∃ ρ', RemakeR θ ρ ρ' ∧ ∀ (ls : List SRec) (w : Val) (ρw ρt : WRes),
      vCE (ℍ := ℍ) none true B ls (mv θ δ) w ρw → ResU.CompS ρw ρ' ρt →
        ∀ α' : Life, LtLife (mv θ δ) b α' →
          cC (ℍ := ℍ) C ls ((mv θ δ).extend y α') (.app (K.plug (.val w)) (.val .unit)) ρt := by
  obtain ⟨ρ', hR, -, h⟩ := kappa_relend hK hδ hlive hg θ
  refine ⟨ρ', hR, fun ls w ρw ρt hw hc α' hα' => ?_⟩
  have hall := h ls w ρw ρt hw hc α' PMap.empty ρt ⟨rfl, hα'⟩ (ResU.comp_empty_right ρt)
  exact hall

/-- **`F`: the moved run is at the moved world's frames.** A typed segment at `F A` over a
hereditarily typed context has one re-made context at which, plugged with any answer related at the
moved reading, it runs to `𝒱⟦A⟧` at the moved reading: `wpTS` there, under every frame of the
moved world. -/
theorem relend_ret {K : Kont} {Δ : LifeCtx} {Γ : Ctx VTy} {B A : VTy} {γ : List Val}
    (hK : TypedSeg K Δ Γ B (.ret A) γ) {δ : LSub} {ρ : WRes} (hδ : Δ.Models δ)
    (hlive : Ctx.LiveWithin Γ γ) (hg : HTG (ℍ := ℍ) Γ δ γ ρ) :
    ∃ ρ', RemakeR θ ρ ρ' ∧ ∀ (ls : List SRec) (w : Val) (ρw ρt : WRes),
      vCE (ℍ := ℍ) none true B ls (mv θ δ) w ρw → ResU.CompS ρw ρ' ρt →
        wpTS (ℍ := ℍ) ls (K.plug (.val w))
          (fun ls'' => vCE (ℍ := ℍ) none true A ls'' (mv θ δ)) ρt := by
  obtain ⟨ρ', hR, -, h⟩ := kappa_relend hK hδ hlive hg θ
  exact ⟨ρ', hR, h⟩

/-- **A closure a typed program builds, at `U (∀'y ⊏ b. C)`**: its re-make is related at every
instance of the moved reading below the moved bound. -/
theorem htv_relend_all {y : LifeVar} {b : Lifetime.Life} {C : CTy} {δ : LSub} {f : Val}
    {ρ : WRes} (h : HTV (ℍ := ℍ) (.thunk (.all y b C)) δ f ρ) (ls : List SRec) :
    ∃ ρ', RemakeR θ ρ ρ' ∧ ∀ α' : Life, LtLife (mv θ δ) b α' →
      cC (ℍ := ℍ) C ls ((mv θ δ).extend y α') (.app (.val f) (.val .unit)) ρ' := by
  obtain ⟨ρ', hR, h'⟩ := htv_relend_vC θ h ls
  refine ⟨ρ', hR, fun α' hα' => ?_⟩
  have hc := h' ls (Ext.refl ls ρ')
  exact hc α' PMap.empty ρ' ⟨rfl, hα'⟩ (ResU.comp_empty_right ρ')

/-- **A closure a typed program builds, at `U (F A)`**: forced, its re-make runs to `𝒱⟦A⟧` at
the moved reading. -/
theorem htv_relend_ret {A : VTy} {δ : LSub} {f : Val} {ρ : WRes}
    (h : HTV (ℍ := ℍ) (.thunk (.ret A)) δ f ρ) (ls : List SRec) :
    ∃ ρ', RemakeR θ ρ ρ' ∧
      wpTS (ℍ := ℍ) ls (.app (.val f) (.val .unit))
        (fun ls'' => vCE (ℍ := ℍ) none true A ls'' (mv θ δ)) ρ' := by
  obtain ⟨ρ', hR, h'⟩ := htv_relend_vC θ h ls
  exact ⟨ρ', hR, h' ls (Ext.refl ls ρ')⟩

end

end Law2

end
