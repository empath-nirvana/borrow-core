import PositiveArrays.FrameFam
import PositiveArrays.Split

/-!
# PositiveArrays — a partial borrow: lend some places, keep the others

`wpTS_M_framePartial` lends the places of a family that satisfy `p` as `mut` leaves at one
lifetime, while the callback keeps the other places owned. It is `sepList_partition` followed by
`wpTS_M_frameList` on the lent part; the kept part rides in the frames' hypothesis. The places
and their types are arbitrary, so the same lemma is Rust's disjoint field borrow of a struct
(`&mut s.a` and `&mut s.c` with `s.b` still usable) and `split_at_mut` of an array followed by
lending one half.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.PositiveArrays
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- **Lend the places satisfying `p`; the callback also owns the rest.** -/
theorem wpTS_M_framePartial (T : Loc → VTy) (δ : LSub) (β : Life)
    (hP : ∀ m ls w σ, vC true (T m) ls δ w σ → σ.InStratum β) (e : Expr) (ls : List SRec)
    (Φ : List SRec → Val → WProp) (β' : Life) (hΦ : ∀ ls v ρ, Φ ls v ρ → BoLo.Outlives ρ β')
    (p : Loc → Bool) (I : List Loc) (Q : List SRec → Val → WProp)
    (hQ : ∀ ls' v, Entails (sepList (ownLeafH T ls' δ) (I.filter p) ⋆ Φ ls' v) (Q ls' v)) :
    Entails
      (sepList (ownLeafH T ls δ) I ⋆
        fresh (fun α => sepList (mutLeafH T ls δ α) (I.filter p) ─⋆
          (sepList (ownLeafH T ls δ) (I.filter (fun m => !p m)) ─⋆ wpTS ls e Φ)))
      (wpTS ls e Q) := by
  rintro ρ ⟨ρo, ρH, hc, ho, γH, hH⟩
  obtain ⟨ρl, ρk, hlk, hl, hk⟩ := sepList_partition p I ho
  -- the kept part joins the hypothesis
  obtain ⟨K, hK, hρ⟩ := compS_reassoc hlk hc
  refine wpTS_M_frameList T δ β hP e ls Φ β' hΦ (I.filter p) Q hQ ρ ⟨ρl, K, hρ, hl, ?_⟩
  obtain ⟨aK, haK⟩ := K.exists_atLife
  refine ⟨aK ⊓ γH, fun α hα => ⟨?_, outlives_of_atLife haK (lt_of_lt_of_le hα inf_le_left)⟩⟩
  intro ρm ρ' hm hcm
  -- `ρ′ = (ρH ● ρm) ● ρk`: the hypothesis takes the lent leaves, then the kept ones
  obtain ⟨X, hX, hρ'⟩ := compS_exch (ResU.CompS.comm hK) hcm
  exact (hH α (lt_of_lt_of_le hα inf_le_right)).1 ρm X hm hX ρk ρ' hk hρ'

end BoCa.Fig16.LogRel.Core.PositiveArrays

end
