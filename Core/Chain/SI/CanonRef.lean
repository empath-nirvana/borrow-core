import Core.Chain.SI.RebAcrossC

/-!
# The canonical image of a `ref S` record is shaped at every lifetime

For a record at `ref S` the image is one cell, at the root. `canon_ref`: whatever lifetime and
variable the template was taken at, `canon r β` has the shape `Imm̲ 'x (ref S)` asks for at `β`:
`relRes` re-takes the root cell at `{β}` and keeps its value and witness, and the witness's shape
at `S` does not read `'x`. The payload `S` is any type: a thunk, an opaque type, a type the
record's type was instantiated at.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeVar)

theorem canon_ref {r : FrameRec} {S : VTy} (hT : r.T = .ref S) {x : LifeVar}
    (hx : ¬ VFree x S) {β : Life} (hS : TmplSpec r (tmpl r)) (hRβ : r.R.InStratum β)
    (hown : ∀ ℓ, r.v = .loc ℓ → ∃ u, r.R.get ℓ = some (CellU.ownOf u)) :
    vShape (r.T.immReborrow (.var x)) (r.δ.extend x β) r.v (canon r β) := by
  obtain ⟨β₀, x₀, hx₀, hreb₀, hden₀, -⟩ := hS
  rw [hT] at hden₀ hx₀ ⊢
  obtain ⟨β₁, -, ℓ, hk⟩ := hden₀
  obtain ⟨hv, hpto⟩ := pure_sep_iff.mp hk
  obtain ⟨s, u, w, h, htm, hSw, -⟩ := hpto
  obtain ⟨u₀, hu₀⟩ := hown ℓ hv
  have e : (tmpl r).get ℓ = some (CellU.immOf s u w h) := by rw [htm]; exact ResU.single_get_self _ _
  have hwβ : (CellU.immOf s u w h).wit.InStratum (LSet.singleton β).join :=
    reb_wit_stratum hRβ hreb₀ ℓ _ e ⟨_, hu₀, by simp⟩
  rw [CellU.wit_immOf] at hwβ
  have hcanon : canon r β = ResU.single ℓ (CellU.immOf (LSet.singleton β) u w hwβ) := by
    rw [canon, htm, relRes_single]
    congr 1
    unfold relCell
    rw [dif_pos ⟨CellU.kind_immOf _ _ _ _, ⟨_, hu₀, by simp⟩, by rw [CellU.wit_immOf]; exact hwβ⟩]
    exact CellU.immOf_congr rfl (by simp) (by simp) _ _
  rw [hcanon]
  have hSw' : vShape S (r.δ.extend x β) u w := by
    rw [vShape_congr S (δ₂ := r.δ.extend x₀ β₀) (fun y hy => by
      rw [find?_extend_ne _ _ (fun e => hx (by subst e; exact hy)),
        find?_extend_ne _ _ (fun e => hx₀ (by subst e; exact hy))])]
    exact hSw
  refine ⟨β, ?_, ℓ, pure_sep_mk hv ⟨LSet.singleton β, u, w, hwβ, rfl, hSw', le_refl _⟩⟩
  simp [BoCa.Lifetime.Life.interp, find?_extend_self]
  rfl

end BoCa.Fig16.LogRel.Core.Chain.SI

end
