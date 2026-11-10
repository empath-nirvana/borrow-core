import LicUpd.Absorb
import Core.Invariant

/-!
# LicUpd — G1ᵐ: a `Mut` getter (`&mut self -> &mut T`)

**The configuration.**
- The start is the parent `0 ↦ mut(b, v, ρw, P̂)`, with `ρw(1) = own(u)`: a `Mut 'a` view of a
  record whose field is at `1`.
- A `Mut 'a` getter would end holding a top-level `1 ↦ mut(b′, u′, χ′, Q̂)`.

**The result: G1ᵐ fails as an exemption.**
1. `g1m_coexist_invalid`: no valid resource holds both the parent, with a witness that still
   owns `1`, and a top-level `mut` cell at `1`. `ex` walks the parent's witness and finds
   `own(u)` at `1`, and the view's `mut` cell is in `ex` too, at the same location.
2. `g1m_parent_kept`: G1 keeps `↭`'s `mut` clause (`UpdLic.updMut`). Every `mut` cell
   `mut(b, _, _, P̂)` of the start's flattening has one at the same location, lifetime and
   predicate in the end's flattening. So the parent survives with its own `P̂`.
3. `k4_refused`: `P̂` cannot change either.

So the parent survives with `P̂` and, by 1, at a witness that does not own `1`: `P̂` must hold
of a witness without the field. A typed `P̂` (`𝒱⟦Ref T⟧`) does not hold there.
- A `mut` view is exclusive. It cannot sit beside the parent as a derivable copy, as an `imm`
  image can.
- A `Mut` getter has to move the parent's authority over `1` to the view. No exemption on
  `↭`'s end→start direction expresses that. It would need the start→end direction exempted at
  the parent, which is the predicate change K4 shows is unsafe.

**Stop:** the G1 design does not extend to `Mut` projections.
-/

noncomputable section

namespace BoCa.Fig16.LicUpd
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core

/-- **G1ᵐ, coexistence.** A resource holding the parent `0 ↦ mut(b, v, ρw, P̂)` with
`ρw(1) = own(u)`, and a top-level `mut` view at `1`, has no flattening. -/
theorem g1m_coexist_invalid {b b' : Life} {v u u' : Val} {ρw χ' : WRes}
    {hρ : ρw.InStratum b} {h' : χ'.InStratum b'}
    {P : Val → SPropS Loc Val b} {Q : Val → SPropS Loc Val b'}
    {hP : P v ⟨ρw, hρ⟩} {hQ : Q u' ⟨χ', h'⟩}
    (hw1 : ρw.get 1 = some (CellU.ownOf u)) {π : WRes}
    (h0 : π.get 0 = some (CellU.mutOf b v ρw hρ P hP))
    (h1 : π.get 1 = some (CellU.mutOf b' u' χ' h' Q hQ)) : ¬ ResU.Valid π := by
  rintro ⟨σ, e, a, hex, -, -⟩
  have hpath : XPath π [0] ρw := by
    have := XPath.cons (p := []) h0 (by simp) (XPath.nil _)
    simpa using this
  have hown := xpath_ex hex hpath hw1 (by simp)
  have hmut := ExS.get_of_ne_imm hex h1 (by simp)
  rw [hown] at hmut
  exact CellU.ownOf_ne_mutOf (Option.some.inj hmut)

/-- **G1ᵐ, the parent survives.** Under G1, a `mut` cell `mut(b, _, _, P̂)` in the start's
flattening at `l` has one in the end's flattening at `l`, with the same `b` and `P̂`.
G1 relaxes only the `imm` clause. -/
theorem g1m_parent_kept {ρ π : WRes} (h : UpdLic ρ π) {l : Loc} {b : Life} {v : Val}
    {χ : WRes} {hχ : χ.InStratum b} {P : Val → SPropS Loc Val b} {hP : P v ⟨χ, hχ⟩}
    (hf : ρ.FlatAt l (CellU.mutOf b v χ hχ P hP)) :
    ∃ (v' : Val) (χ' : WRes) (h' : χ'.InStratum b) (hw' : P v' ⟨χ', h'⟩),
      π.FlatAt l (CellU.mutOf b v' χ' h' P hw') :=
  (h.updMut l b P).mp ⟨v, χ, hχ, hP, hf⟩

end BoCa.Fig16.LicUpd

end
