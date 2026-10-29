import SuspSpike.Depth
import Core.PinDerives

/-!
# SuspSpike — classes 2 and 3: what the routes need, machine-checked where it is a fact

**The open-cell route** (keep the lend open at a stop, §28's stop lemma with the cell held, the
one resume discharging it). `wpG`'s bracket is `↭` from a run's start to its end, and `↭` keeps
every borrow cell of the flattening, both ways (`[TR]` 5.27). A lend opened inside a run and open
at its stop is a `mut` cell at the end that was not at the start: no `↭` has it
(`not_upd_of_new_mut`, `openCellStop_false`). So this route changes the bracket: an invariant
beyond `↭`, a kill criterion of #645. It fires for this route, not for the classes.

**The same-lifetime route** (`frameAt`, class 1's) at a resumption of a stored `κ`. A stored
continuation is a value, and Core's relation of a value is stable along `Ext` (`vC_local`); the
resumption is owed at every `Ext`-extension of the stop's list. `frameAt` lends again at the old
lifetime only at a list with the stop's members (`SameMem`), because the cell it builds again stores
`𝒱⟦T⟧` read at the list (`QsAt_congr`). `Ext` does not give that: at a share holding no borrow cell
it admits a list with one more record, at any lifetime (`ext_adds_record`). The frame's share after
the stop holds the owner and the frozen rest, in `Res_α`; nothing in it pins the records above `α`.
That `frameAt` does not apply is shown; that no proof of class 2 exists is not claimed, and no
obstruction to class 2 itself is verified.

**R1 and `PinLaw`.** R1's row condition `Row.ResumeO` asks every operation to answer `1`; `tick`
answers `Next`, so a lend across `tick` (B2's pending programs, #644) is outside R1 today
(`not_resumeO_tick`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace SuspSpike
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### The open-cell route -/

/-- A `mut` cell in the flattening at the end of an update that was not at its start breaks `↭`
(`[TR]` 5.27's `mut` clause). The same fact as `LoopBorrow.not_upd_of_new_mut`. -/
theorem not_upd_of_new_mut {ρ π : WRes} {l : Loc} {b : Life} {P : Val → SPropS Loc Val b}
    {v : Val} {χ : WRes} {h : χ.InStratum b} {hw : P v ⟨χ, h⟩}
    (hπ : π.FlatAt l (CellU.mutOf b v χ h P hw))
    (hρ : ∀ (v' : Val) (χ' : WRes) (h' : χ'.InStratum b) (hw' : P v' ⟨χ', h'⟩),
      ¬ ρ.FlatAt l (CellU.mutOf b v' χ' h' P hw')) :
    ¬ ResU.Upd ρ π := by
  intro hu
  obtain ⟨v', χ', h', hw', hf⟩ := (hu.2 l b P).mpr ⟨v, χ, h, hw, hπ⟩
  exact hρ v' χ' h' hw' hf

/-- What the open-cell route asks of a run: an update from a start with no lend of `ℓ` at `b` to
an end that holds one. -/
def OpenCellStop : Prop :=
  ∃ (ρ π : WRes) (l : Loc) (b : Life) (P : Val → SPropS Loc Val b) (v : Val) (χ : WRes)
    (h : χ.InStratum b) (hw : P v ⟨χ, h⟩),
    (∀ (v' : Val) (χ' : WRes) (h' : χ'.InStratum b) (hw' : P v' ⟨χ', h'⟩),
      ¬ ρ.FlatAt l (CellU.mutOf b v' χ' h' P hw')) ∧
    π.FlatAt l (CellU.mutOf b v χ h P hw) ∧ ResU.Upd ρ π

/-- **The open-cell route is outside `↭`.** -/
theorem openCellStop_false : ¬ OpenCellStop := by
  rintro ⟨ρ, π, l, b, P, v, χ, h, hw, hρ, hπ, hu⟩
  exact not_upd_of_new_mut hπ hρ hu

/-! ### The same-lifetime route at an `Ext`-extension -/

/-- **`Ext` adds records that `SameMem` does not.** At a share with no borrow cell, a list with
one more record, at any lifetime, is an `Ext`-extension. -/
theorem ext_adds_record (r : FrameRec) (β : Life) :
    Ext [] [(r, β)] PMap.empty ∧ ¬ SameMem [] [(r, β)] := by
  refine ⟨ext_empty' [] [(r, β)], fun h => ?_⟩
  have := (h (r, β)).mp (List.mem_singleton.mpr rfl)
  simp at this

/-- What class 2 asks of a resumption, for the same-lifetime route: the list it is resumed at has
the members of the stop's. A stored continuation is owed at every `Ext`-extension instead. -/
def ScopedResumption (ls ls' : List SRec) : Prop := SameMem ls ls'

/-! ### R1 -/

/-- **`tick` is outside R1's rows**: it answers `Next`, not `1`. -/
theorem not_resumeO_tick (x : LifeVar) : ¬ Row.ResumeO [tickSig] x := by
  intro h
  have := (h tickSig (by simp)).2.2.2.1
  simp [tickSig, nextTy] at this

end SuspSpike

end
