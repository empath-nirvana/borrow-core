import Core.EffMachine
import Core.Closed
import Core.Totality

/-!
# Core — effect safety: a typed program's run never sticks  `[spec §19]`

A typed closed program is a derivation `CDerives LifeCtx.empty [] e (.comp (.ret A))`: a
computation of `F A`, whose row is empty, so each operation it performs and each raise it makes
is handled inside it.  Its runs are the machine's (`Steps`) from the empty memory.

* **Effect safety** (`effSafe_closed`): every configuration a run reaches is a value or steps, and
  is no operation that no live frame catches: not `K[perform p]` with `K` free of a handler of
  `p`'s name, nor `K[raise p]` with `K` catching nothing of it.  Every run continues to a value
  (`total_every_run`), and an operation whose context catches nothing of it is not a value and
  takes no step (`ne_opPlug_of_goes`, from `opPlug_no_step`).  At `F 1` the first half is
  `adequacyD_safe`.
* **`LiveOK`** (`liveOK_closed`): every configuration a run reaches has a closed term and closed
  stored values (`closedAt_of_derives`, `closed_steps`), and goes on: it is a value or steps.  So
  it holds no stuck redex at an evaluation position (`LiveOK.not_stuck`).

A program whose row is not empty may stop at an operation of its row; these theorems are at the
empty row.  Leak freedom at a persistent answer is `leakFree_closed` (`Core/EffPrograms.lean`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.BoLo (Heap Steps Step1 Kont)
open BoCa.Lifetime (LifeCtx)

/-- **A configuration that goes on is no operation its context catches nothing of**: a value, or a
term that steps, is not `K[perform p]` with `K` free of `p`'s name, nor `K[raise p]` with `K`
catching nothing of it.  `[spec §19]` -/
theorem ne_opPlug_of_goes {μ : Heap} {e : Expr} (hgo : IsVal e ∨ ∃ μ' e', Step1 (ℍ := ℍ) μ e μ' e')
    {K : Kont} {r : Bool} {p : Val} {n : UInt32} (hn : payloadName p = some n)
    (hK : OpFree r n K) : e ≠ K.plug (opE r p) := by
  rintro rfl
  rcases hgo with hv | ⟨μ', e', hst⟩
  · exact opE_not_isVal r p (K.isVal_of_plug hv)
  · exact opPlug_no_step hn hK hst

/-- **Effect safety**: every configuration a typed closed program reaches from the empty memory is
a value or steps, and is no operation that no live frame catches: not `K[perform p]` with `K` free
of a handler of `p`'s name, nor `K[raise p]` with `K` catching nothing of it.  So every operation
such a run performs or raises has a live handler, and no run is stuck.  `[spec §19]` -/
theorem effSafe_closed {e : Expr} {A : VTy} (h : CDerives LifeCtx.empty [] e (.comp (.ret A)))
    {μ : Heap} {e' : Expr} (hs : Steps (ℍ := ℍ) Adequacy.emptyMem e μ e') :
    (IsVal e' ∨ ∃ μ₂ e₂, Step1 (ℍ := ℍ) μ e' μ₂ e₂) ∧
    ∀ (K : Kont) (r : Bool) (p : Val) (n : UInt32), payloadName p = some n → OpFree r n K →
      e' ≠ K.plug (opE r p) := by
  obtain ⟨μ', v, hv⟩ := total_every_run h hs
  have hgo : IsVal e' ∨ ∃ μ₂ e₂, Step1 (ℍ := ℍ) μ e' μ₂ e₂ := by
    cases hv with
    | refl => exact .inl v.2
    | more h _ => exact .inr ⟨_, _, h⟩
  exact ⟨hgo, fun K r p n hn hK => ne_opPlug_of_goes hgo hn hK⟩

/-- **`LiveOK`**: the configuration `(μ, e)` has a closed term and closed stored values, and
evaluation goes on from it: `e` is a value or steps.  `[spec §19]` -/
structure LiveOK (μ : Heap) (e : Expr) : Prop where
  closed : closedAt 0 e = true
  heap : HeapClosed μ
  goes : IsVal e ∨ ∃ μ' e', Step1 (ℍ := ℍ) μ e μ' e'

/-- **Every configuration a typed closed program reaches is `LiveOK`**: a typed term is closed
(`closedAt_of_derives`), a run keeps its term and its stored values closed (`closed_steps`), and
the run goes on (`effSafe_closed`).  `[spec §19]` -/
theorem liveOK_closed {e : Expr} {A : VTy} (h : CDerives LifeCtx.empty [] e (.comp (.ret A)))
    {μ : Heap} {e' : Expr} (hs : Steps (ℍ := ℍ) Adequacy.emptyMem e μ e') :
    LiveOK (ℍ := ℍ) μ e' :=
  have hc := closed_steps hs (closedAt_of_derives h) heapClosed_empty
  ⟨hc.1, hc.2, (effSafe_closed h hs).1⟩

/-- A `LiveOK` configuration is no operation its context catches nothing of. -/
theorem LiveOK.ne_opPlug {μ : Heap} {e : Expr} (hL : LiveOK (ℍ := ℍ) μ e) {K : Kont} {r : Bool}
    {p : Val} {n : UInt32} (hn : payloadName p = some n) (hK : OpFree r n K) :
    e ≠ K.plug (opE r p) :=
  ne_opPlug_of_goes hL.goes hn hK

/-- A `LiveOK` configuration holds no stuck redex at an evaluation position (`StuckAt`): `() ()`,
a must-resume `κ`'s cancel branch (`kappaC_cancel_lin`), among them. -/
theorem LiveOK.not_stuck {μ : Heap} {K : Kont} {s : Expr} (hL : LiveOK (ℍ := ℍ) μ (K.plug s))
    (hs : StuckAt (ℍ := ℍ) s) : False := by
  rcases hL.goes with hv | ⟨μ', e', hst⟩
  · exact hs.not_val (K.isVal_of_plug hv)
  · exact stuck_no_step hs K hst

end BoCa.Fig16.LogRel.Core

end
