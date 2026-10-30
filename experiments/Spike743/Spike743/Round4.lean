import Core.PinLaw
import Core.DivReify

/-!
# Spike743 — round 4: W-tick under `reify`

* `cC_tick_iff_cwp`: the relation at a row `tick, Σ` is `cwp` at its table. `PinStopTick`
  concludes `SemC` at `CTy.effOf S (Ref T ⊗ B)` with `S` in `Row.ResumeOT`; at `S = tick :: Σ` that
  is this `cwp`.
* `reify_of_tickC`: a computation in the relation at `tick, Σ` (answering `B ⊕ R`) is what
  `reify_compat` consumes: `reify`'s handler answers a loop value of `𝒱⟦U(Loop_Σ B R)⟧`. Together
  with `fundamentalC_pin` (the `lendRT` case is `PinLaw.tick`; the `reify` case is
  `reify_compatX`), a W-tick lend whose computation is reified is covered by `PinStopTick` as
  stated: no new field.
* `resumeOT_tick_await_reify`: the side conditions of the two rules hold together at
  `tick, await`: `Row.ResumeOT` (the lend) and `Σ = [await]` free of `Div`'s name (`reify`).
* `ext_adds_record_below_cell`: `Ext` from a share that holds a `mut` borrow cell at `α` admits a
  list with one more record at any lifetime no longer than `α`, so not `SameMem`. A stopped
  W-tick lend's continuation, stored in a reified loop, holds its view's cell; the consumer may
  resume it at such a list. The same-lifetime route (`frameAt`, class 1's) asks for `SameMem`
  (`SuspSpike.ext_adds_record`, at the empty share): the cell does not restore it.

Nothing here is a proof of `PinStopTick`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Spike743.Round4
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- The relation at a row holding `tick` is `cwp` at its table. -/
theorem cC_tick_iff_cwp (S : Row) (A : VTy) (ls : List SRec) (δ : LSub) (e : Expr) (ρ : WRes) :
    cC (CTy.effOf (tickSig :: S) A) ls δ e ρ ↔
      cwp (Row.tab (tickSig :: S) δ) (fun ls v => vC true A ls δ v) ls e ρ := by
  rw [cC_effOf_wp, Row.divB_tick]
  rfl

/-- **The relation at `tick, Σ` is `reify`'s input.** A computation in `𝒞⟦F_{tick, Σ}(B ⊕ R)⟧`
(the conclusion of `PinStopTick` at `tick :: Σ`, its answer mapped to `B ⊕ R`) is made by
`reify`'s handler a loop value of `𝒱⟦U(Loop_Σ B R)⟧`. -/
theorem reify_of_tickC {S : Row} (hS : ∀ o ∈ S, o.n ≠ divEff) {B R : VTy} (res : Val)
    (hres : closedAt 0 res.1 = true) {δ : LSub}
    (hresR : ∀ ls b ρ, vC true B ls δ b ρ →
      ewpTS ls (.app (.val res) (.val b)) (opTable (Row.tab S δ)) (fun ls v => vC true R ls δ v) ρ)
    {ls : List SRec} {M : Expr} {ρ : WRes}
    (h : cC (CTy.effOf (tickSig :: S) (.sum B R)) ls δ M ρ) :
    ewpTS ls (.app (.val (rkV res)) (BoCa.BoLo.hndE (reifyH res) M)) (opTable (Row.tab S δ))
      (fun ls v => vC true (.thunk (CTy.loopEff S B R)) ls δ v) ρ :=
  reify_compat hS res hres hresR ((cC_tick_iff_cwp S _ ls δ M ρ).mp h)

/-- The rows of a W-tick lend and of `reify` at once: `tick, await` is in `Row.ResumeOT`, and
`[await]` is free of `Div`'s name. -/
theorem resumeOT_tick_await_reify (x : LifeVar) :
    Row.ResumeOT (tickSig :: [pinAwaitSig]) x ∧ ∀ o ∈ [pinAwaitSig], o.n ≠ divEff := by
  refine ⟨fun o ho => ?_, fun o ho => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl
    · exact .inl rfl
    · exact .inr (resumeO_await_yield x pinAwaitSig (by simp))
  · simp only [List.mem_singleton] at ho
    subst ho
    decide

/-- `ℓ ↦ mut(α, v, ∅, ⊤)`: a `mut` borrow cell at `α` with an empty payload. -/
def mutCellAt (l : Loc) (α : Life) (v : Val) : WRes :=
  ResU.single l (CellU.mutOf α v PMap.empty (ResU.inStratum_empty α) (fun _ _ => True) trivial)

/-- A borrow cell of `mutCellAt l α v` is at `α`. -/
theorem cellIn_mutCellAt {l : Loc} {α b : Life} {v : Val} (h : CellIn (mutCellAt l α v) b) :
    α ⊑ b := by
  obtain ⟨m, ψ, hg, -, hle⟩ := h
  by_cases hm : m = l
  · subst hm
    rw [mutCellAt, ResU.single_get_self] at hg
    cases Option.some.inj hg
    simpa [CellU.mutOf, CellU.at] using hle
  · rw [mutCellAt, ResU.single_get_ne _ hm] at hg
    cases hg

/-- **`Ext` adds a record below a held `mut` cell.** From a share holding a `mut` borrow cell at
`α`, a list with one more record at `β ⊑ α` is an `Ext`-extension, and its members are not the
empty list's. -/
theorem ext_adds_record_below_cell (l : Loc) (α β : Life) (v : Val) (r : FrameRec)
    (hβ : β ⊑ α) :
    Ext [] [(r, β)] (mutCellAt l α v) ∧ ¬ ∀ x : SRec, x ∈ ([] : List SRec) ↔ x ∈ [(r, β)] := by
  refine ⟨⟨fun r' hr' _ => by simp [rsOf] at hr', fun b hb x hx => ?_⟩, fun h => ?_⟩
  · have hαb := cellIn_mutCellAt hb
    constructor
    · intro hm; simp at hm
    · intro hm
      rw [List.mem_singleton] at hm
      subst hm
      exact absurd (lt_of_le_of_lt hβ (lt_of_le_of_lt hαb hx)) (lt_irrefl _)
  · have := (h (r, β)).mpr (List.mem_singleton_self _)
    simp at this

end Spike743.Round4

end
