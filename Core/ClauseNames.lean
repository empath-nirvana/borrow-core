import Core.ClauseKinds
import Core.EffCancelTyped

/-!
# Core — the clause's names, unhandled in the continuation  `[spec §19]`

A tail-resumptive clause lowers to a direct call at the `perform` (`docs/effect-lowering.md`
§2.3): its work `M` then runs inside the continuation `K` between the `perform` and its handler,
where by H-op it runs outside `K`. That is the law only when what `M` performs or raises reaches
the same frames from both places: no frame of `K` catches an operation or a raise of any name `M`
may perform (§2.3's condition 2). The names `M` may perform are bounded by its row's, the
handler's outer row `Σ` (`clauseTy`), and, where the clause runs only code it holds, by the names
its own code performs or raises (`Core/ClauseOwn.lean`, `UnhandledNames`), over which condition 2
is stated.

* `UnhandledIn Σ K` states the condition: no frame of `K` catches a name of `Σ` (`Kont.Catches`,
  which holds at every handler frame of the name, `catches_of_hasHnd`, and at every finaliser).
* The rows decide it when `Σ` is empty (`unhandledIn_nil`).
* Otherwise they do not (`unhandled_not_decided`): one `[handle]` node, at the same name, row,
  operations, cancel rows and types, with the same tail-resumptive clause, over two handled
  computations at the same row, the operation performed in the hole of `K`: in one `K` is empty,
  and in the other `K` holds a handler of the name `2` of `Σ`.

What decides it is the frames `K` may hold: those of the handled computation and of the code that
flows into it. `Core/HandledNames.lean` records them (`Expr.hin`, `flows`), with the run invariant
that every handler frame a run reaches is one of a `handle` node's of the program
(`steps_frame_of_node`) and the theorem that a row none of whose names `flows` may catch is
unhandled in every `K` a run reaches (`steps_unhandledIn`).
-/

namespace BoCa.Fig16.LogRel.Core.ClauseKinds
open BoCa
open BoCa.Fig16
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.CancelIntercept
open BoCa.BoLo (Kont hndE performE opPayload)
open BoCa.Lifetime (LifeCtx)

/-- **The names of `Σ` are unhandled in `K`**: no frame of `K` catches an operation or a raise of a
name of `Σ`.  `[spec §19]` -/
def UnhandledIn (S : Row) (K : Kont) : Prop := ∀ o ∈ S, K.Catches o.n = false

/-- A handler frame of a name catches its raises. -/
theorem catches_of_hasHnd {n : UInt32} : ∀ {K : Kont}, K.HasHnd n = true → K.Catches n = true
  | .hole, h => by simp [Kont.HasHnd] at h
  | .pairL K _, h | .pairR _ K, h | .letpair K _, h | .case K _ _, h | .appL K _, h | .seq K _, h
  | .inj₁ K, h | .inj₂ K, h => by
      simp only [Kont.HasHnd, Kont.Catches] at h ⊢; exact catches_of_hasHnd h
  | .appR f K, h => by
      simp only [Kont.HasHnd, Kont.Catches, Bool.or_eq_true] at h ⊢
      rcases h with h | h
      · left; split at h <;> simp_all
      · right; exact catches_of_hasHnd h

/-- Unhandled in `K`, a name of `Σ` has no handler frame there: its `perform` passes `K`. -/
theorem UnhandledIn.hasHnd {S : Row} {K : Kont} (h : UnhandledIn S K) {o : OpSig} (ho : o ∈ S) :
    K.HasHnd o.n = false := by
  cases hK : K.HasHnd o.n
  · rfl
  · exact absurd (catches_of_hasHnd hK) (by simp [h o ho])

/-- **The rows decide it at an empty row**: a clause that performs nothing is unhandled
everywhere. -/
theorem unhandledIn_nil (K : Kont) : UnhandledIn [] K := fun _ h => absurd h (by simp)

/-- The handler of the name `1` of `unhandled_not_decided`, its operation at `1?`: the answer clause
`λx. x` and the clause `λ(x, κ). κ.1 x`, which resumes in tail position. -/
def hRes : Val := hA 1 idV resumeC

/-- The clause `λ(x, κ). κ.1 x` meets the `tail` kind's premise: its resume in tail position. -/
theorem resumeC_tail : ClauseKind.tail.Premise (.opt, .unit, .unit) resumeC.1 := by
  refine ⟨rfl, _, rfl, ?_⟩
  exact ⟨_, .resume (by simp [mentions])⟩

theorem d_hRes_clauses {Δ : LifeCtx} :
    CDerives Δ [] (.pair (.val idV) (.pair (.val resumeC) (.val Val.unit)))
      (.val (.tensor (retTy [rSig 2] .unit .unit)
        (clausesTy [rSig 2] .unit [(.opt, .unit, .unit)] (fun _ => finR 2)))) :=
  .tensorI .nil (d_idV _ .unit) (.tensorI .nil (d_resumeC _ _ _) (.unitI .nil))

/-- `perform (1, (0, ()))`, at the handled row of `hRes`: `{1⟨{2}⟩, 2}`. -/
theorem d_perform₁ {Δ : LifeCtx} :
    CDerives Δ [] (Kont.hole.plug (performU 1))
      (.comp (CTy.effOf [pSig 1 (finR 2), rSig 2] .unit)) := by
  refine .effSub (RowLe.of_mem fun o ho => ?_)
    (.effPerform (S := [pSig 1 (.ret .unit)]) (o := pSig 1 (.ret .unit)) rfl rfl (.unitI .nil))
  simp only [List.mem_singleton] at ho
  subst ho
  refine ⟨pSig 1 (finR 2), rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ => ?_⟩
  exact (finLe_iff _ _).mpr (Or.inr ⟨rfl, RowLe.nil _⟩)

/-- `hnd (2, H₂) (perform 1 then x. x unwind raise 2)`, at the handled row of `hRes`. -/
theorem d_inner₁ {Δ : LifeCtx} :
    CDerives Δ [] ((KT 2).plug (performU 1)) (.comp (CTy.effOf [pSig 1 (finR 2), rSig 2] .unit)) := by
  refine .effSub (RowLe.of_mem fun o ho => ?_) d_inner₂
  simp only [List.mem_singleton] at ho
  subst ho
  exact ⟨pSig 1 (finR 2), rfl, OpSig.LeF.refl _⟩

/-- `hRes`'s `[handle]` over a handled computation `e` at its handled row: the node at the name
`1`, the outer row `{2}`, the operation `1 ↠^{1?} 1` at the cancel row `{2}`, the types `1`. -/
theorem d_hRes {Δ : LifeCtx} {e : Expr}
    (he : CDerives Δ [] e (.comp (CTy.effOf [pSig 1 (finR 2), rSig 2] .unit))) :
    CDerives Δ [] (hndE hRes e) (.comp (CTy.effOf [rSig 2] .unit)) :=
  .effHandleV (Γ₁ := []) (Γ₂ := []) (E := [(.opt, .unit, .unit)]) (fs := fun _ => finR 2)
    .nil .nil (.pair (.val _) (.pair (.val _) (.val _))) d_hRes_clauses
    (by decide) (by simp [rSig]) (by simp) rfl he

/-- **The rows do not decide that the clause's names are unhandled in `K`.** One `[handle]` node,
the same tail-resumptive clause (`resumeC_tail`) at the same row `Σ = {2}`, over two handled
computations at the same row, each the operation `perform 1` in the hole of a continuation `K`:
both programs are typed, and the name `2` of `Σ` is unhandled in the one `K` (empty) and handled
in the other (`hnd 2 …`).  `[spec §19]` -/
theorem unhandled_not_decided {Δ : LifeCtx} :
    ClauseKind.tail.Premise (.opt, .unit, .unit) resumeC.1 ∧
    CDerives Δ [] (hndE hRes (Kont.hole.plug (performU 1))) (.comp (CTy.effOf [rSig 2] .unit)) ∧
    CDerives Δ [] (hndE hRes ((KT 2).plug (performU 1))) (.comp (CTy.effOf [rSig 2] .unit)) ∧
    UnhandledIn [rSig 2] Kont.hole ∧ ¬ UnhandledIn [rSig 2] (KT 2) := by
  refine ⟨resumeC_tail, d_hRes d_perform₁, d_hRes d_inner₁, fun _ _ => rfl, fun h => ?_⟩
  have := h (rSig 2) (by simp)
  revert this
  decide

end BoCa.Fig16.LogRel.Core.ClauseKinds
