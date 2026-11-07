import Core.Chain.HandleT835N

/-!
# `[handle-last]`: a clause that uses `κ` once, last  `[spec §14, §19, §27, §51]`

Core's `handleL_compatC` (`Core/DivHandleLast.lean`), its proof `ewp_handle_last` (the last
instance, `scope-831-interface.md` §10.5), is read at `SemJN` in `HandleLKW835N`
(`worksTy_atN`, `exitsTy_atN`, `erwp_handle_last`, `handleL_compatN`). This file holds two of its
steps: `lastClause_steps_body` (a last clause's steps after its `β` step) and `capB_of_entN` (a
row entry's capture flag). The finaliser frame's answer (Core's `last_cont`): `inl y` resumes `κ`
at `y`, `inr z` cancels `κ` at the table of its cancel row under the exit's frame
(`erwp_frame_plain_or`), then runs the exit at `z`. The clause pays its `β` step, so the work's
run, the finaliser and the frame's answer are all below the stop's index, where `κ` is owed.

As at `[handle]` with tail clauses (`Core/Chain/HandleT835N.lean`), the works and the exits are read
at the view from consistent resources: the payload at the handler's name (`erwp_consistentPA`), the
work's value across its resumptions (`erwp_consistentAns`), and the exit's argument, a part of
that value. `κ`'s cancel branch gets the table of the operation's own cancel row (Core's `lastTc`),
the entry's cancel obligation itself (`OpTabN.Sub`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel (substAll)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Head Kont performE raiseE cancelVal opPayload hndE hndVal clauseAt capTag)

/-! ### The works and the exits -/

/-- The steps of a clause at `(v, κ)` after its `β` step (Core's `lastClause_steps` without its
first step): to the work under the finaliser frame. -/
theorem lastClause_steps_body (j : Nat) (vc vn g v κ : Val)
    (hg : PureSteps (pickE j (.val vc)) (.val g)) :
    PureSteps (Expr.subst 0 (Val.pair v κ) (.letpair (.var 0)
      (thenE
        (.case (.var 0)
          (.app (.app (.var 2) (.val (Val.inj₁ .unit))) (.var 0))
          (.app (.val (.lam (.app (pickE j ((Expr.val vn).shift 6 0)) (.var 1))))
            (.app (.var 2) (.val (Val.inj₂ .unit)))))
        (.app (.var 1) (.val (Val.inj₂ .unit)))
        (.app (pickE j ((Expr.val vc).shift 3 0)) (.var 1)))))
      ((ubindK (lastN j κ vn) (lastD κ)).plug (.app (.val g) (.val v))) := by
  refine (PureSteps.head (fun μ => Head.letpair μ v κ _) rfl).trans ?_
  have e : ((Expr.subst 2 ((Val.pair v κ).shift 2 0) (thenE
      (.case (.var 0)
        (.app (.app (.var 2) (.val (Val.inj₁ .unit))) (.var 0))
        (.app (.val (.lam (.app (pickE j ((Expr.val vn).shift 6 0)) (.var 1))))
          (.app (.var 2) (.val (Val.inj₂ .unit)))))
      (.app (.var 1) (.val (Val.inj₂ .unit)))
      (.app (pickE j ((Expr.val vc).shift 3 0)) (.var 1)))).subst 0 (κ.shift 1 0)).subst 0 v =
      (ubindK (lastN j κ vn) (lastD κ)).plug (.app (pickE j (.val vc)) (.val v)) := by
    simp [thenE, pickE_subst, lastN, lastD, Kont.plug, subst_shift_succ, Val.pair, Val.lam,
      Val.inj₁, Val.inj₂, Val.unit, Val.prim, Expr.subst, Val.val_shift, Expr.shift_shift,
      Expr.shift_zero]
  rw [e]
  have := PureSteps.plug ((ubindK (lastN j κ vn) (lastD κ)).comp (.appL .hole v)) hg
  rw [Kont.plug_comp, Kont.plug_comp] at this
  exact this

/-- A non-abortive entry that is not `lin` is capturable. -/
theorem capB_of_entN {q : Qual} {B : VTy} (ha : (B.isZero && q != .lin) = false) (hq : q ≠ .lin) :
    capB q B = true := by
  simp only [Bool.and_eq_false_iff, bne_eq_false_iff_eq] at ha
  simp only [capB, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true']
  rcases ha with ha | ha
  · exact ⟨hq, ha⟩
  · exact absurd ha hq

section
variable {δ : LSub} {Θ : LocTy} {c : Loc → Option Life}

end

section
variable {δ : LSub} {Θ : LocTy} {c : Loc → Option Life} {S SW : Row}
  {E : List (Qual × VTy × VTy)} {fs : Nat → CTy} {Xs : Nat → VTy} {n : UInt32} {A R : VTy}

end

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
