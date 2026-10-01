import SecondClass.Restated
import Core.EffPrograms

/-!
# SecondClass — an abortive clause that captures, as a derived rule

#216: §19's `[handle]` types every clause `!` (`clausesTy`), so a clause captures only `!`
values. For an **abortive** operation (answer `0`, a qualifier with weakening) the clause never
receives `κ` and runs at most once, in place of the handler, after the body has been abandoned
(`[unwind]`: `hnd (n, H) K[raise (n, v)] ↦ h_op v`). So its captures need not be inside the
handler at all: the handler can answer the error as data, and the clause can run after it.

    handle_n e with { return x ⇒ N_v ; op v ⇒ N_e }      (N_v, N_e over the captures Γc)
      ≜  r ← handle_n e with (λx. inj₁ x, λv. inj₂ v);  case r { inj₁ x ⇒ N_v | inj₂ v ⇒ N_e }

`d_handleAbortCapture` types it. The captures `Γc` are any context: owned values, borrows,
capabilities. The return clause and the operation clause share them additively (`sumE`), as an
affine clause should (#216's table: "at most once"). The side conditions are `[let]`'s on
`Γc` (`effLet`): if the outer row `Σ` has weakening, the captures must drop when an outer
operation abandons them; if it has an unrestricted operation, they must be persistent. Those are
the conditions a native rule would need too, because the captures sit in the handler's frame,
which an outer continuation captures.

It is a derived rule: no kernel change, and soundness is `fundamentalC`. `probes/p4-clause-captures.bc`
part (b) is an instance, typed by the checker and run.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.SecondClass
open BoCa
open BoCa.Fig16
open BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- The one abortive operation `op : Ae ↠^aff 0`. -/
abbrev Eab (Ae : VTy) : List (Qual × VTy × VTy) := [(.aff, Ae, .zero)]

/-- The return clause `λx. inj₁ x`. -/
def hrInl : Expr := .val (.lam (.inj₁ (.var 0)))

/-- The operation clause `λv. inj₂ v`. -/
def clsInr : Expr := .pair (.val (.lam (.inj₂ (.var 0)))) (.val .unit)

/-- `handle_n e` with the answer as data, `A ⊕ Ae`. -/
def toSumAt (n : UInt32) (e : Expr) : Expr := bindE clsInr (bindE hrInl (hndTerm n 0 1 e))

/-- The handler with capturing clauses: `r ← toSumAt n e; case r { N_v | N_e }`. -/
def handleAbortCapture (n : UInt32) (e Nv Ne : Expr) : Expr :=
  .app (.val (.lam (.case (.var 0) Nv Ne))) (toSumAt n e)

theorem d_hrInl {Δ : LifeCtx} {Γ : Ctx VTy} {S : Row} {A Ae : VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ hrInl (.val (retTy S A (.sum A Ae))) :=
  .bangThunkV (dead_noLive hΓ) rfl
    (.lam (.effSub (S := []) (fun _ _ _ h => by simp [Row.find] at h)
      (.ret (.sumI₁ (.var (.here hΓ.toP))))))

theorem d_clsInr {Δ : LifeCtx} {Γ : Ctx VTy} {S : Row} {A Ae : VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ clsInr (.val (clausesTy S (.sum A Ae) (Eab Ae))) :=
  .tensorI (deadSplit hΓ)
    (.bangThunkV (dead_noLive hΓ) rfl
      (.lam (.effSub (S := []) (fun _ _ _ h => by simp [Row.find] at h)
        (.ret (.sumI₂ (.var (.here hΓ.toP)))))))
    (.unitI hΓ.toP)

/-- **The abortive handler with capturing clauses, derived.** -/
theorem d_handleAbortCapture {Δ : LifeCtx} {Γ Γb Γc : Ctx VTy} {S : Row} {A Ae R : VTy}
    {n : UInt32} {e Nv Ne : Expr}
    (hs : Ctx.SplitP Γ Γb Γc) (hn0 : n ≠ 0) (hnS : ∀ o ∈ S, o.n ≠ n)
    (hW : S.Weak → Γc.Drops) (hU : S.Unr → Persistent Γc)
    (he : CDerives Δ (⟨retTy S A (.sum A Ae), false⟩ ::
        ⟨clausesTy S (.sum A Ae) (Eab Ae), false⟩ :: Γb)
      e (.comp (CTy.effOf (Row.ofEff n (Eab Ae) 0 ++ S) A)))
    (hv : CDerives Δ (⟨A, true⟩ :: ⟨.sum A Ae, false⟩ :: Γc) Nv (.comp (CTy.effOf S R)))
    (hE : CDerives Δ (⟨Ae, true⟩ :: ⟨.sum A Ae, false⟩ :: Γc) Ne (.comp (CTy.effOf S R))) :
    CDerives Δ Γ (handleAbortCapture n e Nv Ne) (.comp (CTy.effOf S R)) := by
  refine .effLet (A := .sum A Ae) hs hW hU ?_ ?_
  · refine .bind (split_kill Γb).toP (.ret (d_clsInr (S := S) (A := A) (Ae := Ae) (kill_dead Γb))) ?_
    refine .bind (.right (split_kill Γb).toP)
      (.ret (d_hrInl (S := S) (A := A) (Ae := Ae) (.cons (kill_dead Γb)))) ?_
    exact .effHandle (E := Eab Ae) (.left (.left (split_kill Γb).toP))
      (.left (.right (deadSplit (kill_dead Γb)))) (.here (.cons (kill_dead Γb).toP))
      (.there (.here (kill_dead Γb).toP)) hn0 hnS (by simp) he
  · exact .sumE (.left (split_kill Γc).toP) (.var (.here (kill_dead Γc).toP)) hv hE

/-- At a pure outer row the side conditions are vacuous: the clauses capture any context. -/
theorem d_handleAbortCapture_pure {Δ : LifeCtx} {Γ Γb Γc : Ctx VTy} {A Ae R : VTy}
    {n : UInt32} {e Nv Ne : Expr} (hs : Ctx.SplitP Γ Γb Γc) (hn0 : n ≠ 0)
    (he : CDerives Δ (⟨retTy [] A (.sum A Ae), false⟩ ::
        ⟨clausesTy [] (.sum A Ae) (Eab Ae), false⟩ :: Γb)
      e (.comp (CTy.effOf (Row.ofEff n (Eab Ae) 0 ++ []) A)))
    (hv : CDerives Δ (⟨A, true⟩ :: ⟨.sum A Ae, false⟩ :: Γc) Nv (.comp (.ret R)))
    (hE : CDerives Δ (⟨Ae, true⟩ :: ⟨.sum A Ae, false⟩ :: Γc) Ne (.comp (.ret R))) :
    CDerives Δ Γ (handleAbortCapture n e Nv Ne) (.comp (.ret R)) :=
  d_handleAbortCapture (S := []) hs hn0 (by simp) (fun ⟨_, h, _⟩ => by simp at h)
    (fun ⟨_, h, _⟩ => by simp at h) he hv hE

/-- Its soundness, by `fundamentalC`. -/
theorem handleAbortCapture_sem {Δ : LifeCtx} {Γ Γb Γc : Ctx VTy} {S : Row} {A Ae R : VTy}
    {n : UInt32} {e Nv Ne : Expr}
    (hs : Ctx.SplitP Γ Γb Γc) (hn0 : n ≠ 0) (hnS : ∀ o ∈ S, o.n ≠ n)
    (hW : S.Weak → Γc.Drops) (hU : S.Unr → Persistent Γc)
    (he : CDerives Δ (⟨retTy S A (.sum A Ae), false⟩ ::
        ⟨clausesTy S (.sum A Ae) (Eab Ae), false⟩ :: Γb)
      e (.comp (CTy.effOf (Row.ofEff n (Eab Ae) 0 ++ S) A)))
    (hv : CDerives Δ (⟨A, true⟩ :: ⟨.sum A Ae, false⟩ :: Γc) Nv (.comp (CTy.effOf S R)))
    (hE : CDerives Δ (⟨Ae, true⟩ :: ⟨.sum A Ae, false⟩ :: Γc) Ne (.comp (CTy.effOf S R))) :
    SemC Δ Γ (handleAbortCapture n e Nv Ne) (CTy.effOf S R) :=
  fundamentalC (d_handleAbortCapture hs hn0 hnS hW hU he hv hE)

end BoCa.Fig16.LogRel.Core.SecondClass
