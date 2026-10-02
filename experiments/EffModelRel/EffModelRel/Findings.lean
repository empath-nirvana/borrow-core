import EffModelRel.UnaryFP
import EffModelRel.Writers

/-!
# EffModelRel — the TR's three findings, refused by the judgement (`docs/effects-tr` §10)

Each program is one of the three that phase A's checker accepts and whose run goes wrong,
written in this calculus. Each run goes wrong here too (computed by `decide`), and so none of the
three is moded: a moded closed program answers (`safety_obs`). The refusal is therefore a
consequence of the fundamental property, not a separate check.

- **§10.1, a lent capability moved before the lend.** A thunk captured before the lend consumes
  the capability inside it; the lend's write-back finds no cell (`movedLend_stuck`). The owning
  lend makes the lend a second use of the capability (`movedLend_not_moded`).
- **§10.2, a frame-owned resource carried past its frame.** A stream escapes a `using` frame and
  its pull uses the resource after the frame freed it. With the handle an instance of `Res`, the
  late `use` is an operation nothing handles (`resEscape_obs`). A stream whose pull performs it
  must name the frame's instance in its row, and a type naming it cannot leave the frame (scope);
  as written, with an empty row on the stream, the thunk's row does not cover what it performs.
  Either way no derivation exists (`resEscape_not_moded`).
- **§10.3, a return clause run twice.** A handler whose return clause owns a capability, under a
  multi-shot operation resumed twice, consumes the capability twice (`retTwice_stuck`); the
  handler's own resuming qualifiers forbid the clause's capture (`retTwice_not_moded`).
-/

namespace EffRel

/-- A moded closed program is not stuck and does not end at an unhandled operation. -/
theorem not_moded_of_obs {g : G} {P : Prog σ g} (h : ∀ v, P.obs.out ≠ .ret v) :
    ¬ ∃ R : Row σ [], CM (Ψ := []) (Γ := []) VSet.none R P := fun ⟨_, hP⟩ =>
  let ⟨v, hv⟩ := safety_obs P hP; h v hv

/-! ## §10.1 -/

/-- `newcap c; t ← thunk(getcap c); lend c as x in (force t; inc x; ret 0)`, the capability
answered back and consumed. -/
def movedLend : Prog σ .int :=
  .bind (.newcap Eff.ctr .int coCtr (.int 0))
    (.bind (.ret (.thunk (b := Rw.nil) Mode.lin (.getcap v0)))
      (.bind (.lend v1 (.bind (.force v0) (.op .z Op.inc .unit (.ret (.int 0)))))
        (.split v0 (.bind (.getcap v1) (.ret v0)))))

theorem movedLend_stuck : movedLend.obs.out = .stuck := by decide

theorem movedLend_not_moded : ¬ ∃ R, CM (Ψ := []) (Γ := []) VSet.none R movedLend :=
  not_moded_of_obs (fun v h => by rw [movedLend_stuck] at h; cases h)

/-! ## §10.2 -/

abbrev tIStep : VTy σ := VTy.step Rw.nil tInt

/-- `Yield` to a stored generator over integers. -/
def streamOpsI {Ψ : List Eff} {Γ : List (VTy σ)} : (o : Op .yld) →
    M Ψ (kty (σ.q .yld o) Rw.nil (σ.res .yld o) (.F tIStep) :: .g (σ.arg .yld o) :: Γ) (.F tIStep)
  | .yield => .ret (.inr (.pair v1 (.fold (.thunk Mode.lin
      (.rcd (.app (.prj1 (.force v0)) .unit) (.prj2 (.force v0)))))))

/-- `using r = acquire 1 in (handle y with stream in (yield y 1; use r; ret 0))`, then pull the
stream past the frame. -/
def resEscape : Prog σ .int :=
  .bind (.using 1 (.handle .yld Rw.nil (.ret (.inl v0)) streamOpsI (fun a => nomatch a)
      (.op .z Op.yield (.int 1) (.op (.s .z) Op.use .unit (.ret (.int 0))))))
    (.case v0 (.ret v0) (.split v0 (.bind (.prj1 (.unfold v0)) (.ret (.int 1)))))

theorem resEscape_obs :
    resEscape.obs = ⟨.unhandled, [.acq 1, .free 1]⟩ := by decide

theorem resEscape_not_moded : ¬ ∃ R, CM (Ψ := []) (Γ := []) VSet.none R resEscape :=
  not_moded_of_obs (fun v h => by rw [resEscape_obs] at h; cases h)

/-! ## §10.3 -/

/-- Resume twice; the return clause consumes the capability. -/
def againOps {Ψ : List Eff} {Γ : List (VTy σ)} : (o : Op .choose) →
    M Ψ (kty (σ.q .choose o) Rw.nil (σ.res .choose o) (.F tInt) :: .g (σ.arg .choose o) :: Γ)
      (.F tInt)
  | .choose =>
      .bind (.app (.prj1 (.force v0)) (.bool true))
        (.bind (.app (.prj1 (.force v1)) (.bool false)) (.ret v0))

/-- `newcap c; handle g with {choose(_, k) ↦ k tt; k ff; ret z ↦ getcap c} in (choose; ret 0)`. -/
def retTwice : Prog σ .int :=
  .bind (.newcap Eff.ctr .int coCtr (.int 0))
    (.handle .choose Rw.nil (.getcap v1) againOps (fun a => nomatch a)
      (.op .z Op.choose .unit (.ret (.int 0))))

theorem retTwice_stuck : retTwice.obs.out = .stuck := by decide

theorem retTwice_not_moded : ¬ ∃ R, CM (Ψ := []) (Γ := []) VSet.none R retTwice :=
  not_moded_of_obs (fun v h => by rw [retTwice_stuck] at h; cases h)

end EffRel
