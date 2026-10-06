import Targets.Statements.Interface

/-!
# Targets — `UnwindRun` on two frames whose inner finaliser raises (DESIGN §5 I3, §9 item 21)

`ubind (N₁, D₁) (ubind (N₂, D₂) (raise p))`, with `D₂ = λ_. raise p′` and `D₁ = λ_. ()`.  The
machine runs `ufin` at the inner frame, then `D₂ ()` to `(raise p′; raise p)`, a raise under a
`seq` frame that no rule reduces there, then `ufin` at the outer frame on `p′`, then
`D₁ (); raise p′` to `raise p′` (`two_frame_steps`).  `UnwindRun`'s `fin` derives that run with
`Kd = (_; raise p)` at the first frame and `Kd = □` at the second, firing `[D₂, D₁]`, the frames'
`Kont.fins`, innermost first (`two_frame`).  Without the outer frame the run stops at
`(raise p′; raise p)`, and `fin` then `out` at `K = (_; raise p)` derive it (`one_frame`).
`[prog]`
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont raiseE opPayload ubindE)

/-- The two finaliser frames: `ubind (N₁, D₁) (ubind (N₂, D₂) □)`. -/
def twoFrames (N₁ D₁ N₂ D₂ : Val) : Kont := (ubindK N₁ D₁).comp (ubindK N₂ D₂)

/-- The raising finaliser `λ_. raise p′`. -/
def raiseFin (p : Val) : Val := Val.lam (raiseE (.val p))

/-- The finaliser that returns: `λ_. ()`. -/
def unitFin : Val := Val.lam (.val .unit)

theorem twoFrames_fins (N₁ D₁ N₂ D₂ : Val) : (twoFrames N₁ D₁ N₂ D₂).fins = [D₂.1, D₁.1] := rfl

theorem raiseE_subst {p : Val} (hp : closedAt 0 p.1 = true) (s : Val) :
    (raiseE (.val p)).subst 0 s = raiseE (.val p) := by
  show Expr.app ((Expr.prim .raise).subst 0 s) (Expr.subst 0 s (.val p)) = _
  rw [val_subst_closed hp]; rfl

/-- `D₂ (); raise p` runs to `raise p′; raise p`: one β step under the `seq` frame. -/
theorem raiseFin_steps {μ : Heap} {p p' : Val} (hp' : closedAt 0 p'.1 = true) :
    Steps (ℍ := ℍ) μ (.seq (.app (.val (raiseFin p')) (.val .unit)) (raiseE (.val p))) μ
      ((Kont.seq .hole (raiseE (.val p))).plug (raiseE (.val p'))) := by
  refine .more ⟨.seq .hole (raiseE (.val p)), _, _, rfl, ?_, Head.beta μ (raiseE (.val p')) .unit⟩
    (.refl _ _)
  simp only [Kont.plug, raiseE_subst hp']

/-- `D₁ (); raise p′` runs to `raise p′`: β, then `1↦`. -/
theorem unitFin_steps {μ : Heap} (p' : Val) :
    Steps (ℍ := ℍ) μ (.seq (.app (.val unitFin) (.val .unit)) (raiseE (.val p'))) μ
      (Kont.hole.plug (raiseE (.val p'))) :=
  .more ⟨.seq .hole (raiseE (.val p')), _, _, rfl, rfl, Head.beta μ (.val .unit) .unit⟩
    (.more (Step1.head (Head.seq μ (raiseE (.val p')))) (.refl _ _))

/-- **The machine run** through the two frames. -/
theorem two_frame_steps {μ : Heap} (N₁ N₂ : Val) {n i m j : UInt32} (v w : Val) (hn : n ≠ 0)
    (hm : m ≠ 0) (hw : closedAt 0 (opPayload m j w).1 = true) :
    Steps (ℍ := ℍ) μ
      ((twoFrames N₁ unitFin N₂ (raiseFin (opPayload m j w))).plug (raiseE (.val (opPayload n i v))))
      μ (raiseE (.val (opPayload m j w))) := by
  -- `ufin` at the inner frame
  refine .more ⟨ubindK N₁ unitFin, _, _, rfl, rfl,
    Head.ufin μ N₂ (raiseFin (opPayload m j w)) n i v .hole hn rfl⟩ ?_
  -- `D₂ ()` to `raise p′` under `seq` and the outer frame
  refine BoCa.BoLo.Steps.trans (BoCa.BoLo.Steps.plug (ubindK N₁ unitFin) (raiseFin_steps hw)) ?_
  -- `ufin` at the outer frame on `p′`
  refine .more ⟨.hole, _, _, rfl, rfl,
    Head.ufin μ N₁ unitFin m j w (.seq .hole (raiseE (.val (opPayload n i v)))) hm rfl⟩ ?_
  exact unitFin_steps _

/-- **`UnwindRun` on the two frames**, firing `[D₂, D₁]`, the frames' `Kont.fins`. -/
theorem two_frame {μ : Heap} (N₁ N₂ : Val) {n i m j : UInt32} (v w : Val) (hn : n ≠ 0)
    (hm : m ≠ 0) (hw : closedAt 0 (opPayload m j w).1 = true) :
    UnwindRun (ℍ := ℍ) μ
      ((twoFrames N₁ unitFin N₂ (raiseFin (opPayload m j w))).plug (raiseE (.val (opPayload n i v))))
      (twoFrames N₁ unitFin N₂ (raiseFin (opPayload m j w))).fins
      μ (raiseE (.val (opPayload m j w))) := by
  rw [twoFrames_fins]
  refine UnwindRun.fin (K₀ := ubindK N₁ unitFin) (K := .hole)
    (Kd := .seq .hole (raiseE (.val (opPayload n i v)))) hn rfl (raiseFin_steps hw) rfl ?_
  exact UnwindRun.fin (K₀ := .hole) (K := .seq .hole (raiseE (.val (opPayload n i v))))
    (Kd := .hole) hm rfl (unitFin_steps _) rfl (UnwindRun.out (K := Kont.hole.comp .hole) rfl)

/-- **One frame**: the run stops at `(raise p′; raise p)`, and `fin` then `out` at
`K = (_; raise p)` derive it. -/
theorem one_frame {μ : Heap} (N₂ : Val) {n i m j : UInt32} (v w : Val) (hn : n ≠ 0)
    (hw : closedAt 0 (opPayload m j w).1 = true) :
    UnwindRun (ℍ := ℍ) μ
      ((ubindK N₂ (raiseFin (opPayload m j w))).plug (raiseE (.val (opPayload n i v))))
      (ubindK N₂ (raiseFin (opPayload m j w))).fins
      μ ((Kont.seq .hole (raiseE (.val (opPayload n i v)))).plug (raiseE (.val (opPayload m j w)))) :=
  UnwindRun.fin (K₀ := .hole) (K := .hole) (Kd := .seq .hole (raiseE (.val (opPayload n i v)))) hn
    rfl (raiseFin_steps hw) rfl (UnwindRun.out (K := Kont.hole.comp (.seq .hole _)) rfl)

end Targets

end
