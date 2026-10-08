import Targets.Instance.ERuns

/-!
# The Instance — E1's runs at our instance

E1's program and E1′'s run to their answers with no observable event, under the runner that answers
nothing (`runsTo_noColour`, `runsTo_noColourS`).  Each run is calm (`Calm`): quiet head steps,
which `look` computes between the catches; the catch of `exn`'s raise by its handler (`[unwind]`,
no cell: `exn` is abortive); and the catch of the affine `wait` around `κ`'s cell (SPEC §25),
which the resume releases.  In E1′ the clause answers a closure holding `κ`, and the cell is
released when the closure runs, after `f` has run again.  `[Core σ=[]]`
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets.Inst
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Head Kont performE raiseE hndE hndVal opPayload kappaCell kappaCBody freeE kappaAt
  capTag)
open Targets (EffCtx orowRF orowAlg lookRun lookEnd)

/-! ### The handler values -/

/-- `toResult`'s handler at the name `n` and the tags `qs`. -/
def toResultV (n : UInt32) (qs : Val) : Val :=
  hndVal n qs ⟨.lam (.inj₁ (.var 0)), .lam⟩ ⟨clausesE [.lam (.inj₂ .unit)], .pair .lam .unit⟩

/-- `resumer`'s handler at the name `n` and the tags `qs`. -/
def resumerV (n : UInt32) (qs : Val) : Val := hndVal n qs ⟨.lam (.var 0), .lam⟩ resumerCsV

/-- A label's tags at our instance, at the signature the context declares there. -/
theorem qsOf_eq {Ξ : EffCtx} {n : UInt32} {E : List (Qual × VTy × VTy)} (h : Ξ n = E) :
    qsOf Ξ n = (qualsVal (E.map Prod.fst)).1 := by
  rw [qsOf, h]

/-! ### E1 -/

/-- E1's rest after its first use. -/
def ncR2 (nw : UInt32) (qw : Expr) : Expr :=
  bindE ((handleK nw qw (.lam (.var 0)) [resumeClE]).plug (appE hofE (asyncCbE nw)))
    (.pair (.inj₂ .unit) (.pair (.var 1) (.var 0)))

/-- E1's rest after its second use. -/
def ncR3 : Expr := .pair (.inj₂ .unit) (.pair (.inj₂ .unit) (.var 0))

theorem nc_segA (ne nw : UInt32) (q : Qual) :
    lookEnd 9 (threeUsesW hofE ne nw (qualsVal [q]).1 (qualsVal [.aff]).1) =
      (bindK (ncR2 nw (qualsVal [.aff]).1)).plug
        ((handleK ne (qualsVal [q]).1 (.lam (.inj₁ (.var 0))) [.lam (.inj₂ .unit)]).plug
          (raiseE (opArgE ne 0 .unit))) := by rfl

theorem nc_segC (nw : UInt32) :
    lookEnd 6 ((bindK (ncR2 nw (qualsVal [.aff]).1)).plug (.app (.lam (.inj₂ .unit)) .unit)) =
      (bindK ncR3).plug ((handleK nw (qualsVal [.aff]).1 (.lam (.var 0)) [resumeClE]).plug
        ((bindK (.inj₂ .unit)).plug (performE (opArgE nw 0 .unit)))) := by rfl

theorem nc_segE (nw : UInt32) :
    lookEnd 5 ((bindK ncR3).plug ((handleK nw (qualsVal [.aff]).1 (.lam (.var 0)) [resumeClE]).plug
        ((bindK (.inj₂ .unit)).plug .unit))) =
      .pair (.inj₂ .unit) (.pair (.inj₂ .unit) (.inj₂ .unit)) := by rfl

/-- **E1's program runs calmly to its answer** `(tt, (inr (), tt))`. -/
theorem calm_threeUses (ne nw : UInt32) (q : Qual) :
    Calm (ℍ := ℍ) (threeUsesW hofE ne nw (qualsVal [q]).1 (qualsVal [.aff]).1)
      (.pair (.inj₂ .unit) (.pair (.inj₂ .unit) (.inj₂ .unit))) := by
  have hA := quiet_of_look (ℍ := ℍ) 9 (threeUsesW hofE ne nw (qualsVal [q]).1 (qualsVal [.aff]).1)
    rfl
  rw [nc_segA] at hA
  have hB := quiet_hunwind (ℍ := ℍ) (bindK (ncR2 nw (qualsVal [.aff]).1)) ne 0 (qualsVal [q])
    ⟨.lam (.inj₁ (.var 0)), .lam⟩ ⟨clausesE [.lam (.inj₂ .unit)], .pair .lam .unit⟩
    ⟨.lam (.inj₂ .unit), .lam⟩ Val.unit (clauseAt_clausesE [.lam (.inj₂ .unit)] 0 .lam rfl)
  have hC := quiet_of_look (ℍ := ℍ) 6
    ((bindK (ncR2 nw (qualsVal [.aff]).1)).plug (.app (.lam (.inj₂ .unit)) .unit)) rfl
  rw [nc_segC] at hC
  have hD := cellQuiet_resumeCl (ℍ := ℍ) true (bindK ncR3) nw (qualsVal [.aff])
    ⟨.lam (.var 0), .lam⟩ (bindK (.inj₂ .unit)) Val.unit rfl rfl rfl rfl
  have hE := quiet_of_look (ℍ := ℍ) 5 ((bindK ncR3).plug ((handleK nw (qualsVal [.aff]).1
    (.lam (.var 0)) [resumeClE]).plug ((bindK (.inj₂ .unit)).plug .unit))) rfl
  rw [nc_segE] at hE
  exact ((hA.trans (hB.trans hC)).calm.trans hD.calm).trans hE.calm

/-! ### E1′ -/

/-- E1′'s rest after `sched`. -/
def usS2 : Expr := bindE (appE hofE pureCbE) (bindE (appE (.var 1) .unit) (.pair (.var 1) (.var 0)))

/-- `sched`'s handler at the name `n`, at an affine operation. -/
def schedV (n : UInt32) : Val :=
  hndVal n (qualsVal [.aff]) ⟨schedRetE, .lam⟩ ⟨clausesE [schedClE], .pair .lam .unit⟩

/-- Around the allocation of `κ`'s cell, after `sched`'s catch. -/
def usK1 (n : UInt32) : Kont := (bindK usS2).comp (.appR schedClE (.pairR Val.unit
  (.appR (.lam (kappaCBody true n (schedV n) (bindK (.inj₂ .unit)))) .hole)))

/-- Around the release of `κ`'s cell, when the closure resumes `κ`. -/
def usK2 (n : UInt32) : Kont := (bindK (.pair (.inj₂ .unit) (.var 0))).comp
  ((bindK (appE (.var 0) .unit)).comp
    (Kont.appL (Kont.seq .hole (kResV (schedV n) (bindK (.inj₂ .unit)))) Val.unit))

theorem us_segA (nw : UInt32) :
    lookEnd 4 (usesSW hofE nw (qualsVal [.aff]).1) =
      (bindK usS2).plug (hndE (schedV nw) ((bindK (.inj₂ .unit)).plug
        (performE (.val (opPayload nw 0 Val.unit))))) := by rfl

theorem us_segB (nw : UInt32) (ℓ : Loc) :
    lookEnd 15 ((usK1 nw).plug (.val (Val.loc ℓ))) = (usK2 nw).plug (freeE (.val (Val.loc ℓ))) := by
  rfl

set_option maxHeartbeats 2000000 in
theorem us_segB_quiet (nw : UInt32) (ℓ : Loc) :
    (lookRun 15 ((usK1 nw).plug (.val (Val.loc ℓ)))).all (fun x => !finHead x.2.1) = true := by
  rfl

theorem us_segC (nw : UInt32) :
    lookEnd 11 ((usK2 nw).plug (.val Val.unit)) = .pair (.inj₂ .unit) (.inj₂ .unit) := by rfl

/-- **E1′'s program runs around `κ`'s cell to its answer** `(tt, tt)`: `sched`'s catch allocates
the cell, the closure it answers holds `κ`, and the closure's resume, after `f` runs again,
releases it. -/
theorem cellQuiet_usesS (nw : UInt32) :
    CellQuiet (ℍ := ℍ) (usesSW hofE nw (qualsVal [.aff]).1) (.pair (.inj₂ .unit) (.inj₂ .unit)) := by
  refine ⟨usK1 nw, ?_, fun ℓ => ⟨usK2 nw, ?_, ?_⟩⟩
  · have hA := quiet_of_look (ℍ := ℍ) 4 (usesSW hofE nw (qualsVal [.aff]).1) rfl
    rw [us_segA] at hA
    refine hA.trans ?_
    have hk : kappaAt (capTag (qualsVal [.aff]).1 (0 : UInt32).toNat) nw (schedV nw)
        (bindK (.inj₂ .unit)) = kappaCell true nw (schedV nw) (bindK (.inj₂ .unit)) := by
      simp [capTag, qualsVal, Qual.tag, kappaAt, Val.pair, Val.i32]
    have hh : ∀ μ, Head (ℍ := ℍ) μ (hndE (schedV nw) ((bindK (.inj₂ .unit)).plug
        (performE (.val (opPayload nw 0 Val.unit))))) μ (.app (.val ⟨schedClE, .lam⟩)
        (.pair (.val Val.unit) (kappaCell true nw (schedV nw) (bindK (.inj₂ .unit))))) := by
      intro μ
      have h := Head.hop (ℍ := ℍ) μ nw 0 (qualsVal [.aff]) ⟨schedRetE, .lam⟩
        ⟨clausesE [schedClE], .pair .lam .unit⟩ ⟨schedClE, .lam⟩ Val.unit (bindK (.inj₂ .unit))
        (clauseAt_clausesE [schedClE] 0 .lam rfl) rfl
      simp only [schedV] at hk ⊢
      rwa [hk] at h
    have e : (usK1 nw).plug (allocE Val.unit) = (bindK usS2).plug (.app (.val ⟨schedClE, .lam⟩)
        (.pair (.val Val.unit) (kappaCell true nw (schedV nw) (bindK (.inj₂ .unit))))) := by
      rw [usK1, Kont.plug_comp]; rfl
    rw [e]
    exact Quiet.head (bindK usS2) hh rfl rfl
  · have hB := quiet_of_look (ℍ := ℍ) 15 ((usK1 nw).plug (.val (Val.loc ℓ))) (us_segB_quiet nw ℓ)
    rwa [us_segB] at hB
  · have hC := quiet_of_look (ℍ := ℍ) 11 ((usK2 nw).plug (.val Val.unit)) rfl
    rwa [us_segC] at hC

section E1
variable {Ξ : EffCtx}

local notation "𝕁" => ourInst (ℍ := ℍ) orowRF Ξ J₁

/-- E1's program, `f` let-bound to `hof`, is E1's program with `hof` in place after one β-step. -/
theorem noColour_beta (le lw : (orowAlg Ξ).Lab) :
    Expr.subst 0 ⟨hofE, .lam⟩ (((𝕁).threeUses le lw : Expr)) =
      threeUsesW hofE le.1 lw.1 (qsOf Ξ le.1) (qsOf Ξ lw.1) := by
  simp only [A.EffectSystem.threeUses, A.EffectSystem.call, A.EffectSystem.apps, List.foldl,
    A.EffectSystem.toResult, A.EffectSystem.resumer, A.EffectSystem.pureCb, A.EffectSystem.failCb,
    A.EffectSystem.asyncCb, A.EffectSystem.resumeCl, A.EffectSystem.tt]
  simp only [ourInst, List.map]
  simp [threeUsesW, pureCbE, failCbE, asyncCbE, resumeClE, hofE, appE, bindE, handleK, hndValE,
    Kont.plug, Expr.shift, Expr.subst, clausesE, resumeE, qsOf, performE, raiseE, opArgE, Val.i32]

/-- **E1's run**: every complete run answers `(tt, (inr (), tt))` and shows nothing. -/
theorem runsTo_noColour {le lw : (orowAlg Ξ).Lab} {q : Qual}
    (hle : Ξ le.1 = [(q, .unit, .zero)]) (hlw : Ξ lw.1 = [(.aff, .unit, .unit)]) :
    (𝕁).RunsTo (𝕁).R₀ ((𝕁).noColour le lw) (𝕁).ans1 [] := by
  have h₀ := quiet_beta (ℍ := ℍ) .hole ((𝕁).threeUses le lw) ⟨hofE, .lam⟩
  rw [noColour_beta, qsOf_eq hle, qsOf_eq hlw] at h₀
  have h := (show Quiet (ℍ := ℍ) ((𝕁).noColour le lw) _ from h₀).calm.trans (calm_threeUses le.1 lw.1 q)
  exact runsTo_of_calm (𝕁).R₀
    (v := ⟨_, .pair (.inj₂ .unit) (.pair (.inj₂ .unit) (.inj₂ .unit))⟩) h

/-- E1′'s program, `f` let-bound to `hof`, after one β-step. -/
theorem noColourS_beta (lw : (orowAlg Ξ).Lab) :
    Expr.subst 0 ⟨hofE, .lam⟩ (((𝕁).usesS lw : Expr)) = usesSW hofE lw.1 (qsOf Ξ lw.1) := by
  simp only [A.EffectSystem.usesS, A.EffectSystem.call, A.EffectSystem.apps, List.foldl,
    A.EffectSystem.sched, A.EffectSystem.schedRet, A.EffectSystem.schedCl, A.EffectSystem.pureCb,
    A.EffectSystem.asyncCb, A.EffectSystem.tt]
  simp only [ourInst, List.map]
  simp [usesSW, schedRetE, schedClE, pureCbE, asyncCbE, hofE, appE, bindE, handleK, hndValE,
    Kont.plug, Expr.shift, Expr.subst, clausesE, resumeE, qsOf, performE, opArgE, Val.i32]

/-- **`hof` calls its callback, catching nothing**: from `let f = hof in f (λ_. M)`, the run reaches
`M` by store-keeping steps, at the empty context. -/
theorem callsThrough_hof {M : Expr} (hM : closedAt 0 M = true) :
    (𝕁).CallsThrough (fun _ => True) ((𝕁).lets [(𝕁).hof] ((𝕁).call ((𝕁).var 0) ((𝕁).lam M))) M := by
  obtain ⟨q, hc, -⟩ := quiet_hof_call (ℍ := ℍ) hM
  exact ⟨.hole, fun _ _ => rfl, trivial, pureSteps_of_chain hc⟩

/-- **E1′'s run**: every complete run answers `(tt, tt)` and shows nothing. -/
theorem runsTo_noColourS {lw : (orowAlg Ξ).Lab} (hlw : Ξ lw.1 = [(.aff, .unit, .unit)]) :
    (𝕁).RunsTo (𝕁).R₀ ((𝕁).noColourS lw) ((𝕁).pair (𝕁).tt (𝕁).tt) [] := by
  have h₀ := quiet_beta (ℍ := ℍ) .hole ((𝕁).usesS lw) ⟨hofE, .lam⟩
  rw [noColourS_beta, qsOf_eq hlw] at h₀
  have h := (show Quiet (ℍ := ℍ) ((𝕁).noColourS lw) _ from h₀).calm.trans
    (cellQuiet_usesS lw.1).calm
  exact runsTo_of_calm (𝕁).R₀ (v := ⟨_, .pair (.inj₂ .unit) (.inj₂ .unit)⟩) h

end E1

end Targets.Inst

end
