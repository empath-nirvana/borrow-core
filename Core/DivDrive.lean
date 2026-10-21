import Core.DivReify
import Core.DivIterate
import Core.DelayPrograms
import Core.Stale
import Core.EffMachine

/-!
# Core — the runtime's drive of a reified loop answers *next* at every tick  `[spec §14, §49]`

A `main` that loops is the loop value of its body (SPEC §47): `reify_res t`, which the runtime
observes with *next* until it finishes (SPEC §11; `driveE n` observes at most `n` times,
`Backend/Source.lean`'s `driveSource` without a bound). These are the steps of that drive at a
tick and at the body's end, the law the new backend's rule for `main` and `tick` reads
(`Backend2/Convert.lean`, `runtimeMain`; SPEC §49):

* `reify_seg_tick`: under `reify`'s handler `H`, a segment that reaches a tick answers the loop
  `tickLoop κ` at it, `κ` given a fresh cell;
* `reify_next_resumes`: observing that loop with *next* frees the cell and resumes the segment
  with *next* under `H` again;
* `drive_reify_tick`: so the drive, one observation deeper, goes from `hnd H K[tick ()]` to
  `hnd H K[next]`, at the memory it had: the tick is answered *next* where it was performed;
* `drive_reify_done`: a segment that ends with `inl b` ends the drive with `inl b`;
* `drive_reify_closed`: a segment that ends with `inr r` (a loop closed with its residual) leaves
  the loop `closed r`, which every observation skips: every bounded drive answers `inr r`, so the
  unbounded drive does not finish;
* `reify_start`, `reify_first_tick`, `reify_first_done`, `drive_first_tick`, `drive_first_done`:
  the first segment, `t ()` under `reify`'s `rk` frame rather than the drive's.

`iterate`'s back edge under the drive is then `iter_step`, `iterK_inr`, `drive_reify_tick` and
`turnK_next` (`Core/DivIterate.lean`): its turn's tick is answered *next*, and the loop goes on.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont performE opPayload hndE hndVal kappaC kappaCell
  kappaCBody kappaAt clauseAt capTag freeE)

attribute [local simp] Expr.subst Val.val_shift Expr.shift_shift Expr.shift_zero

namespace DivDrive

/-- A pure reduction is a run at every memory, which it keeps. -/
theorem pure_steps {e e' : Expr} (h : PureSteps e e') (μ : Heap) : Steps (ℍ := ℍ) μ e μ e' := by
  induction h with
  | refl => exact .refl _ _
  | tail _ hs ih => exact ih.trans (.more (hs μ).toStep1 (.refl _ _))

/-- The rest of `driveE (n + 1)` after its observation: `[·] to r. case r { inl b → inl b |
inr d′ → driveE n }`. -/
def obsK (n : ℕ) : Kont := .appR (.val (.lam (.case (.var 0) (.inj₁ (.var 0)) (driveE n)))) .hole

/-- `driveE n` reads only the loop it observes. -/
theorem driveE_closed : ∀ n, closedAt 1 (driveE n) = true
  | 0 => by simp [driveE, bindE, closedAt]
  | n + 1 => by
    have h := closedAt_mono _ (driveE_closed n) (show 1 ≤ 3 by omega)
    simp [driveE, bindE, closedAt, h]

/-- **`driveE (n + 1)` at the loop `L`** is its observation of `L` with *next*, in `obsK n`. -/
theorem driveE_succ (n : ℕ) (L : Val) :
    (driveE (n + 1)).subst 0 L = (obsK n).plug (.app (.val L) (.val nextV)) := by
  have h : (driveE n).subst 2 ((L.shift 1 0).shift 1 0) = driveE n :=
    subst_closedAt _ _ (driveE_closed n) (by omega)
  simp [driveE, bindE, obsK, Kont.plug, nextV, h]

/-- After an observation that answers `inr L`, the drive goes on at `L`. -/
theorem obsK_inr (n : ℕ) (L : Val) :
    PureSteps ((obsK n).plug (.val (Val.inj₂ L))) ((driveE n).subst 0 L) := by
  refine (PureSteps.beta _ _).trans ?_
  refine (PureSteps.head (fun μ => Head.case₂ μ L _ _) rfl).trans ?_
  have h : (driveE n).subst 1 ((Val.inj₂ L).shift 1 0) = driveE n :=
    subst_closedAt _ _ (driveE_closed n) (by omega)
  simp [h]
  exact .refl

/-- After an observation that answers `inl b`, the drive ends with `inl b`. -/
theorem obsK_inl (n : ℕ) (b : Val) :
    PureSteps ((obsK n).plug (.val (Val.inj₁ b))) (.val (Val.inj₁ b)) := by
  refine (PureSteps.beta _ _).trans ?_
  refine (PureSteps.head (fun μ => Head.case₁ μ b _ _) rfl).trans ?_
  simp
  exact .refl

section
variable (res : Val) (hres : closedAt 0 res.1 = true)

/-- `reify`'s handler. -/
abbrev H : Val := reifyH res

/-- `κ` at its cell `ℓ`, for the segment's context `K`. -/
abbrev kap (ℓ : Loc) (K : Kont) : Val := kapV ℓ (H res) K

include hres in
/-- **A segment that reaches a tick answers the loop at it**: under `reify`'s handler, in a
context `K₀`, `K[tick ()]` (`K` free of `Div`'s handler) gives `κ` a fresh cell `ℓ` and answers
`inr (tickLoop κ)`. -/
theorem reify_seg_tick {μ : Heap} {ℓ : Loc} (hℓ : μ ℓ = none) (K₀ K : Kont)
    (hK : K.HasHnd divEff = false) :
    Steps (ℍ := ℍ) μ (K₀.plug (hndE (H res) (K.plug tickE))) (μ.upd ℓ .unit)
      (K₀.plug (.val (Val.inj₂ (tickLoop res (kap res ℓ K))))) := by
  have h₁ := (catch_step (ℍ := ℍ) μ (n := divEff) (i := 0) (qs := qualsVal [.lin]) (hr := reifyR)
    (hs := Val.pair (reifyC res) .unit) Val.unit (clauseAt_one (reifyC res)) hK K₀).1
  rw [kappaAt_lin, plug_kappaCell] at h₁
  rw [tickE_eq]
  refine .more h₁ ?_
  have h₂ := (step1_alloc_iff (ℍ := ℍ) (μ := μ) (μ₁ := μ.upd ℓ .unit)
    (e₁ := (K₀.comp (.appR (.val (reifyC res)) (.pairR Val.unit (.appR
      (.val (Val.lam (kappaCBody false (H res) K))) .hole)))).plug (.val (Val.loc ℓ))) _ Val.unit).2
    ⟨ℓ, hℓ, rfl, rfl⟩
  refine .more h₂ ?_
  rw [plug_kappaCellLoc]
  refine .more (kappaCell_beta (ℍ := ℍ) _ K₀ (reifyC res) Val.unit false ℓ (H res) K).1 ?_
  exact pure_steps (PureSteps.plug K₀ (reifyC_steps res hres (kap res ℓ K))) _

include hres in
/-- **Observing the loop at a tick with *next* resumes the segment with *next***: `κ`'s cell
freed, `K[next]` under `reify`'s handler again, in a context `K₀`. -/
theorem reify_next_resumes {μ : Heap} {ℓ : Loc} (hℓ : μ ℓ = some .unit) (K₀ K : Kont) :
    Steps (ℍ := ℍ) μ (K₀.plug (.app (.val (tickLoop res (kap res ℓ K))) (.val nextV))) (μ.del ℓ)
      (K₀.plug (hndE (H res) (K.plug (.val nextV)))) := by
  refine (pure_steps (PureSteps.plug K₀ (tickLoop_next res hres (kap res ℓ K))) μ).trans ?_
  let nK : Kont := K₀.comp (.appL .hole nextV)
  have e₁ : K₀.plug (.app (.app (.val (kap res ℓ K)) (.val (Val.inj₁ .unit))) (.val nextV)) =
      nK.plug (.app (kappaC false ℓ (H res) K) (.val (Val.inj₁ .unit))) := by
    simp only [nK, Kont.plug_comp]; rfl
  rw [e₁]
  refine .more (kappaC_beta (ℍ := ℍ) μ false ℓ (H res) K (Val.inj₁ .unit) nK).1 ?_
  refine .more (kappaC_case₁ (ℍ := ℍ) μ false ℓ (H res) K _ .unit nK).1 ?_
  refine .more (step1Only_plug (ℍ := ℍ) (Head.seq μ _) rfl nK).1 ?_
  have h₄ := (free_step1Only (ℍ := ℍ) hℓ (nK.comp (.seq .hole (kResume (H res) K).1))).1
  have e₃ : nK.plug (.seq (freeE (.val (Val.loc ℓ))) (kResume (H res) K).1) =
      (nK.comp (.seq .hole (kResume (H res) K).1)).plug (freeE (.val (Val.loc ℓ))) := by
    simp only [nK, Kont.plug_comp]; rfl
  rw [e₃]
  refine .more h₄ ?_
  have e₄ : (nK.comp (.seq .hole (kResume (H res) K).1)).plug (.val Val.unit) =
      nK.plug (.seq (.val Val.unit) (kResume (H res) K).1) := by
    simp only [nK, Kont.plug_comp]; rfl
  rw [e₄]
  refine .more (step1Only_plug (ℍ := ℍ) (Head.seq (μ.del ℓ) _) rfl nK).1 ?_
  have e₂ : nK.plug (kResume (H res) K).1 =
      K₀.plug (.app (.val (kResume (H res) K)) (.val nextV)) := by
    simp only [nK, Kont.plug_comp]; rfl
  rw [e₂]
  exact .more (step1Only_plug (kResume_beta (μ.del ℓ) (H res) K nextV) rfl K₀).1 (.refl _ _)

include hres in
/-- **The drive answers *next* at a tick**: one observation deeper, `hnd H K[tick ()]` reaches
`hnd H K[next]` at the memory it had.  `[spec §49]` -/
theorem drive_reify_tick {μ : Heap} {ℓ : Loc} (hℓ : μ ℓ = none) (n : ℕ) (K : Kont)
    (hK : K.HasHnd divEff = false) :
    Steps (ℍ := ℍ) μ ((obsK (n + 1)).plug (hndE (H res) (K.plug tickE))) μ
      ((obsK n).plug (hndE (H res) (K.plug (.val nextV)))) := by
  refine (reify_seg_tick res hres hℓ (obsK (n + 1)) K hK).trans ?_
  refine (pure_steps (obsK_inr (n + 1) _) _).trans ?_
  rw [driveE_succ]
  have h := reify_next_resumes (ℍ := ℍ) res hres (μ := μ.upd ℓ .unit) (ℓ := ℓ)
    (BoCa.BoLo.Heap.upd_same μ ℓ .unit) (obsK n) K
  rwa [upd_del_of_none hℓ] at h

/-- **A segment that ends with `inl b` ends the drive with `inl b`**.  `[spec §49]` -/
theorem drive_reify_done (μ : Heap) (n : ℕ) (b : Val) :
    Steps (ℍ := ℍ) μ ((obsK n).plug (hndE (H res) (.val (Val.inj₁ b)))) μ (.val (Val.inj₁ b)) := by
  refine .more (catch_ret (ℍ := ℍ) μ divEff _ reifyR _ _ (obsK n)).1 ?_
  exact pure_steps ((PureSteps.plug (obsK n) (reifyR_inl b)).trans (obsK_inl n b)) μ

/-- The loop `closed r`, observed by the drive: every bounded drive answers `inr r`. -/
theorem drive_closed (μ : Heap) (r : Val) : ∀ n,
    Steps (ℍ := ℍ) μ ((obsK n).plug (.val (Val.inj₂ (clLoop r)))) μ (.val (Val.inj₂ r))
  | 0 => by
    refine (pure_steps (obsK_inr 0 _) μ).trans ?_
    simp only [driveE, bindE, Expr.subst]
    refine pure_steps ((PureSteps.plug (.appR (.val (.lam (.inj₂ (.var 0)))) .hole)
      (clLoop_close r)).trans ?_) μ
    refine (PureSteps.beta _ _).trans ?_
    simp
    exact .refl
  | n + 1 => by
    refine (pure_steps (obsK_inr (n + 1) _) μ).trans ?_
    rw [driveE_succ]
    exact (pure_steps (PureSteps.plug (obsK n) (clLoop_next r)) μ).trans (drive_closed μ r n)

/-- **A segment that ends with `inr r` never finishes the drive**: the loop it leaves is `closed
r`, which every observation skips, so every bounded drive answers `inr r` and none answers `inl`.
`[spec §49]` -/
theorem drive_reify_closed (μ : Heap) (n : ℕ) (r : Val) :
    Steps (ℍ := ℍ) μ ((obsK n).plug (hndE (H res) (.val (Val.inj₂ r)))) μ (.val (Val.inj₂ r)) := by
  refine .more (catch_ret (ℍ := ℍ) μ divEff _ reifyR _ _ (obsK n)).1 ?_
  exact (pure_steps (PureSteps.plug (obsK n) (reifyR_inr r)) μ).trans (drive_closed μ r n)

/-! ### The first segment

`reify_res t` runs `t ()` under `rk [hnd H ·]` (`reifyV`): the first segment's answer is turned
into the loop value the drive then observes. -/

/-- `rk`'s frame. -/
abbrev rkK : Kont := .appR (.val (rkV res)) .hole

include hres in
/-- **`reify_res t` starts its body**: `t ()` under `rk [hnd H ·]`. -/
theorem reify_start (t : Val) :
    PureSteps (.app (.val (reifyV res)) (.val t))
      ((rkK res).plug (hndE (H res) (.app (.val t) (.val .unit)))) := by
  refine (PureSteps.beta _ _).trans ?_
  simp only [BoCa.BoLo.hndE, Expr.subst, closed_subst (rkV_closed hres),
    closed_subst (reifyH_closed hres), H, Kont.plug]
  exact .refl

include hres in
/-- The first segment reaching a tick is the loop at it. -/
theorem reify_first_tick {μ : Heap} {ℓ : Loc} (hℓ : μ ℓ = none) (K : Kont)
    (hK : K.HasHnd divEff = false) :
    Steps (ℍ := ℍ) μ ((rkK res).plug (hndE (H res) (K.plug tickE))) (μ.upd ℓ .unit)
      (.val (tickLoop res (kap res ℓ K))) :=
  (reify_seg_tick res hres hℓ (rkK res) K hK).trans (pure_steps (rkV_inr res _) _)

include hres in
/-- The first segment ending with `inl b` is the loop `done b`. -/
theorem reify_first_done (μ : Heap) (b : Val) :
    Steps (ℍ := ℍ) μ ((rkK res).plug (hndE (H res) (.val (Val.inj₁ b)))) μ
      (.val (doneLoop res b)) := by
  refine .more (catch_ret (ℍ := ℍ) μ divEff _ reifyR _ _ (rkK res)).1 ?_
  exact pure_steps ((PureSteps.plug (rkK res) (reifyR_inl b)).trans (rkV_inl res hres b)) μ

include hres in
/-- The drive's first observation of the loop at the first tick resumes the segment with *next*,
in `obsK`. -/
theorem drive_first_tick {μ : Heap} {ℓ : Loc} (hℓ : μ ℓ = some .unit) (n : ℕ) (K : Kont) :
    Steps (ℍ := ℍ) μ ((driveE (n + 1)).subst 0 (tickLoop res (kap res ℓ K))) (μ.del ℓ)
      ((obsK n).plug (hndE (H res) (K.plug (.val nextV)))) := by
  rw [driveE_succ]
  exact reify_next_resumes res hres hℓ (obsK n) K

include hres in
/-- The drive's first observation of `done b` ends it with `inl b`. -/
theorem drive_first_done (μ : Heap) (n : ℕ) (b : Val) :
    Steps (ℍ := ℍ) μ ((driveE (n + 1)).subst 0 (doneLoop res b)) μ (.val (Val.inj₁ b)) := by
  rw [driveE_succ]
  exact pure_steps ((PureSteps.plug (obsK n) (doneLoop_next res hres b)).trans (obsK_inl n b)) μ

end

end DivDrive

end BoCa.Fig16.LogRel.Core

end
