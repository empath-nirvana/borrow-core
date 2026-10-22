import Core.DivHandleLast
import Core.DivDrive
import Core.EffCancelRuns

/-!
# Core — `[handle-last]`'s erasure law at a work that performs nothing  `[spec §19, §25, §51, §54]`

The backend's licence to call a `[handle-last]` clause's work where its operation is performed
(SPEC §54, *Backend*): the two endings of a clause whose work runs to a value without performing
an operation the node handles. The handled computation is `K[perform (n, (i, v))]`, `K` free of
`n`, under the handler `lastH n E vr vw vn`; the operation `i = j` is affine, and its work `g` (the
`j`-th of the works' tuple `vw`) applied to `v` runs to `inl y` or `inr z`.

* **T-B1, `last_resume_direct`**: on `inl y` the configuration reaches `hnd H K[y]`: the handler
  around the rest of the handled computation, `y` the operation's answer where it was performed,
  and `κ`'s cell released. So a direct call of the work in place of the `perform` returns to the
  handled computation on `inl`. The steps: `[op]` and `κ`'s cell (`catch_cell`), the clause up to
  its work under the finaliser frame (`lastClause_steps`), the work's run, the frame's answer
  (`lastN_inl`), and `κ`'s resume at its cell (`kappaC_resume`).
* **T-B1′, `last_cancel_direct`**: on `inr z` the configuration reaches `κ`'s cancel run, the dead
  region `K†` from the cancel under its delimiter (`cancelOf K`, as `kappa_cancel_steps`), under the
  exit's frame, `κ`'s cell released; `last_cancel_exit`: when that cancel run answers `()`, the exit
  runs at `z` (`exitK_steps`). So on `inr` the backend unwinds the handled computation from the
  `perform` to the node, running `K`'s finalisers innermost first (`cancel_prefix` reads that run;
  `K†` holds no handler, so none of `K`'s handlers catches anything), and branches to the exit.

* **`tail_resume_direct`**: the same law at `effHandleT`'s clause `λ(x, κ). κ.1 (g x)`: `g`'s
  answer `w` is the operation's answer where it was performed.

A tick inside the work is answered *next* where it is performed when `main`'s `reify` is the one
handler of `Div` (`drive_reify_tick`, SPEC §53); the work's run here is the run with the ticks so
answered. A work that performs an operation of a handler outside the node (T-B2) is not covered.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont performE opPayload hndE hndVal kappaC clauseAt capTag)

namespace LastRuns

/-- `κ` at its cell `ℓ`, as a value. -/
def kapV (ℓ : Loc) (H : Val) (K : Kont) : Val := ⟨kappaC true ℓ H K, by unfold kappaC; exact .lam⟩

/-- **The clause runs its work under the finaliser frame**: `[op]` at the affine operation `i = j`
allocates `κ`'s cell at `ℓ` (`catch_cell`), and the clause steps to its work `g` applied to `v`,
under the frame `ubind (lastN, lastD)` around which `K₀` stands. -/
theorem last_op_work {μ : Heap} {ℓ : Loc} (hℓ : μ ℓ = none) {n i : UInt32}
    {E : List (Qual × VTy × VTy)} {vr vw vn : Val} {j : Nat} (hj : j < E.length)
    (hji : i.toNat = j) (hq : E[j].1 = .aff) (hB : E[j].2.2.isZero = false)
    {K : Kont} (hK : K.HasHnd n = false) {g v : Val}
    (hg : PureSteps (pickE j (.val vw)) (.val g)) (K₀ : Kont) :
    Steps (ℍ := ℍ) μ (K₀.plug (hndE (lastH n E vr vw vn) (K.plug (performE (.val (opPayload n i v))))))
      (μ.upd ℓ .unit)
      (K₀.plug ((ubindK (lastN j (kapV ℓ (lastH n E vr vw vn) K) vn)
        (lastD (kapV ℓ (lastH n E vr vw vn) K))).plug (.app (.val g) (.val v)))) := by
  have hc : clauseAt (lastTuple E 0 (.val vw) (.val vn)) i.toNat =
      some ⟨lastClause j false (.val vw) (.val vn), isVal_lastClause _ _ _ _⟩ := by
    rw [hji, clauseAt_lastTuple _ _ E 0 j hj]
    simp [hB]
  have htag : capTag (qualsVal (E.map Prod.fst)).1 i.toNat = Qual.aff.tag := by
    rw [hji, capTag_qualsVal _ j (by simpa using hj)]
    simp [hq]
  have h₁ := catch_cell (ℍ := ℍ) (qs := qualsVal (E.map Prod.fst)) (hr := vr)
    (hs := ⟨lastTuple E 0 (.val vw) (.val vn), isVal_lastTuple _ _ E 0⟩) hℓ v (q := .aff)
    (by decide) hc hK htag K₀
  refine h₁.trans ?_
  have h₂ := DivDrive.pure_steps (ℍ := ℍ) (lastClause_steps j vw vn g v
    (kapV ℓ (lastH n E vr vw vn) K) hg) (μ.upd ℓ .unit)
  exact h₂.plug K₀

/-- **T-B1: the resume ending.** A work that runs to `inl y` resumes the handled computation at
`y` where the operation was performed, the handler around it, `κ`'s cell released.
`[spec §51, §54]` -/
theorem last_resume_direct {μ μ₁ : Heap} {ℓ : Loc} (hℓ : μ ℓ = none) {n i : UInt32}
    {E : List (Qual × VTy × VTy)} {vr vw vn : Val} {j : Nat} (hj : j < E.length)
    (hji : i.toNat = j) (hq : E[j].1 = .aff) (hB : E[j].2.2.isZero = false)
    {K : Kont} (hK : K.HasHnd n = false) {g v y : Val}
    (hg : PureSteps (pickE j (.val vw)) (.val g))
    (hw : Steps (ℍ := ℍ) (μ.upd ℓ .unit) (.app (.val g) (.val v)) μ₁ (.val (Val.inj₁ y)))
    (hℓ₁ : μ₁ ℓ = some .unit) (K₀ : Kont) :
    Steps (ℍ := ℍ) μ (K₀.plug (hndE (lastH n E vr vw vn) (K.plug (performE (.val (opPayload n i v))))))
      (μ₁.del ℓ) (K₀.plug (hndE (lastH n E vr vw vn) (K.plug (.val y)))) := by
  let H := lastH n E vr vw vn
  let κ := kapV ℓ H K
  refine (last_op_work hℓ hj hji hq hB hK hg K₀).trans ?_
  refine ((hw.plug (ubindK (lastN j κ vn) (lastD κ))).plug K₀).trans ?_
  refine ((DivDrive.pure_steps (ℍ := ℍ) (lastN_inl j κ vn y) μ₁).plug K₀).trans ?_
  exact kappaC_resume hℓ₁ true H K y K₀

/-- **T-B1′: the cancel ending.** A work that runs to `inr z` cancels `κ`: the configuration
reaches `κ`'s cancel run `cancelOf K`, the dead region from the cancel under its delimiter, under
the exit's frame, `κ`'s cell released.  `[spec §51, §54]` -/
theorem last_cancel_direct {μ μ₁ : Heap} {ℓ : Loc} (hℓ : μ ℓ = none) {n i : UInt32}
    {E : List (Qual × VTy × VTy)} {vr vw vn : Val} {j : Nat} (hj : j < E.length)
    (hji : i.toNat = j) (hq : E[j].1 = .aff) (hB : E[j].2.2.isZero = false)
    {K : Kont} (hK : K.HasHnd n = false) {g v z : Val}
    (hg : PureSteps (pickE j (.val vw)) (.val g))
    (hw : Steps (ℍ := ℍ) (μ.upd ℓ .unit) (.app (.val g) (.val v)) μ₁ (.val (Val.inj₂ z)))
    (hℓ₁ : μ₁ ℓ = some .unit) (K₀ : Kont) :
    Steps (ℍ := ℍ) μ (K₀.plug (hndE (lastH n E vr vw vn) (K.plug (performE (.val (opPayload n i v))))))
      (μ₁.del ℓ) (K₀.plug ((exitK j vn z).plug (cancelOf K))) := by
  let H := lastH n E vr vw vn
  let κ := kapV ℓ H K
  refine (last_op_work hℓ hj hji hq hB hK hg K₀).trans ?_
  refine ((hw.plug (ubindK (lastN j κ vn) (lastD κ))).plug K₀).trans ?_
  refine ((DivDrive.pure_steps (ℍ := ℍ) (lastN_inr j κ vn z) μ₁).plug K₀).trans ?_
  have h := kappaC_cancel hℓ₁ H K (K₀.comp (exitK j vn z))
  rw [Kont.plug_comp, Kont.plug_comp] at h
  exact h

/-- **The exit after the cancel**: when the cancel run answers `()`, the exit `nf_j` runs at `z`.
With `last_cancel_direct`, `inr z` is the handled computation unwound to the node, its finalisers
run, and then a branch to the exit.  `[spec §51, §54]` -/
theorem last_cancel_exit {μ₁ μ₂ : Heap} {j : Nat} {vn z gn : Val} {K : Kont}
    (hgn : PureSteps (pickE j (.val vn)) (.val gn))
    (hc : Steps (ℍ := ℍ) μ₁ (cancelOf K) μ₂ (.val .unit)) (K₀ : Kont) :
    Steps (ℍ := ℍ) μ₁ (K₀.plug ((exitK j vn z).plug (cancelOf K))) μ₂
      (K₀.plug (.app (.val gn) (.val z))) := by
  refine ((hc.plug (exitK j vn z)).plug K₀).trans ?_
  exact (DivDrive.pure_steps (ℍ := ℍ) (exitK_steps j vn z gn hgn) μ₂).plug K₀

/-- **The cancel run of a region with no finaliser** answers `()` at once (`[cancel]`): with no
`ubind` frame, `K†` holds no `cfin`, no handler and no `ccatch`, so the cancel reaches its
delimiter. This is the case the backend meets when the handled computation's finalisers are all
empty, as at the empty cancel rows the checker emits. -/
theorem cancelOf_steps (μ : Heap) (K : Kont) (hK : K.dead.Catches 0 = false) :
    Steps (ℍ := ℍ) μ (cancelOf K) μ (.val .unit) :=
  .one (Step1.head (Head.cancel μ K.dead hK))

/-- **The tail-resuming rule's direct call** (`effHandleT`, SPEC §14, §54): at a non-abortive
operation `i = j` of qualifier `q ≠ unr`, whose answering function `g` (the `j`-th of the tuple
`vc`) applied to `v` runs to `w`, the configuration reaches `hnd H K[w]`, the handler around the
rest of the handled computation, `κ`'s cell released: `[op]` and the cell (`catch_cell`), the
clause up to `g v` under the resume frame (`tailClause_steps`), `g`'s run, the resume frame
(`resK_steps`) and `κ`'s resume at its cell (`kappaC_resume`).  `[spec §14, §54]` -/
theorem tail_resume_direct {μ μ₁ : Heap} {ℓ : Loc} (hℓ : μ ℓ = none) {n i : UInt32}
    {E : List (Qual × VTy × VTy)} {vr vc : Val} {j : Nat} (hj : j < E.length)
    (hji : i.toNat = j) (hq : E[j].1 ≠ .unr) (hB : (E[j].2.2.isZero && E[j].1 != .lin) = false)
    {K : Kont} (hK : K.HasHnd n = false) {g v w : Val}
    (hg : PureSteps (pickE j (.val vc)) (.val g))
    (hw : Steps (ℍ := ℍ) (μ.upd ℓ .unit) (.app (.val g) (.val v)) μ₁ (.val w))
    (hℓ₁ : μ₁ ℓ = some .unit) (K₀ : Kont) :
    Steps (ℍ := ℍ) μ (K₀.plug (hndE (tailH n E vr vc) (K.plug (performE (.val (opPayload n i v))))))
      (μ₁.del ℓ) (K₀.plug (hndE (tailH n E vr vc) (K.plug (.val w)))) := by
  let H := tailH n E vr vc
  have hc : clauseAt (tailTuple E 0 (.val vc)) i.toNat =
      some ⟨tailClause j false (.val vc), isVal_tailClause _ _ _⟩ := by
    rw [hji, clauseAt_tailTuple _ E 0 j hj]
    simp [hB]
  have htag : capTag (qualsVal (E.map Prod.fst)).1 i.toNat = E[j].1.tag := by
    rw [hji, capTag_qualsVal _ j (by simpa using hj)]
    simp
  have h₁ := catch_cell (ℍ := ℍ) (qs := qualsVal (E.map Prod.fst)) (hr := vr)
    (hs := ⟨tailTuple E 0 (.val vc), isVal_tailTuple _ E 0⟩) hℓ v hq hc hK htag K₀
  refine h₁.trans ?_
  let κ : Val := ⟨kappaC (cellAff E[j].1) ℓ H K, by unfold kappaC; exact .lam⟩
  refine ((DivDrive.pure_steps (ℍ := ℍ) (tailClause_steps j vc g v κ hg) _).plug K₀).trans ?_
  refine ((hw.plug (resK κ)).plug K₀).trans ?_
  refine ((DivDrive.pure_steps (ℍ := ℍ) (resK_steps κ w) μ₁).plug K₀).trans ?_
  exact kappaC_resume hℓ₁ _ H K w K₀

end LastRuns

end BoCa.Fig16.LogRel.Core
