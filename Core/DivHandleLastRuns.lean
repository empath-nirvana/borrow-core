import Core.DivHandleLast
import Core.DivDrive
import Core.EffCancelRuns
import Core.ClauseKinds

/-!
# Core — the rule-written handlers' clauses at a work that performs nothing  `[spec §14, §19, §25, §51, §54]`

The per-perform laws of the two rule-written handlers (SPEC §54): what a `perform` of one of the
node's operations runs to, when the clause's work runs to a value without performing an operation.
The handled computation is `K[perform (n, (i, v))]`, `K` free of `n`.

* **`tail_resume_direct`** (`effHandleT`, SPEC §14): under `tailH n E vr vc`, at a non-abortive
  operation `i = j` whose answering function `g` (the `j`-th of the tuple `vc`) applied to `v`
  runs to `w`, the configuration reaches `hnd H K[w]`: the handler around the rest of the handled
  computation, `w` the operation's answer where it was performed, `κ`'s cell released. The steps:
  `[op]` and `κ`'s cell (`catch_cell`), the clause `λ(x, κ). κ.1 (g x)` up to `g v` under the
  resume frame (`tailClause_steps`), `g`'s run, the resume frame (`resK_steps`), and `κ`'s resume
  at its cell (`kappaC_resume`).
* **`last_resume_direct`** (`effHandleL`, SPEC §51): under `lastH n E vr vw vn`, at an operation
  at the count `1?`, a work that runs to `inl y` resumes the handled computation at `y`.
* **`last_cancel_direct`**, **`last_cancel_exit`**: a work that runs to `inr z` reaches `κ`'s
  cancel run `cancelOf K` under the exit's frame; when that run answers `()`, the exit runs at `z`.

An operation's count (`Count`, SPEC §53) gives its tag (`Count.toQual`): `1` linear, `1?` affine,
never unrestricted. The clause of an operation at the count `0` is its function itself, so the laws
are stated at a count other than `0`.

A work that performs an operation of a handler outside the node is not covered: the work's run
here is a run to a value (`hw`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont performE opPayload hndE hndVal kappaC clauseAt capTag)

namespace LastRuns

/-- `κ` at its cell `ℓ`, affine, as a value. -/
def kapV (ℓ : Loc) (H : Val) (K : Kont) : Val := ⟨kappaC true ℓ H K, by unfold kappaC; exact .lam⟩

/-- **The clause runs its work under the finaliser frame**: `[op]` at the operation `i = j`, at the
count `1?`, allocates `κ`'s cell at `ℓ` (`catch_cell`), and the clause steps to its work `g`
applied to `v`, under the frame `ubind (lastN, lastD)` around which `K₀` stands. -/
theorem last_op_work {μ : Heap} {ℓ : Loc} (hℓ : μ ℓ = none) {n i : UInt32}
    {E : List (Count × VTy × VTy)} {vr vw vn : Val} {j : Nat} (hj : j < E.length)
    (hji : i.toNat = j) (hq : E[j].1 = .opt)
    {K : Kont} (hK : K.HasHnd n = false) {g v : Val}
    (hg : PureSteps (pickE j (.val vw)) (.val g)) (K₀ : Kont) :
    Steps (ℍ := ℍ) μ (K₀.plug (hndE (lastH n E vr vw vn) (K.plug (performE (.val (opPayload n i v))))))
      (μ.upd ℓ .unit)
      (K₀.plug ((ubindK (lastN j (kapV ℓ (lastH n E vr vw vn) K) vn)
        (lastD (kapV ℓ (lastH n E vr vw vn) K))).plug (.app (.val g) (.val v)))) := by
  have hc : clauseAt (lastTuple E 0 (.val vw) (.val vn)) i.toNat =
      some ⟨lastClause j false (.val vw) (.val vn), isVal_lastClause _ _ _ _⟩ := by
    rw [hji, clauseAt_lastTuple _ _ E 0 j hj, hq, Nat.zero_add]
    rfl
  have htag : capTag (qualsVal (E.map Prod.fst)).1 i.toNat = Qual.aff.tag := by
    rw [hji, capTag_qualsVal _ j (by simpa using hj)]
    simp [hq, Count.toQual]
  have h₁ := catch_cell (ℍ := ℍ) (qs := qualsVal (E.map Prod.fst)) (hr := vr)
    (hs := ⟨lastTuple E 0 (.val vw) (.val vn), isVal_lastTuple _ _ E 0⟩) hℓ v (q := .aff)
    (by decide) hc hK htag K₀
  refine h₁.trans ?_
  have h₂ := DivDrive.pure_steps (ℍ := ℍ) (lastClause_steps j vw vn g v
    (kapV ℓ (lastH n E vr vw vn) K) hg) (μ.upd ℓ .unit)
  exact h₂.plug K₀

/-- **The resume ending** (`effHandleL`). A work that runs to `inl y` resumes the handled
computation at `y` where the operation was performed, the handler around it, `κ`'s cell released.
`[spec §51, §54]` -/
theorem last_resume_direct {μ μ₁ : Heap} {ℓ : Loc} (hℓ : μ ℓ = none) {n i : UInt32}
    {E : List (Count × VTy × VTy)} {vr vw vn : Val} {j : Nat} (hj : j < E.length)
    (hji : i.toNat = j) (hq : E[j].1 = .opt)
    {K : Kont} (hK : K.HasHnd n = false) {g v y : Val}
    (hg : PureSteps (pickE j (.val vw)) (.val g))
    (hw : Steps (ℍ := ℍ) (μ.upd ℓ .unit) (.app (.val g) (.val v)) μ₁ (.val (Val.inj₁ y)))
    (hℓ₁ : μ₁ ℓ = some .unit) (K₀ : Kont) :
    Steps (ℍ := ℍ) μ (K₀.plug (hndE (lastH n E vr vw vn) (K.plug (performE (.val (opPayload n i v))))))
      (μ₁.del ℓ) (K₀.plug (hndE (lastH n E vr vw vn) (K.plug (.val y)))) := by
  let H := lastH n E vr vw vn
  let κ := kapV ℓ H K
  refine (last_op_work hℓ hj hji hq hK hg K₀).trans ?_
  refine ((hw.plug (ubindK (lastN j κ vn) (lastD κ))).plug K₀).trans ?_
  refine ((DivDrive.pure_steps (ℍ := ℍ) (lastN_inl j κ vn y) μ₁).plug K₀).trans ?_
  exact kappaC_resume hℓ₁ true H K y K₀

/-- **The cancel ending** (`effHandleL`). A work that runs to `inr z` cancels `κ`: the
configuration reaches `κ`'s cancel run `cancelOf K`, the dead region from the cancel under its
delimiter, under the exit's frame, `κ`'s cell released.  `[spec §51, §54]` -/
theorem last_cancel_direct {μ μ₁ : Heap} {ℓ : Loc} (hℓ : μ ℓ = none) {n i : UInt32}
    {E : List (Count × VTy × VTy)} {vr vw vn : Val} {j : Nat} (hj : j < E.length)
    (hji : i.toNat = j) (hq : E[j].1 = .opt)
    {K : Kont} (hK : K.HasHnd n = false) {g v z : Val}
    (hg : PureSteps (pickE j (.val vw)) (.val g))
    (hw : Steps (ℍ := ℍ) (μ.upd ℓ .unit) (.app (.val g) (.val v)) μ₁ (.val (Val.inj₂ z)))
    (hℓ₁ : μ₁ ℓ = some .unit) (K₀ : Kont) :
    Steps (ℍ := ℍ) μ (K₀.plug (hndE (lastH n E vr vw vn) (K.plug (performE (.val (opPayload n i v))))))
      (μ₁.del ℓ) (K₀.plug ((exitK j vn z).plug (cancelOf K))) := by
  let H := lastH n E vr vw vn
  let κ := kapV ℓ H K
  refine (last_op_work hℓ hj hji hq hK hg K₀).trans ?_
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
delimiter. -/
theorem cancelOf_steps (μ : Heap) (K : Kont) (hK : K.dead.Catches 0 = false) :
    Steps (ℍ := ℍ) μ (cancelOf K) μ (.val .unit) :=
  .one (Step1.head (Head.cancel μ K.dead hK))

/-- **The tail-resuming rule's direct call** (`effHandleT`, SPEC §14, §54): at an operation
`i = j` whose count is not `0`, whose answering function `g` (the `j`-th of the tuple `vc`)
applied to `v` runs to `w`, the configuration reaches `hnd H K[w]`, the handler around the rest
of the handled computation, `κ`'s cell released: `[op]` and the cell (`catch_cell`), the clause up
to `g v` under the resume frame (`tailClause_steps`), `g`'s run, the resume frame (`resK_steps`)
and `κ`'s resume at its cell (`kappaC_resume`).  `[spec §14, §54]` -/
theorem tail_resume_direct {μ μ₁ : Heap} {ℓ : Loc} (hℓ : μ ℓ = none) {n i : UInt32}
    {E : List (Count × VTy × VTy)} {vr vc : Val} {j : Nat} (hj : j < E.length)
    (hji : i.toNat = j) (hB : E[j].1 ≠ .zero)
    {K : Kont} (hK : K.HasHnd n = false) {g v w : Val}
    (hg : PureSteps (pickE j (.val vc)) (.val g))
    (hw : Steps (ℍ := ℍ) (μ.upd ℓ .unit) (.app (.val g) (.val v)) μ₁ (.val w))
    (hℓ₁ : μ₁ ℓ = some .unit) (K₀ : Kont) :
    Steps (ℍ := ℍ) μ (K₀.plug (hndE (tailH n E vr vc) (K.plug (performE (.val (opPayload n i v))))))
      (μ₁.del ℓ) (K₀.plug (hndE (tailH n E vr vc) (K.plug (.val w)))) := by
  let H := tailH n E vr vc
  have hc : clauseAt (tailTuple E 0 (.val vc)) i.toNat =
      some ⟨tailClause j false (.val vc), isVal_tailClause _ _ _⟩ := by
    rw [hji, clauseAt_tailTuple _ E 0 j hj, beq_false_of_ne hB, Nat.zero_add]
  have htag : capTag (qualsVal (E.map Prod.fst)).1 i.toNat = E[j].1.toQual.tag := by
    rw [hji, capTag_qualsVal _ j (by simpa using hj)]
    simp
  have h₁ := catch_cell (ℍ := ℍ) (qs := qualsVal (E.map Prod.fst)) (hr := vr)
    (hs := ⟨tailTuple E 0 (.val vc), isVal_tailTuple _ E 0⟩) hℓ v (Count.toQual_ne_unr _) hc hK
    htag K₀
  refine h₁.trans ?_
  let κ : Val := ⟨kappaC (cellAff E[j].1.toQual) ℓ H K, by unfold kappaC; exact .lam⟩
  refine ((DivDrive.pure_steps (ℍ := ℍ) (tailClause_steps j vc g v κ hg) _).plug K₀).trans ?_
  refine ((hw.plug (resK κ)).plug K₀).trans ?_
  refine ((DivDrive.pure_steps (ℍ := ℍ) (resK_steps κ w) μ₁).plug K₀).trans ?_
  exact kappaC_resume hℓ₁ _ H K w K₀

end LastRuns

/-! ### The clause conversion: an open statement  `[spec §54]`

The checker writes an `effHandleT` node where its classification of a `[handle]` node's clauses
is `tail` (SPEC §54): the clause `λp. let (x, κ) = p; M` of an operation is replaced by the
rule's clause `tailClause j false vc`, whose `j`-th answering function is the work `λx. M′`, `M′`
the body `M` with each resume replaced by its answer (`TailResumesAt 0 M M′`), `κ`'s binder
dropped. `ClauseTailReplace` states that the two clauses, applied to an argument and a
continuation, reach the same values at the same memories. It is not proved here: no result
depends on it. The route its proof is to take composes `tail_resumes_answer` with
`TailResumesAt.subst_kappa`, as `OnPaths.rebind`'s does. -/

/-- **The clause conversion of the tail-resuming rule** (`clause_tail_replace`, SPEC §54), stated,
not proved: at a body `M` that resumes `κ` (its slot `0`) in tail position on every path, with
`M′` its answer (`TailResumesAt 0 M M′`), and a tuple `vc` whose `j`-th component is the work
`λx. M′` (`κ`'s binder dropped, `M′.subst 0 ()`), the clause `λp. let (x, κ) = p; M` and the rule's
clause `tailClause j false vc`, applied to `(v, κ)` at a closed `κ`, run to the same values at the
same memories. -/
def ClauseTailReplace (ℍ : BoCa.Host) [BoCa.HostIs ℍ] : Prop :=
  ∀ {M M' : Expr}, ClauseKinds.TailResumesAt 0 M M' →
  ∀ (j : Nat) (vc g : Val), PureSteps (pickE j (.val vc)) (.val g) →
    g.1 = .lam (M'.subst 0 .unit) →
  ∀ (v κ : Val), closedAt 0 κ.1 = true →
  ∀ (μ μ' : BoCa.BoLo.Heap) (w : Val),
    BoCa.BoLo.Steps (ℍ := ℍ) μ (.app (.lam (.letpair (.var 0) M)) (.val (Val.pair v κ))) μ' w.1 ↔
      BoCa.BoLo.Steps (ℍ := ℍ) μ (.app (tailClause j false (.val vc)) (.val (Val.pair v κ))) μ' w.1

/-! #### Its hypotheses, met at a corpus clause

`corpus/core-effects-tail.bc`'s clause, erased (`bcc erase`), is `λp. let (u, κ) = p; M` with
`M = u; (λx. κ.1 x) 10`: `M` resumes `κ` in tail position (`TailResumesAt 0 M M′`, through `[1E]`
and `[let]`), `M′ = u; (λx. x) 10`, and the tuple `(λu. M′[()/κ], ())` holds the work at `0`. So
`ClauseTailReplace`'s hypotheses are met there, and the statement is not vacuous. -/

/-- `core-effects-tail`'s clause body, `κ` in the slot `0` and `u` in `1`. -/
def cetBody : Expr :=
  .seq (.var 1) (.app (.lam (.app (ClauseKinds.resumeAt 1) (.var 0))) (.prim (.lit (.i32 10))))

/-- The body without its resume. -/
def cetBody' : Expr := .seq (.var 1) (.app (.lam (.var 0)) (.prim (.lit (.i32 10))))

/-- The work: the body without its resume, `κ`'s binder dropped. -/
def cetWork : Val := ⟨.lam (cetBody'.subst 0 .unit), .lam⟩

/-- **`ClauseTailReplace`'s hypotheses at `core-effects-tail`'s clause**: the body resumes in tail
position with `cetBody'` its answer, and the tuple `(cetWork, ())` gives the work at `0`. -/
theorem cet_clauseTailReplace_hyps :
    ClauseKinds.TailResumesAt 0 cetBody cetBody' ∧
      PureSteps (pickE 0 (.val (Val.pair cetWork Val.unit))) (.val cetWork) ∧
      cetWork.1 = .lam (cetBody'.subst 0 .unit) := by
  refine ⟨?_, pickE_steps 0 cetWork Val.unit _ rfl cetWork (fun _ => rfl)
    (fun _ h => by cases h), rfl⟩
  exact .seq (by simp [ClauseKinds.mentions])
    (.bind (by simp [ClauseKinds.mentions]) (.resume (by simp [ClauseKinds.mentions])))

/-! ### The node's removal: an open statement  `[spec §54]`

R1 (SPEC §54) makes every `perform` of an admitted name a call of its work, and then removes the
name's node: `handle_n e with (h, gs)` becomes `e to a. h a`. `HandleTransparent` states that a
handler is transparent over a computation that performs none of its operations: the two reach the
same values at the same memories. It is not proved here: no result depends on it. The route its
proof is to take composes `catch_ret` (the node's answer clause at a value) with the frame's
invisibility to every step that is not a `perform` of its name. -/

/-- **A handler's transparency** (`HandleTransparent`, SPEC §54), stated, not proved: at a handler
value `hndVal n qs hr hs` and a computation `e` none of whose runs, from any memory, reaches a
`perform` of an operation of `n`, `hnd H e` and `(λa. hr a) e` (the computation's answer handed to
the answer clause) run to the same values at the same memories. -/
def HandleTransparent (ℍ : BoCa.Host) [BoCa.HostIs ℍ] : Prop :=
  ∀ (n : UInt32) (qs hr hs : Val) (e : Expr),
    (∀ {μ μ' : BoCa.BoLo.Heap} {e' : Expr}, BoCa.BoLo.Steps (ℍ := ℍ) μ e μ' e' →
      ∀ (K : Kont) (i : UInt32) (v : Val), e' ≠ K.plug (performE (.val (opPayload n i v)))) →
  ∀ (μ μ' : BoCa.BoLo.Heap) (w : Val),
    BoCa.BoLo.Steps (ℍ := ℍ) μ (hndE (hndVal n qs hr hs) e) μ' w.1 ↔
      BoCa.BoLo.Steps (ℍ := ℍ) μ (.app (.lam (.app (hr.1.shift 1 0) (.var 0))) e) μ' w.1

/-- **`HandleTransparent`'s hypothesis at a value**: a run from a value performs nothing, so the
statement is not vacuous. -/
theorem handleTransparent_hyp_val (n : UInt32) (w : Val) :
    ∀ {μ μ' : BoCa.BoLo.Heap} {e' : Expr}, BoCa.BoLo.Steps (ℍ := ℍ) μ w.1 μ' e' →
      ∀ (K : Kont) (i : UInt32) (v : Val), e' ≠ K.plug (performE (.val (opPayload n i v))) := by
  intro μ μ' e' h K i v he
  obtain ⟨_, h₂⟩ := BoCa.BoLo.steps_val_inv (w := w) h
  exact plug_perform_ne_val K (opPayload n i v) w (he ▸ h₂)

end BoCa.Fig16.LogRel.Core
