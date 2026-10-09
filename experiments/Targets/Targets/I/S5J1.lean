import Targets.I.J1
import Targets.I.Theories
import Targets.I.CancelsNZ
import Targets.B.HeapFrame
import Targets.Instance.CancelRuns
import Targets.Instance.UnaryLaws
import Targets.A.CancelWhole

/-!
# The interaction — S5 at `J₁` (decision S5)

S5 (`Cancellation noFinRaise`, `Targets/A/Soundness.lean`) carries the no-interception condition
explicitly (decision D4): the finalisers a cancel or an unwind fires are closed programs typed at a
row of abortive operations of `FR`'s labels (`FinRow`); at option A (`noFinRaise`) that row admits
nothing.  It reads every run from the start of a cancel or an unwind as a prefix of a trace.

* **What typing gives about such a finaliser** (`finOK_of_finRow`): at a typing system whose closed
  programs are Core's, the row it is typed at is tied to the effect context, and a tied row that
  admits nothing is empty; so Core's kernel types it at `F 1`, FL puts it in Core's relation there,
  and it runs to `()` from every finite memory (`runs_of_rel_unit`).  This is the hypothesis the
  instance's traces read (`FinOK`).  It does not read `FinRowsAt`: decision D4 put the finaliser's
  typing into S5's statement, so the bridges need it only for the finalisers S5 names.
* **S5's unwind**: PROVED at `J₁` (`unwindOrder_J₁`) and at today's kernel
  (`cancellation_tier1Open`), at every effect context.
* **S5's no-interception**: PROVED at `J₁` (`noIntercept_J₁_of`) and at today's kernel, given that
  a cancelled continuation's running finalisers hold kept errors the labels read (`CancelsNamed`:
  every `cfin` frame of the region holds none or a raise of a label's name; a whole-run fact about
  the names finalisers raise).  The cancel runs the dead region `K†`, which holds no handler and no
  `ccatch` frame, so the cancel trace passes a running finaliser's `cfin` frame by `[cfin-cancel]`
  (`pend`), and reads no handler name; no handler named `0` is a run invariant read by nothing here
  (`cancelsNZ_J₁`, `Targets/I/CancelsNZ.lean`).
* **The extension a run needs is the β-step after a fire** (`Inst.unwind_pfx`, `Inst.cancel_pfx`,
  `Inst.FireExt`): a run is a trace as it is, or, when it stops right after a fire step, once the
  β-step that starts the finaliser is taken.
* **S5 read whole fails** (kept as a record, `A.CancellationWhole`) at every typing system that
  types `fireProg` and `(); ()` (`not_unwindOrderWhole_of_types`), so at `J₁`
  (`not_unwindOrderWhole_J₁`, `not_cancellationWhole_J₁`) and at today's kernel
  (`not_unwindOrderWhole_tier1Open`, `not_cancellationWhole_tier1Open`), at every effect context
  declaring `exn : 1 ↠ 0` at the name `1`, among them the admissible `ΞA`
  (`not_cancellationWhole_ΞA`, `not_cancellationWhole_admissible`).  `fireProg` is
  `handle_exn (raise exn () then x. x unwind ((); ()))`; its run reaches the raise under the
  finaliser frame, where every premise of the unwind holds (`fireProg_premises`), and the path of
  its one fire step follows no unwind trace: `[finalise]` leaves `((λ_. (); ()) ()); raise p`, the
  finaliser `(); ()` is not yet at an evaluation position, and `UnwindTrace.fire` reads the fire
  step's administrative steps whole.  At the same configuration S5 holds (`unwindOrder_fireProg`):
  one more step, the β-step, and the path is a trace.

`[Core σ=[]]`
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets.I
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont performE raiseE opPayload hndE ubindE hndVal)
open BoCa.Lifetime (LSub LifeCtx)
open Targets (RowForm EffCtx orowRF orowAlg ORow RowAt rowAt_nil lookRun lookEnd lookRun_sound)
open Targets.Inst (OVTy OCTy OurTyping ourInst J₁ J1DerAt CoreClosed coreClosed_J₁At FinOK
  LiveOK liveOK_of_coreClosed der_cases effOf_inj)

/-! ### What typing gives about a finaliser that meets the no-interception condition -/

section Fin
variable {Ξ : EffCtx} {D : Targets.RowCtx → LifeCtx → Ctx OVTy → Expr → Inst.OJdg → Prop}

local notation "𝕊" => ourInst (ℍ := ℍ) orowRF Ξ (OurTyping.ofDer D)

/-- A row whose every key finds nothing is empty. -/
theorem row_nil_of_find_none : ∀ {S : Row}, (∀ n i, Row.find S n i = none) → S = []
  | [], _ => rfl
  | o :: _, h => by
      have := h o.n o.i
      simp [Row.find, List.find?] at this

/-- **A finaliser that meets S5's no-interception condition at option A runs to `()` from every
finite memory**, at a typing system whose closed programs are Core's.  Its row admits no label's
operation; tied to the effect context, every operation it finds is a label's, so it finds nothing
and is empty.  Core's kernel types the finaliser at `F 1` (`der_cases`), so it is in Core's
relation there, and runs to `()` from every finite memory (`runs_of_rel_unit`). -/
theorem finOK_of_finRow (hJ : CoreClosed (OurTyping.ofDer D)) {Dt : Expr}
    (h : (𝕊).FinRow (𝕊).noFinRaise Dt) {μ : Heap} (hfin : FinDom μ) : FinOK (ℍ := ℍ) μ Dt := by
  obtain ⟨ε, hε, hder⟩ := h
  obtain ⟨S, A₀, hC, hS, hrel⟩ := Inst.der_cases hJ hder
  change CTy.effOf (ε.ops ++ (match ε.tail with | none => [] | some ρ => ([] : Row))) .unit =
    CTy.effOf S A₀ at hC
  obtain ⟨hSe, rfl⟩ := effOf_inj hC
  have hnil : ε.ops ++ (match ε.tail with | none => [] | some _ => ([] : Row)) = ε.ops := by
    cases ε.tail <;> simp
  rw [hnil] at hSe
  subst hSe
  -- the row finds nothing
  have hnone : ∀ n i, Row.find ε.ops n i = none := by
    intro n i
    cases hf : Row.find ε.ops n i with
    | none => rfl
    | some o =>
        exfalso
        obtain ⟨hn0, hlen, hget⟩ := hS n i o hf
        have hne : Ξ n ≠ [] := by
          intro h0; rw [h0] at hget; simp at hget
        let l : (orowAlg Ξ).Lab := ⟨n, hn0, hne, hlen⟩
        refine (hε l i.toNat ⟨UInt32.toNat_lt i, fun η => ?_⟩).1
        change (Row.find (ε.ops ++ _) n (UInt32.ofNat i.toNat)).isSome = true
        rw [UInt32.ofNat_toNat, Row.find_append, hf]
        rfl
  rw [row_nil_of_find_none hnone] at hrel
  rcases hrel with hrel | ⟨M, S₀, A₁, -, -, -, hA, -⟩
  · intro μ₁ e₁ hs
    exact runs_of_rel_unit hrel hfin hs
  · cases hA

end Fin

/-! ### S5 at `J₁`, prefix-closed -/

section J1
variable {Ξ : EffCtx}

/-- A label's name is not the reserved `0`. -/
theorem name_ne_zero_orow (l : (orowAlg Ξ).Lab) : orowRF.name Ξ l ≠ 0 := l.2.1

/-- At `J₁`, a finaliser that meets the no-interception condition at option A runs to `()` from
every finite memory. -/
theorem finOK_J₁ {Dt : Expr}
    (h : (ourInst (ℍ := ℍ) orowRF Ξ J₁).FinRow (ourInst (ℍ := ℍ) orowRF Ξ J₁).noFinRaise Dt)
    {μ : Heap} (hfin : FinDom μ) : FinOK (ℍ := ℍ) μ Dt :=
  finOK_of_finRow (D := J1DerAt Ξ) (coreClosed_J₁At Ξ) h hfin

/-- **S5's unwind at `J₁`**, at every effect context: every run from a raise pending under a
context of A's unwinding shape is a prefix of an unwind trace — a trace as it is, or once the
β-step after a fire step is taken. -/
theorem unwindOrder_J₁ :
    (ourInst (ℍ := ℍ) orowRF Ξ J₁).UnwindOrder (ourInst (ℍ := ℍ) orowRF Ξ J₁).noFinRaise :=
  Inst.unwindOrder_of_core liveOK_J₁ name_ne_zero_orow (fun _ h _ hμ => finOK_J₁ h hμ)

/-- **S5's no-interception at `J₁`**, at every effect context, given that every cancelled
continuation's running finalisers hold kept errors the labels read. -/
theorem noIntercept_J₁_of (hN : Inst.CancelsNamed (ℍ := ℍ) orowRF Ξ J₁) :
    (ourInst (ℍ := ℍ) orowRF Ξ J₁).NoIntercept (ourInst (ℍ := ℍ) orowRF Ξ J₁).noFinRaise :=
  Inst.noIntercept_of_core liveOK_J₁ (fun _ h _ hμ => finOK_J₁ h hμ) hN

/-- **S5 at `J₁`**, at every effect context, given `CancelsNamed`. -/
theorem cancellation_J₁_of (hN : Inst.CancelsNamed (ℍ := ℍ) orowRF Ξ J₁) :
    (ourInst (ℍ := ℍ) orowRF Ξ J₁).Cancellation (ourInst (ℍ := ℍ) orowRF Ξ J₁).noFinRaise :=
  ⟨noIntercept_J₁_of hN, unwindOrder_J₁⟩

/-- **S5 at today's kernel**: the unwind at every effect context, the no-interception given
`CancelsNamed`. -/
theorem cancellation_tier1Open :
    (ourInst (ℍ := ℍ) orowRF Ξ Inst.tier1Open).UnwindOrder
        (ourInst (ℍ := ℍ) orowRF Ξ Inst.tier1Open).noFinRaise ∧
      (Inst.CancelsNamed (ℍ := ℍ) orowRF Ξ Inst.tier1Open →
        (ourInst (ℍ := ℍ) orowRF Ξ Inst.tier1Open).NoIntercept
          (ourInst (ℍ := ℍ) orowRF Ξ Inst.tier1Open).noFinRaise) :=
  have hF : ∀ D, (ourInst (ℍ := ℍ) orowRF Ξ Inst.tier1Open).FinRow
      (ourInst (ℍ := ℍ) orowRF Ξ Inst.tier1Open).noFinRaise D → ∀ μ, FinDom μ → FinOK (ℍ := ℍ) μ D :=
    fun _ h _ hμ => finOK_of_finRow (D := Inst.tier1OpenDer) Inst.coreClosed_tier1Open h hμ
  ⟨Inst.unwindOrder_of_core Inst.liveOK_tier1Open name_ne_zero_orow hF,
    fun hN => Inst.noIntercept_of_core Inst.liveOK_tier1Open hF hN⟩

end J1

/-! ### S5 read whole fails at `J₁` -/

/-- The finaliser `(); ()`: at the pure row, and no value. -/
def finSeq : Expr := .seq .unit .unit

/-- `handle_exn (raise exn () then x. x unwind ((); ())) with (λ_. ())`, `exn` at the name `1`. -/
def fireProg : Expr :=
  Inst.withH 1 .aff Inst.abortCl (thenE (.var 0) finSeq (raiseE (opArgE 1 0 (.val .unit))))

/-- The handler of `exn`, after the program's two `let`s. -/
def fireK₀ : Kont := Inst.handleK 1 (qualsVal [.aff]).1 (.lam (.var 0)) [Inst.abortCl]

/-- The raise `exn ()`, as Core's operation at its payload. -/
abbrev fireRaise : Expr := raiseE (.val (opPayload 1 0 Val.unit))

/-- The program's run reaches the raise under the finaliser frame, inside the handler. -/
theorem fireProg_c : lookEnd 2 fireProg =
    fireK₀.plug ((Inst.thenK (.var 0) finSeq).plug fireRaise) := by
  rfl

/-- What the fire step reaches: the finaliser `λ_. (); ()` applied to `()`, then the raise. -/
abbrev fireAfter : Expr :=
  fireK₀.plug (.seq (.app (.val (Val.lam (finSeq.shift 1 0))) (.val Val.unit)) fireRaise)

/-- `(); ()` at a term's subterm. -/
def seqUnitShape : Expr → Bool
  | .seq .unit .unit => true
  | _ => false

theorem noFin_fireAfter : (Inst.evalSubs fireAfter).any seqUnitShape = false := by decide

/-- After the fire step, the finaliser `(); ()` is at no evaluation position. -/
theorem fireAfter_ne (Kf : Kont) : fireAfter ≠ Kf.plug finSeq := by
  intro h
  have := Inst.any_evalSubs_plug (p := seqUnitShape) Kf (s := finSeq) rfl
  rw [← h, noFin_fireAfter] at this
  cases this

section Fail
variable {Ξ : EffCtx}

/-- **`fireProg` is typed by `J₁`'s kernel at `Ξ`**, with its rows tied, at every effect context
declaring `exn : 1 ↠ 0` at the name `1`. -/
theorem d_fireProg (h1 : Ξ 1 = Inst.Eab) :
    Targets.CDerivesAt Ξ LifeCtx.empty [] fireProg (.comp (.ret .unit)) := by
  refine Inst.d_withHAt (S := []) (Targets.rowAt_ofEff_append h1 (by decide) (by simp) (rowAt_nil Ξ))
    (by decide) (by simp) .nil (Inst.d_abortClAt (S := []) .nil) ?_
  refine .effThen (A := .unit) (deadSplit (by cdead)) ?_ ?_
    (fun h => absurd h (by simp [Row.UnrD, Row.ofEff, capB])) ?_ ?_ ?_
  · intro o ho; simp [Row.ofEff] at ho; subst ho; decide
  · simp [Row.Uniq, Row.ofEff]
  · exact .effRaise (o := ⟨1, 0, .aff, .unit, .zero, .ret .unit⟩)
      (Targets.rowAt_ofEff_append h1 (by decide) (by simp) (rowAt_nil Ξ)) rfl rfl .unit
      (.unitI (by cdead))
  · exact .effSub (S := []) (Inst.rowLe_nil _) (.ret (.var (.here (by cdead))))
  · exact .unitE (deadSplit (by cdead)) (.unitI (by cdead)) (.ret (.unitI (by cdead)))

/-- `(); ()` is typed by `J₁` as a closed program at the pure row. -/
theorem der_finSeq_J₁ :
    (ourInst (ℍ := ℍ) orowRF Ξ J₁).der [] finSeq
      ((ourInst (ℍ := ℍ) orowRF Ξ J₁).F (orowAlg Ξ).unit (OVTy.ofV .unit)) :=
  Inst.der_J₁_ret rfl (.unitE (deadSplit .nil) (.unitI .nil) (.ret (.unitI .nil)))

/-- `exn`, the label of the name `1`. -/
def lab₁ (h1 : Ξ 1 = Inst.Eab) : (orowAlg Ξ).Lab := ⟨1, by decide, by rw [h1]; simp, by rw [h1]; simp⟩

/-- **The premises of S5's unwind, met at `fireProg`'s raise under its finaliser frame**, at every
typing system that types `fireProg` and `(); ()` at the pure row: the runner answers nothing, the
configuration is reached, the context is one finaliser frame (A's shape) holding no handler of
`exn`, its finaliser `(); ()` meets the no-interception condition (a closed program at the pure
row), and the fire step is a path. -/
theorem fireProg_premises {J : OurTyping orowRF} (h1 : Ξ 1 = Inst.Eab)
    (hder : (ourInst (ℍ := ℍ) orowRF Ξ J).der [] fireProg
      ((ourInst (ℍ := ℍ) orowRF Ξ J).F (orowAlg Ξ).unit (OVTy.ofV .unit)))
    (hseq : (ourInst (ℍ := ℍ) orowRF Ξ J).der [] finSeq
      ((ourInst (ℍ := ℍ) orowRF Ξ J).F (orowAlg Ξ).unit (OVTy.ofV .unit))) :
    (ourInst (ℍ := ℍ) orowRF Ξ J).RReach (ourInst (ℍ := ℍ) orowRF Ξ J).R₀
        ((ourInst (ℍ := ℍ) orowRF Ξ J).rinit (ourInst (ℍ := ℍ) orowRF Ξ J).R₀ fireProg)
        ((Adequacy.emptyMem, lookEnd 2 fireProg), ()) ∧
      (ourInst (ℍ := ℍ) orowRF Ξ J).Std (Inst.thenK (.var 0) finSeq) ∧
      (ourInst (ℍ := ℍ) orowRF Ξ J).term (Adequacy.emptyMem, lookEnd 2 fireProg) =
        (ourInst (ℍ := ℍ) orowRF Ξ J).plug fireK₀ ((ourInst (ℍ := ℍ) orowRF Ξ J).plug
          (Inst.thenK (.var 0) finSeq)
          ((ourInst (ℍ := ℍ) orowRF Ξ J).raise (lab₁ h1) 0 (ourInst (ℍ := ℍ) orowRF Ξ J).unitV)) ∧
      (ourInst (ℍ := ℍ) orowRF Ξ J).catches (Inst.thenK (.var 0) finSeq) (lab₁ h1) = false ∧
      (∀ D ∈ (ourInst (ℍ := ℍ) orowRF Ξ J).fins (Inst.thenK (.var 0) finSeq),
        (ourInst (ℍ := ℍ) orowRF Ξ J).FinRow (ourInst (ℍ := ℍ) orowRF Ξ J).noFinRaise D) ∧
      (ourInst (ℍ := ℍ) orowRF Ξ J).RPath (ourInst (ℍ := ℍ) orowRF Ξ J).R₀
        ((Adequacy.emptyMem, lookEnd 2 fireProg), ())
        [(.fire finSeq, ((Adequacy.emptyMem, fireAfter), ()))] := by
  have hreach := Inst.rreach_of_chain (RF := orowRF) (Ξ := Ξ) (J := J)
    (ourInst (ℍ := ℍ) orowRF Ξ J).R₀ (μ := Adequacy.emptyMem) (s := ())
    (lookRun_sound (ℍ := ℍ) 2 fireProg)
  have hstd : (ourInst (ℍ := ℍ) orowRF Ξ J).Std (Inst.thenK (.var 0) finSeq) :=
    @A.EffectSystem.Std.frame (ourInst (ℍ := ℍ) orowRF Ξ J) Kont.hole Kont.hole
      ((ourInst (ℍ := ℍ) orowRF Ξ J).thenF (.var 0) finSeq) (show Kont.NoUnwind .hole from trivial)
      (.inr ⟨_, _, rfl⟩) (.clear (show Kont.NoUnwind .hole from trivial))
  have hfin : ∀ D ∈ (ourInst (ℍ := ℍ) orowRF Ξ J).fins (Inst.thenK (.var 0) finSeq),
      (ourInst (ℍ := ℍ) orowRF Ξ J).FinRow (ourInst (ℍ := ℍ) orowRF Ξ J).noFinRaise D := by
    intro D hD
    rw [show (ourInst (ℍ := ℍ) orowRF Ξ J).fins (Inst.thenK (.var 0) finSeq) = [finSeq] from
      Inst.thenK_fins (.var 0) finSeq] at hD
    obtain rfl := List.mem_singleton.1 hD
    refine ⟨(orowAlg Ξ).unit, fun l i hh => ?_, hseq⟩
    obtain ⟨-, hh⟩ := hh
    have := hh (fun _ => [])
    simp [Targets.Row.Has, Row.find] at this
  have hstep : (ourInst (ℍ := ℍ) orowRF Ξ J).RStep (ourInst (ℍ := ℍ) orowRF Ξ J).R₀
      ((Adequacy.emptyMem, lookEnd 2 fireProg), ()) (.fire finSeq)
      ((Adequacy.emptyMem, fireAfter), ()) := by
    rw [fireProg_c]
    exact Inst.rstep_fire (RF := orowRF) (Ξ := Ξ) (J := J)
      (R := (ourInst (ℍ := ℍ) orowRF Ξ J).R₀) (n := 1) (i := 0) (v := Val.unit) ()
      Adequacy.emptyMem fireK₀ .hole (.var 0) finSeq (by decide) rfl
  exact ⟨hreach, hstd, by rw [fireProg_c]; rfl, rfl, hfin, .cons hstep .nil⟩

/-- **S5's unwind read whole fails at every typing system that types `fireProg` and `(); ()`**, at
every effect context declaring `exn : 1 ↠ 0` at the name `1`: at `fireProg`'s raise under its
finaliser frame, where every premise holds (`fireProg_premises`), the path of the fire step alone
follows no unwind trace. -/
theorem not_unwindOrderWhole_of_types {J : OurTyping orowRF} (h1 : Ξ 1 = Inst.Eab)
    (hder : (ourInst (ℍ := ℍ) orowRF Ξ J).der [] fireProg
      ((ourInst (ℍ := ℍ) orowRF Ξ J).F (orowAlg Ξ).unit (OVTy.ofV .unit)))
    (hseq : (ourInst (ℍ := ℍ) orowRF Ξ J).der [] finSeq
      ((ourInst (ℍ := ℍ) orowRF Ξ J).F (orowAlg Ξ).unit (OVTy.ofV .unit))) :
    ¬ (ourInst (ℍ := ℍ) orowRF Ξ J).UnwindOrderWhole (ourInst (ℍ := ℍ) orowRF Ξ J).noFinRaise := by
  intro h
  obtain ⟨hreach, hstd, hterm, hcat, hfin, hq⟩ := fireProg_premises (ℍ := ℍ) h1 hder hseq
  have htr := h (ourInst (ℍ := ℍ) orowRF Ξ J).R₀ Inst.r₀_respects fireProg _ _
    (Inst.answers_unit _) hder _ fireK₀ (Inst.thenK (.var 0) finSeq) (lab₁ h1) 0
    (ourInst (ℍ := ℍ) orowRF Ξ J).unitV _ hreach hstd hterm hcat hfin hq
  exact Inst.not_unwindTrace_one (fun Kf h' => fireAfter_ne Kf h') htr

/-- **S5's unwind read whole fails at `J₁`**, at every effect context declaring `exn : 1 ↠ 0` at the
name `1`. -/
theorem not_unwindOrderWhole_J₁ (h1 : Ξ 1 = Inst.Eab) :
    ¬ (ourInst (ℍ := ℍ) orowRF Ξ J₁).UnwindOrderWhole (ourInst (ℍ := ℍ) orowRF Ξ J₁).noFinRaise :=
  not_unwindOrderWhole_of_types h1
    (Inst.der_J₁_ret (ℍ := ℍ) (Ξ := Ξ) (e := fireProg) (A := .unit) rfl (d_fireProg h1))
    der_finSeq_J₁

/-- `fireProg` in today's unr-free kernel. -/
theorem d_fireProgNU : Targets.CDerivesNU LifeCtx.empty [] fireProg (.comp (.ret .unit)) := by
  refine Inst.d_withHNU (S := []) (Inst.nu_ofEff_aff Inst.nu_nil) Inst.nu_nil (by decide) (by simp)
    .nil (Inst.d_abortClNU Inst.nu_nil .nil) ?_
  refine .effThen (A := .unit) (Inst.nu_ofEff_aff Inst.nu_nil) (deadSplit (by cdead)) ?_ ?_
    (fun h => absurd h (by simp [Row.UnrD, Row.ofEff, capB])) ?_ ?_ ?_
  · intro o ho; simp [Row.ofEff] at ho; subst ho; decide
  · simp [Row.Uniq, Row.ofEff]
  · exact .effRaise (o := ⟨1, 0, .aff, .unit, .zero, .ret .unit⟩) rfl rfl .unit (.unitI (by cdead))
  · exact .effSub (Inst.nu_ofEff_aff Inst.nu_nil) (Inst.rowLe_nil _)
      (.ret (.var (.here (by cdead))))
  · exact .unitE (deadSplit (by cdead)) (.unitI (by cdead)) (.ret (.unitI (by cdead)))

/-- **S5's unwind read whole fails at today's kernel** (`tier1Open`), at every effect context
declaring `exn : 1 ↠ 0` at the name `1`. -/
theorem not_unwindOrderWhole_tier1Open (h1 : Ξ 1 = Inst.Eab) :
    ¬ (ourInst (ℍ := ℍ) orowRF Ξ Inst.tier1Open).UnwindOrderWhole
      (ourInst (ℍ := ℍ) orowRF Ξ Inst.tier1Open).noFinRaise :=
  not_unwindOrderWhole_of_types h1 (Inst.der_tier1Open_ret d_fireProgNU)
    (Inst.der_tier1Open_ret (.unitE (deadSplit .nil) (.unitI .nil) (.ret (.unitI .nil))))

/-- **At the same configuration S5 holds** at `J₁`: the path of the fire step, followed by one step
of the run (the β-step that starts the finaliser), follows an unwind trace (`unwindOrder_J₁` at
`fireProg_premises`). -/
theorem unwindOrder_fireProg (h1 : Ξ 1 = Inst.Eab) :
    ∃ q', (ourInst (ℍ := ℍ) orowRF Ξ J₁).RPath (ourInst (ℍ := ℍ) orowRF Ξ J₁).R₀
        ((Adequacy.emptyMem, lookEnd 2 fireProg), ())
        ([(.fire finSeq, ((Adequacy.emptyMem, fireAfter), ()))] ++ q') ∧
      (ourInst (ℍ := ℍ) orowRF Ξ J₁).UnwindTrace (ourInst (ℍ := ℍ) orowRF Ξ J₁).R₀
        (ourInst (ℍ := ℍ) orowRF Ξ J₁).noFinRaise fireK₀
        ((Adequacy.emptyMem, lookEnd 2 fireProg), ()) (Inst.thenK (.var 0) finSeq)
        ([(.fire finSeq, ((Adequacy.emptyMem, fireAfter), ()))] ++ q') := by
  have hder := Inst.der_J₁_ret (ℍ := ℍ) (Ξ := Ξ) (e := fireProg) (A := .unit) rfl (d_fireProg h1)
  obtain ⟨hreach, hstd, hterm, hcat, hfin, hq⟩ :=
    fireProg_premises (ℍ := ℍ) h1 hder der_finSeq_J₁
  exact unwindOrder_J₁ (ourInst (ℍ := ℍ) orowRF Ξ J₁).R₀ Inst.r₀_respects fireProg _ _
    (Inst.answers_unit _) hder _ fireK₀ (Inst.thenK (.var 0) finSeq) (lab₁ h1) 0
    (ourInst (ℍ := ℍ) orowRF Ξ J₁).unitV _ hreach hstd hterm hcat hfin hq

/-- **S5 read whole fails at `J₁`**, at every effect context declaring `exn : 1 ↠ 0` at `1`. -/
theorem not_cancellationWhole_J₁ (h1 : Ξ 1 = Inst.Eab) :
    ¬ (ourInst (ℍ := ℍ) orowRF Ξ J₁).CancellationWhole (ourInst (ℍ := ℍ) orowRF Ξ J₁).noFinRaise :=
  fun h => not_unwindOrderWhole_J₁ h1 h.2

/-- **S5 read whole fails at today's kernel**, at every effect context declaring `exn : 1 ↠ 0` at
`1`. -/
theorem not_cancellationWhole_tier1Open (h1 : Ξ 1 = Inst.Eab) :
    ¬ (ourInst (ℍ := ℍ) orowRF Ξ Inst.tier1Open).CancellationWhole
      (ourInst (ℍ := ℍ) orowRF Ξ Inst.tier1Open).noFinRaise :=
  fun h => not_unwindOrderWhole_tier1Open h1 h.2

end Fail

/-- **S5 read whole fails at `J₁` at the admissible `ΞA`.** -/
theorem not_cancellationWhole_ΞA :
    ¬ (ourInst (ℍ := ℍ) orowRF Inst.ΞA J₁).CancellationWhole
      (ourInst (ℍ := ℍ) orowRF Inst.ΞA J₁).noFinRaise :=
  not_cancellationWhole_J₁ (by simp [Inst.ΞA])

theorem not_cancellationWhole_admissible :
    ¬ ∀ Ξ, Inst.AdmEff Ξ → (ourInst (ℍ := ℍ) orowRF Ξ J₁).CancellationWhole
      (ourInst (ℍ := ℍ) orowRF Ξ J₁).noFinRaise :=
  fun h => not_cancellationWhole_ΞA (h Inst.ΞA Inst.admEff_ΞA)

end Targets.I

end
