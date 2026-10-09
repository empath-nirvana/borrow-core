import Targets.I.AlgJ1
import Targets.Instance.CancelRuns
import Targets.Instance.Restricted.NoInterception

/-!
# The interaction — no run of a typed program creates a handler named `0`

A cancel's raise is named `0` (SPEC §19, `cancelVal`), and a handler frame of `0` in the region a
cancel tears down would catch it.  `CancelsStd`'s handler half (`CancelsNZ`,
`Targets/Instance/CancelRuns.lean`) asks that no cancelled continuation's context holds one.  At a
typing system whose closed programs are Core's it is a run invariant:

* **a typed program names no handler `0`** (I3.c, `okE_of_derives`): Core's kernel names a handler
  by a label of its row;
* **no machine step creates one** (`hndNZ_step1`; the stored values too, `HeapNZ`);
* **the runner answers with data**, which names no handler: a typed program asks the runner at
  data arguments only, since every run of a program in Core's relation keeps the platform's
  protocol (`platData_of_start`; a driven program's, `driveData_of_reach`), and the protocol answers
  a data argument with data (`Platform.Respects.typed`).

So every configuration a typed program reaches names no handler `0` (`hndNZ_reach`).  A cancelled
`κ = kappa H K` holds the continuation's context `K` in its resume branch `λy. hnd H K[y]`, shifted
past the branch's binders, and a shift keeps a context's handler names (`hasHnd_shift`); so `K` has
no handler of `0` (`cancelsNZ_of_coreClosed`; at `J₁`, `I.cancelsNZ_J₁`).  `[Core σ=[]]`
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont performE raiseE opPayload)
open BoCa.Lifetime (LSub)

/-! ### A shift keeps handler names -/

/-- A frame is a handler frame of name `m` exactly when its shift is. -/
theorem hndFrame_shift_iff (f : Expr) (d c : ℕ) (m : UInt32) :
    (∃ x, f.shift d c = .app (.prim .hnd) (.pair (.prim (.lit (.i32 m))) x)) ↔
      ∃ x, f = .app (.prim .hnd) (.pair (.prim (.lit (.i32 m))) x) := by
  constructor
  · rintro ⟨x, h⟩
    cases f with
    | var i => simp only [Expr.shift] at h; split at h <;> cases h
    | app g a =>
        simp only [Expr.shift, Expr.app.injEq] at h
        obtain ⟨hg, ha⟩ := h
        cases g with
        | var i => simp only [Expr.shift] at hg; split at hg <;> cases hg
        | prim p =>
            simp only [Expr.shift, Expr.prim.injEq] at hg
            subst hg
            cases a with
            | var i => simp only [Expr.shift] at ha; split at ha <;> cases ha
            | pair a₁ a₂ =>
                simp only [Expr.shift, Expr.pair.injEq] at ha
                obtain ⟨ha₁, -⟩ := ha
                cases a₁ with
                | var i => simp only [Expr.shift] at ha₁; split at ha₁ <;> cases ha₁
                | prim q =>
                    simp only [Expr.shift, Expr.prim.injEq] at ha₁
                    subst ha₁
                    exact ⟨a₂, rfl⟩
                | _ => simp [Expr.shift] at ha₁
            | _ => simp [Expr.shift] at ha
        | _ => simp [Expr.shift] at hg
    | _ => simp [Expr.shift] at h
  · rintro ⟨x, rfl⟩
    exact ⟨x.shift d c, by simp [Expr.shift]⟩

/-- **A shift keeps a context's handler names.** -/
theorem hasHnd_shift (n : UInt32) (d : ℕ) :
    ∀ (K : Kont) (c : ℕ), (K.shift d c).HasHnd n = K.HasHnd n := by
  intro K
  induction K with
  | hole => intro c; rfl
  | appR f K ih =>
      intro c
      simp only [Kont.shift, Kont.HasHnd, ih]
      congr 1
      split
      next m x hx =>
        obtain ⟨x', rfl⟩ := (hndFrame_shift_iff f d c m).1 ⟨x, hx⟩
        rfl
      next hne =>
        split
        next m' x' =>
          obtain ⟨x, hx⟩ := (hndFrame_shift_iff _ d c m').2 ⟨x', rfl⟩
          exact absurd hx (hne m' x)
        next => rfl
  | pairL K e ih | pairR v K ih | letpair K e ih | case K e₁ e₂ ih | appL K v ih | seq K e ih
  | inj₁ K ih | inj₂ K ih => intro c; simp only [Kont.shift, Kont.HasHnd, ih]

/-! ### Data names no handler -/

/-- A data value names no handler. -/
theorem hndNZ_of_dataVal : ∀ {A : VTy} {v : Val}, DataVal A v → v.1.HndNamesNZ
  | _, _, .unit => by simp [Val.unit, Expr.HndNamesNZ]
  | _, _, .int h => by
      obtain ⟨c, hc⟩ := h.val
      rw [hc]
      simp [Expr.HndNamesNZ]
  | _, _, .pair h₁ h₂ => by
      simp only [Val.pair, Expr.HndNamesNZ]
      exact ⟨hndNZ_of_dataVal h₁, hndNZ_of_dataVal h₂⟩
  | _, _, .inj₁ h => by
      simp only [Val.inj₁, Expr.HndNamesNZ]
      exact hndNZ_of_dataVal h
  | _, _, .inj₂ h => by
      simp only [Val.inj₂, Expr.HndNamesNZ]
      exact hndNZ_of_dataVal h
  | _, _, .roll h => hndNZ_of_dataVal h

/-! ### Runs under a platform -/

/-- **A step under a platform keeps every handler named nonzero**, at a configuration where the
platform is asked at data arguments only: a machine step creates no handler named `0`
(`hndNZ_step1`), and the platform's answer to a data argument is data. -/
theorem hndNZ_pstep {P : Platform} (hP : P.Respects) {c c' : Conf P} (hPD : PlatData P c)
    (h : PStep (ℍ := ℍ) P c c') (he : c.e.HndNamesNZ) (hμ : HeapNZ c.μ) :
    c'.e.HndNamesNZ ∧ HeapNZ c'.μ := by
  cases h with
  | mach hs => exact hndNZ_step1 hs he hμ
  | @plat μ s s' K n i v w o hK hf hco =>
      have hdA : DataVal o.A v := hPD K n i v o rfl hK hf
      have hm := Row.find_mem hf
      have hdB : DataVal o.B w :=
        hP.typed s s' o v w hm.1 hdA (by rw [hm.2.1, hm.2.2]; exact hco)
      exact ⟨plug_hndNZ K (plug_hndNZ_inv K (notNameLike_perform _) he).1 (hndNZ_of_dataVal hdB), hμ⟩

/-- **Every run from a start in Core's relation keeps every handler named nonzero**, from a
program that names none: each configuration it reaches asks the platform at data arguments
(`platData_of_start`). -/
theorem hndNZ_of_start {P : Platform} (hP : P.Respects) {S : Row} (hag : PlatAgree P S)
    {Q : List SRec → Val → WProp} {e : Expr}
    (h₀ : ewpTS (ℍ := ℍ) [] e (opTable (Row.tab S LSub.empty)) Q PMap.empty) (he : e.HndNamesNZ) :
    ∀ c, PSteps (ℍ := ℍ) P (init P e) c → c.e.HndNamesNZ ∧ HeapNZ c.μ := by
  intro c h
  induction h with
  | refl => exact ⟨he, heapNZ_empty⟩
  | @tail b c hb hbc ih =>
      exact hndNZ_pstep hP (Inst.platData_of_start hP hag h₀ b hb).1 hbc ih.1 ih.2

/-! ### The drive -/

/-- A step of the drive under a platform, at a configuration where the platform is asked at data
arguments only, is a step under the restricted platform. -/
theorem rstep_restrict {P : Platform} {rc rc' : Conf P × Phase} (hPD : PlatData P rc.1)
    (h : RStep (ℍ := ℍ) P rc rc') :
    RStep (ℍ := ℍ) P.restrict (rc.1.toRestrict, rc.2) (rc'.1.toRestrict, rc'.2) := by
  cases h with
  | run hp => exact .run (pstep_restrict hPD hp)
  | start => exact .start
  | again => exact .again

/-- **Every configuration the drive reaches keeps the platform's protocol**, and the drive reaches
it under the restricted platform too: the drive's invariant holds under the restricted platform
(`driveSafe_of_reach`), so the run continues there to an end or a stop (`driveSafe_cont`), where
the protocol holds (`platData_of_cont`). -/
theorem driveData_of_reach {P : Platform} (hP : P.Respects) {S S₀ : Row} {A : VTy}
    (hsub : ∀ n i o, Row.find P.ops n i = some o → Row.find S n i = some o) (hle : RowLe S₀ S)
    (hC : (CTy.loopEffBody S₀ A .unit).NuOk) {M : Expr}
    (h : cC (ℍ := ℍ) (CTy.effOf S (.sum A (.thunk (CTy.loopEff S₀ A .unit)))) [] LSub.empty M
      PMap.empty)
    {rc : Conf P × Phase} (hr : Relation.ReflTransGen (RStep (ℍ := ℍ) P) (init P M, .drive) rc) :
    PlatData P rc.1 ∧
      Relation.ReflTransGen (RStep (ℍ := ℍ) P.restrict) (init P.restrict M, .drive)
        (rc.1.toRestrict, rc.2) := by
  have hP' := restrict_respects hP
  have hsub' : ∀ n i o, Row.find P.restrict.ops n i = some o → Row.find S n i = some o := hsub
  have hdata : ∀ {rc : Conf P × Phase},
      Relation.ReflTransGen (RStep (ℍ := ℍ) P.restrict) (init P.restrict M, .drive)
        (rc.1.toRestrict, rc.2) → PlatData P rc.1 := by
    intro rc hr'
    have hds := driveSafe_of_reach hP' hsub' hle hC h hr'
    exact Inst.platData_of_cont (driveSafe_cont hP' hsub' hds)
  induction hr with
  | refl =>
      have hr' : Relation.ReflTransGen (RStep (ℍ := ℍ) P.restrict) (init P.restrict M, .drive)
          ((init P M).toRestrict, Phase.drive) := .refl
      exact ⟨hdata hr', hr'⟩
  | @tail b c _ hbc ih =>
      have hr' := ih.2.tail (rstep_restrict ih.1 hbc)
      exact ⟨hdata hr', hr'⟩

/-- `next l` names a handler only where `l` does. -/
theorem hndNZ_nextE {l : Val} (hl : l.1.HndNamesNZ) : (nextE l).HndNamesNZ := by
  unfold nextE
  rw [hndNZ_app]
  refine .inr ⟨fun h => ?_, hl, by simp [Val.inj₁, Val.unit, Expr.HndNamesNZ]⟩
  rw [show Expr.val l = l.1 from rfl] at h
  rw [h] at hl
  exact hndNZ_prim_hnd hl

/-- **Every configuration a drive reaches from a start in Core's relation names no handler `0`**,
from a step that names none. -/
theorem hndNZ_drive_of_reach {P : Platform} (hP : P.Respects) {S S₀ : Row} {A : VTy}
    (hsub : ∀ n i o, Row.find P.ops n i = some o → Row.find S n i = some o) (hle : RowLe S₀ S)
    (hC : (CTy.loopEffBody S₀ A .unit).NuOk) {M : Expr}
    (h : cC (ℍ := ℍ) (CTy.effOf S (.sum A (.thunk (CTy.loopEff S₀ A .unit)))) [] LSub.empty M
      PMap.empty) (hM : M.HndNamesNZ)
    {rc : Conf P × Phase} (hr : Relation.ReflTransGen (RStep (ℍ := ℍ) P) (init P M, .drive) rc) :
    rc.1.e.HndNamesNZ ∧ HeapNZ rc.1.μ := by
  induction hr with
  | refl => exact ⟨hM, heapNZ_empty⟩
  | @tail b c hb hbc ih =>
      have hPD := (driveData_of_reach hP hsub hle hC h hb).1
      rcases rstep_cases hbc with ⟨hp, -⟩ | ⟨-, l, he, rfl⟩ | ⟨-, l, he, rfl⟩
      · exact hndNZ_pstep hP hPD hp ih.1 ih.2
      · refine ⟨hndNZ_nextE ?_, ih.2⟩
        have := ih.1
        rw [he] at this
        exact this
      · refine ⟨hndNZ_nextE ?_, ih.2⟩
        have := ih.1
        rw [he] at this
        exact this

end Targets

namespace Targets.Inst
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont performE raiseE opPayload hndE ccatchE kappa cancelVal)
open BoCa.Lifetime (LSub LifeCtx)
open Targets (RowForm EffCtx orowRF orowAlg ORow RowAt RowCtx Platform PSteps HeapNZ okE okE_sound
  okE_of_derives)

/-! ### At a typing system whose closed programs are Core's -/

section Reach
variable {Ξ : EffCtx} {D : RowCtx → LifeCtx → Ctx OVTy → Expr → OJdg → Prop}

local notation "𝕊" => ourInst (ℍ := ℍ) orowRF Ξ (OurTyping.ofDer D)

variable {R : (ourInst (ℍ := ℍ) orowRF Ξ (OurTyping.ofDer D)).Runner}

/-- A term Core's kernel types names no handler `0` (I3.c). -/
theorem hndNZ_of_derives {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg}
    (h : CDerives Δ Γ e j) : e.HndNamesNZ :=
  (okE_sound e (okE_of_derives h)).2.2

/-- **A typed closed program names no handler `0`**: its derivation, or its driven step's, is
Core's. -/
theorem hndNZ_of_der (hJ : CoreClosed (OurTyping.ofDer D)) {e : Expr} {C : OCTy}
    (h : (𝕊).der [] e C) : e.HndNamesNZ := by
  obtain ⟨-, hd⟩ := h
  rcases hd with ⟨Θ, hΘ, hd⟩ | ⟨-, M, rfl, -, Θ, hΘ, hd⟩
  · exact hndNZ_of_derives (hJ Θ e C hΘ hd)
  · have hM := hndNZ_of_derives (hJ Θ M C hΘ hd)
    unfold driveE
    rw [Targets.hndNZ_app]
    exact .inr ⟨by simp [driveMark], by simp [driveMark, Expr.HndNamesNZ], hM⟩

/-- **No run of a typed program creates a handler named `0`**, under every runner that keeps its
protocol: every configuration it reaches names none, and neither does its memory unless the
configuration is the driven program's answer.  A plain program's run is its run under the runner's
platform (`plain_reach`), a driven program's the drive's (`drive_reach`); along both the platform
is asked at data arguments only, and answers with data. -/
theorem hndNZ_reach (hJ : CoreClosed (OurTyping.ofDer D)) (hR : R.Respects) {P : Expr}
    {C : OCTy} (hP : (𝕊).der [] P C) {x : (𝕊).RConf R} (hx : (𝕊).RReach R ((𝕊).rinit R P) x) :
    x.1.2.HndNamesNZ ∧ (HeapNZ x.1.1 ∨ IsVal x.1.2) := by
  have hPnz := hndNZ_of_der hJ hP
  obtain ⟨S, A₀, -, hS, hcases⟩ := der_cases hJ hP
  have hcl := closed_of_der hJ hP
  have hPl := platformOf_respects hR hS
  rcases hcases with hcC | ⟨M, S₀, A₁, rfl, hle, hnu, rfl, hcC⟩
  · obtain ⟨-, -, hps⟩ := plain_reach hR hS hcC hcl hx
    obtain ⟨h₁, h₂⟩ := Targets.hndNZ_of_start hPl platAgree_platformOf
      ((cC_effOf S _ [] LSub.empty P PMap.empty).mp hcC) hPnz _ hps
    exact ⟨h₁, .inl h₂⟩
  · have hM : closedAt 0 M = true := by simpa [driveE, driveMark, closedAt] using hcl
    have hMnz : M.HndNamesNZ := by
      unfold driveE at hPnz
      rw [Targets.hndNZ_app] at hPnz
      rcases hPnz with ⟨h, -⟩ | ⟨-, -, h⟩
      · simp [driveMark] at h
      · exact h
    rcases drive_reach hR hS hle hnu hcC hM hx with ⟨t, he, -, -, hr⟩ | ⟨a, μ₀, s₀, he, -, hr⟩
    · obtain ⟨h₁, h₂⟩ := Targets.hndNZ_drive_of_reach hPl platformOf_sub hle hnu hcC hMnz hr
      refine ⟨?_, .inl h₂⟩
      rw [he]
      unfold driveE
      rw [Targets.hndNZ_app]
      exact .inr ⟨by simp [driveMark], by simp [driveMark, Expr.HndNamesNZ], h₁⟩
    · obtain ⟨h₁, -⟩ := Targets.hndNZ_drive_of_reach hPl platformOf_sub hle hnu hcC hMnz hr
      refine ⟨?_, .inr ?_⟩
      · rw [he]
        simpa [Val.inj₁, Expr.HndNamesNZ] using h₁
      · rw [he]; exact a.2

/-- **A cancelled continuation's context has no handler of `0`**, at every typing system whose
closed programs are Core's: the configuration that cancels `κ = kappa H K` names no handler `0`,
since no run of a typed program creates one (`hndNZ_reach`), and `κ`'s resume branch
`λy. hnd H K[y]` holds `K` shifted, which keeps its handler names (`hasHnd_shift`); so `K` names
none.  The handler is a value: otherwise the cancel is stuck at `() (inj₂ ())`, against
`LiveOK`. -/
theorem cancelsNZ_of_coreClosed (hJ : CoreClosed (OurTyping.ofDer D)) :
    CancelsNZ (ℍ := ℍ) orowRF Ξ (OurTyping.ofDer D) := by
  intro R hR e ε A _ he c₀ K₀ l H K hreach h₀
  have hlive : (𝕊).Live c₀.1 := ⟨e, _, R, c₀.2, hR, he, hreach⟩
  have hgo := (liveOK_of_coreClosed hJ c₀.1 hlive).2
  obtain ⟨hnz, -⟩ := hndNZ_reach hJ hR he hreach
  obtain ⟨⟨μ₀, e₀⟩, s₀⟩ := c₀
  change e₀ = Kont.plug K₀ (cancelE (captureE (orowRF.name Ξ l) (qsOf Ξ (orowRF.name Ξ l)) H.1.1
    (H.2.map Subtype.val) K)) at h₀
  change e₀.HndNamesNZ at hnz
  -- the handler is a value: otherwise the cancel's start is stuck at `() (inj₂ ())`
  have hv : IsVal (hndValE (orowRF.name Ξ l) (qsOf Ξ (orowRF.name Ξ l)) H.1.1
      (H.2.map Subtype.val)) := by
    by_contra hnv
    rw [captureE_of_not_val K hnv] at h₀
    have h₀' : e₀ = Kont.plug K₀ (.app .unit (Val.inj₂ Val.unit).1) := h₀
    rw [h₀'] at hgo
    exact not_goesOn_stuck (stuckAt_unit_app (Val.inj₂ Val.unit)) K₀ μ₀
      (plug_unit_app_ne_drive K₀ _) hgo
  rw [captureE_of_val K hv] at h₀
  -- `κ`'s resume branch holds `K` shifted, and names no handler `0`
  rw [h₀] at hnz
  have hc : (cancelE (kappa ⟨_, hv⟩ K)).HndNamesNZ :=
    (plug_hndNZ_inv K₀ ⟨fun _ _ h => by simp [cancelE] at h, fun _ h => by simp [cancelE] at h⟩
      hnz).2
  have hκ := (hndNZ_app_inv (by simp [kappa]) hc).1
  simp only [kappa, Expr.val, Val.lam, Expr.HndNamesNZ, true_and] at hκ
  have hr := (hndNZ_app_inv (f := .app (.prim .hnd) _) (by simp) hκ.1).2
  have h0 := hasHnd0_of_knz (K.shift 3 0) hr
  rwa [hasHnd_shift] at h0

end Reach

end Targets.Inst

namespace Targets.I
open Targets.Inst (ourInst J₁ J1DerAt coreClosed_J₁At)

/-- **At `J₁`, a cancelled continuation's context has no handler of `0`**, at every effect
context. -/
theorem cancelsNZ_J₁ {Ξ : EffCtx} : Inst.CancelsNZ (ℍ := ℍ) orowRF Ξ J₁ :=
  Inst.cancelsNZ_of_coreClosed (D := J1DerAt Ξ) (coreClosed_J₁At Ξ)

/-- **At today's kernel, a cancelled continuation's context has no handler of `0`**, at every
effect context. -/
theorem cancelsNZ_tier1Open {Ξ : EffCtx} : Inst.CancelsNZ (ℍ := ℍ) orowRF Ξ Inst.tier1Open :=
  Inst.cancelsNZ_of_coreClosed (D := Inst.tier1OpenDer) Inst.coreClosed_tier1Open

end Targets.I

end
