import Targets.Base.KeptCount
import Targets.I.CancelsNamed
import Targets.I.ContUseJ1

/-!
# The interaction — no typed run drops an error (decision D1)

The machine never silently drops a finaliser's error (decision D1 of 2026-10-08): a cancel keeps
the first error its region's finalisers raise, and at its canceller re-raises it as an ordinary
raise (SPEC §19).  Counted on a run, every error kept leaves it in one of the algebra's two ways:

    keeps = reraises + merges

`keeps` counts the `[cfin-raise]` steps at a cancel that kept nothing (each keeps a new error),
`reraises` the `[cancel-raise]` steps (each re-raises one at its canceller), and `merges` the
`[cfin-cancel]` steps at two kept errors (the later loses to the earlier, SPEC §19's first-wins).
`NoDroppedError` asks it on every complete run of a program typed at a data answer, the runs S6
reads.

**Proved at `J₁`, at every effect context, on the runs that capture no context holding a kept
error** (`I.noDroppedErrorNKC_J₁`).  The holders of kept errors (a cancel's raise keeping one, a
running finaliser's `cfin` frame keeping one) are counted (`kc`, `Targets/Base/KeptCount.lean`);
they sit on the configuration's evaluation spine (`OnPath`), and each step changes their number
only as the count says (`kc_step1`).  A typed program holds none (it writes no `cfin` and raises
only its labels' names), an answer holds none, and the runner answers at data, which holds none.
The run invariants the steps need are the run's: every raise of a label's name or a cancel's
(`raiseOK_of_start`), every handler named nonzero (`hndNZ_of_start`), and the runner asked at data
(`platData_of_start`).

**What is left** is the runs on which an `[op]` step captures a context that holds a kept error: a
running finaliser of a cancel that has kept an error performs an operation whose live handler
catches it outside the cancelled region.  The kept error then sits in the continuation the handler
gets, and whether it returns to the run depends on what the handler does with the continuation.
At an `unr` operation the handler may drop it, and the error goes with it: `NoDroppedError` fails
at a typed program (`Targets/Instance/DropWitness.lean`).  `[Core σ=[]]`
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont performE raiseE opPayload cancelVal)

/-- A data value holds no kept error. -/
theorem kc_of_dataVal : ∀ {A : VTy} {v : Val}, DataVal A v → kc v.1 = 0
  | _, _, .unit => rfl
  | _, _, .int h => by
      obtain ⟨c, hc⟩ := h.val
      rw [hc]; rfl
  | _, _, @DataVal.pair _ _ v₁ v₂ h₁ h₂ => by
      show kc v₁.1 + kc v₂.1 = 0
      rw [kc_of_dataVal h₁, kc_of_dataVal h₂]
  | _, _, @DataVal.inj₁ _ _ v h => (kc_of_dataVal h : kc v.1 = 0)
  | _, _, @DataVal.inj₂ _ _ v h => (kc_of_dataVal h : kc v.1 = 0)
  | _, _, .roll h => kc_of_dataVal h

/-- **A term that raises only the names `q` reaches, `0` not one of them, and holds no `cfin`,
holds no kept error.** -/
theorem kc_of_rcE {q : UInt32 → Bool} (hq : q 0 = false) (e : Expr) (h : rcE q e = true) :
    kc e = 0 := by
  fun_induction rcE q e with
  | case1 m r ih =>
      simp only [Bool.and_eq_true] at h
      have hm : m ≠ 0 := fun h0 => by rw [h0, hq] at h; exact Bool.false_ne_true h.1
      show holdAt (.prim .raise) (.pair (.prim (.lit (.i32 m))) r) + 0 + (0 + kc r) = 0
      simp only [holdAt, keptB_pairLit_ne hm, ih h.2]
      rfl
  | case2 p => rfl
  | case3 => rfl
  | case4 => rfl
  | case5 => rfl
  | case6 a b iha ihb =>
      simp only [Bool.and_eq_true] at h
      show kc a + kc b = 0
      rw [iha h.1, ihb h.2]
  | case7 a b iha ihb =>
      simp only [Bool.and_eq_true] at h
      show kc a + kc b = 0
      rw [iha h.1, ihb h.2]
  | case8 a b iha ihb =>
      simp only [Bool.and_eq_true] at h
      show kc a + kc b = 0
      rw [iha h.1, ihb h.2]
  | case9 a b hab iha ihb =>
      simp only [Bool.and_eq_true] at h
      have h₀ : holdAt a b = 0 := by
        cases a with
        | prim p =>
            cases p with
            | raise => simp [rcE] at h
            | cfin => simp [rcE] at h
            | _ => rfl
        | _ => rfl
      show holdAt a b + kc a + kc b = 0
      rw [h₀, iha h.1, ihb h.2]
  | case10 a iha => exact iha h
  | case11 a iha => exact iha h
  | case12 a iha => exact iha h
  | case13 a b c iha ihb ihc =>
      simp only [Bool.and_eq_true] at h
      show kc a + kc b + kc c = 0
      rw [iha h.1.1, ihb h.1.2, ihc h.2]

end Targets

namespace Targets.Inst
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont performE raiseE opPayload cancelVal)
open BoCa.Lifetime (LSub LifeCtx)
open Targets (RowForm EffCtx orowRF orowAlg ORow RowAt RowCtx Platform PStep PSteps Conf DataVal
  PlatStart platStart_init platStart_safe kc OnPath HeapKC KeepAt ReraiseAt
  MergeAt NoKeptCaptureAt labQ rcE rcE_of_derivesAt kc_of_rcE kc_of_dataVal)

/-! ### The counts, and the statement -/

section Counts
variable {RF : RowForm} {Ξ : EffCtx} {J : OurTyping RF}

local notation "𝕊" => ourInst (ℍ := ℍ) RF Ξ J

variable {R : (ourInst (ℍ := ℍ) RF Ξ J).Runner}

open Classical in
/-- The steps of the path `q` from `c₀` at `[cfin-raise]` keeping a new error. -/
noncomputable def keepsOf (c₀ : (𝕊).RConf R) (q : List ((𝕊).Event × (𝕊).RConf R)) : ℕ :=
  (List.range q.length).countP fun j => decide (KeepAt ((𝕊).cfgAt c₀ q j).1.2)

open Classical in
/-- The steps of the path `q` from `c₀` at `[cancel-raise]`, re-raising a kept error. -/
noncomputable def reraisesOf (c₀ : (𝕊).RConf R) (q : List ((𝕊).Event × (𝕊).RConf R)) : ℕ :=
  (List.range q.length).countP fun j => decide (ReraiseAt ((𝕊).cfgAt c₀ q j).1.2)

open Classical in
/-- The steps of the path `q` from `c₀` at `[cfin-cancel]` at two kept errors. -/
noncomputable def mergesOf (c₀ : (𝕊).RConf R) (q : List ((𝕊).Event × (𝕊).RConf R)) : ℕ :=
  (List.range q.length).countP fun j => decide (MergeAt ((𝕊).cfgAt c₀ q j).1.2)

open Classical in
theorem countP_cfgAt_cons (p : Expr → Prop) (c c' : (𝕊).RConf R) (ev : (𝕊).Event)
    (q : List ((𝕊).Event × (𝕊).RConf R)) :
    (List.range ((ev, c') :: q).length).countP (fun j => decide (p ((𝕊).cfgAt c ((ev, c') :: q) j).1.2)) =
      (if p c.1.2 then 1 else 0) +
        (List.range q.length).countP (fun j => decide (p ((𝕊).cfgAt c' q j).1.2)) := by
  rw [List.length_cons, List.range_succ_eq_map, List.countP_cons, List.countP_map]
  have h₀ : (𝕊).cfgAt c ((ev, c') :: q) 0 = c := rfl
  have hfun : ∀ j ∈ List.range q.length,
      ((fun j => decide (p ((𝕊).cfgAt c ((ev, c') :: q) j).1.2)) ∘ Nat.succ) j =
        decide (p ((𝕊).cfgAt c' q j).1.2) := by
    intro j hj
    simp only [Function.comp]
    rw [Targets.A.EffectSystem.cfgAt_cons_succ c c' ev q (Nat.le_of_lt (List.mem_range.1 hj))]
  rw [List.countP_congr (fun j hj => by rw [hfun j hj]), h₀]
  by_cases hp : p c.1.2 <;> simp [hp, Nat.add_comm]

theorem keepsOf_cons (c c' : (𝕊).RConf R) (ev : (𝕊).Event) (q : List ((𝕊).Event × (𝕊).RConf R)) :
    keepsOf c ((ev, c') :: q) = (open Classical in if KeepAt c.1.2 then 1 else 0) + keepsOf c' q :=
  countP_cfgAt_cons KeepAt c c' ev q

theorem reraisesOf_cons (c c' : (𝕊).RConf R) (ev : (𝕊).Event)
    (q : List ((𝕊).Event × (𝕊).RConf R)) :
    reraisesOf c ((ev, c') :: q) = (open Classical in if ReraiseAt c.1.2 then 1 else 0) +
      reraisesOf c' q :=
  countP_cfgAt_cons ReraiseAt c c' ev q

theorem mergesOf_cons (c c' : (𝕊).RConf R) (ev : (𝕊).Event) (q : List ((𝕊).Event × (𝕊).RConf R)) :
    mergesOf c ((ev, c') :: q) = (open Classical in if MergeAt c.1.2 then 1 else 0) +
      mergesOf c' q :=
  countP_cfgAt_cons MergeAt c c' ev q

end Counts

/-- **No typed run drops an error** (decision D1 of 2026-10-08): on every complete run of a program
typed at a data answer, under every runner that keeps its protocol, every error a cancel keeps is
re-raised at its canceller or loses to an earlier one (`keeps = reraises + merges`). -/
def NoDroppedError (RF : RowForm) (Ξ : EffCtx) (J : OurTyping RF) : Prop :=
  ∀ R : (ourInst (ℍ := ℍ) RF Ξ J).Runner, R.Respects → ∀ e ε A,
    (ourInst (ℍ := ℍ) RF Ξ J).Answers R ε →
    (ourInst (ℍ := ℍ) RF Ξ J).der [] e ((ourInst (ℍ := ℍ) RF Ξ J).F ε A) →
    (ourInst (ℍ := ℍ) RF Ξ J).DataTy A →
    ∀ q, (ourInst (ℍ := ℍ) RF Ξ J).CompleteFrom R ((ourInst (ℍ := ℍ) RF Ξ J).rinit R e) q →
      keepsOf ((ourInst (ℍ := ℍ) RF Ξ J).rinit R e) q =
        reraisesOf ((ourInst (ℍ := ℍ) RF Ξ J).rinit R e) q +
          mergesOf ((ourInst (ℍ := ℍ) RF Ξ J).rinit R e) q

/-- **`NoDroppedError` on the runs that capture no context holding a kept error**: at every
configuration of the run, an `[op]` step captures a context with no running finaliser's `cfin`
frame keeping an error. -/
def NoDroppedErrorNKC (RF : RowForm) (Ξ : EffCtx) (J : OurTyping RF) : Prop :=
  ∀ R : (ourInst (ℍ := ℍ) RF Ξ J).Runner, R.Respects → ∀ e ε A,
    (ourInst (ℍ := ℍ) RF Ξ J).Answers R ε →
    (ourInst (ℍ := ℍ) RF Ξ J).der [] e ((ourInst (ℍ := ℍ) RF Ξ J).F ε A) →
    (ourInst (ℍ := ℍ) RF Ξ J).DataTy A →
    ∀ q, (ourInst (ℍ := ℍ) RF Ξ J).CompleteFrom R ((ourInst (ℍ := ℍ) RF Ξ J).rinit R e) q →
      (∀ j, j ≤ q.length →
        NoKeptCaptureAt ((ourInst (ℍ := ℍ) RF Ξ J).cfgAt ((ourInst (ℍ := ℍ) RF Ξ J).rinit R e) q j).1.2) →
      keepsOf ((ourInst (ℍ := ℍ) RF Ξ J).rinit R e) q =
        reraisesOf ((ourInst (ℍ := ℍ) RF Ξ J).rinit R e) q +
          mergesOf ((ourInst (ℍ := ℍ) RF Ξ J).rinit R e) q

/-! ### At `J₁` -/

section J1
variable {Ξ : EffCtx}

local notation "𝕊" => ourInst (ℍ := ℍ) orowRF Ξ (OurTyping.ofDer (J1DerAt Ξ))

variable {R : (ourInst (ℍ := ℍ) orowRF Ξ (OurTyping.ofDer (J1DerAt Ξ))).Runner}

/-- A program typed at `J₁` holds no kept error. -/
theorem kc_of_der_J₁ {e : Expr} {C : OCTy} (h : (𝕊).der [] e C) : kc e = 0 := by
  have hq : labQ Ξ 0 = false := by
    cases h0 : labQ Ξ 0
    · rfl
    · exact absurd h0 (Targets.labQ_zero Ξ)
  obtain ⟨-, hd⟩ := h
  rcases hd with ⟨Θ, hΘ, hd⟩ | ⟨-, M, rfl, -, Θ, hΘ, hd⟩
  · exact kc_of_rcE hq e (rcE_of_derivesAt (coreClosedAt_J₁ Ξ hΘ hd))
  · have hM := kc_of_rcE hq M (rcE_of_derivesAt (coreClosedAt_J₁ Ξ hΘ hd))
    show Targets.holdAt _ M + kc _ + kc M = 0
    rw [hM]
    rfl

open Classical in
/-- **A step of a typed program's run at a data answer changes the kept errors only as the count
says**, at a configuration whose holders are on its spine and whose `[op]` captures no context
holding one.  The step is the platform's (`plain_rstep`): a machine step (`kc_step1`, with the run
invariants `raiseOK_of_start`, `hndNZ_of_start`), or an answer of the runner, which is data
(`platData_of_start`) and holds none. -/
theorem kc_rstep {P : Expr} {ε : ORow} {A : OVTy} (hR : R.Respects) (hA : (𝕊).DataTy A)
    (hP : (𝕊).der [] P ((𝕊).F ε A)) {c c' : (𝕊).RConf R} {ev : (𝕊).Event}
    (hc : (𝕊).RReach R ((𝕊).rinit R P) c) (hs : (𝕊).RStep R c ev c') (hon : OnPath c.1.2)
    (hμ : HeapKC c.1.1) (hcap : NoKeptCaptureAt c.1.2) :
    OnPath c'.1.2 ∧ HeapKC c'.1.1 ∧
      kc c'.1.2 + (if ReraiseAt c.1.2 then 1 else 0) + (if MergeAt c.1.2 then 1 else 0) =
        kc c.1.2 + (if KeepAt c.1.2 then 1 else 0) := by
  have hJ := coreClosed_J₁At Ξ
  have hP0 : ¬ (fun m => labQ Ξ m = true) 0 := Targets.labQ_zero Ξ
  obtain ⟨hS, -, hcl, hcC⟩ := plain_of_dataTy hJ hA hP
  have hPl := platformOf_respects hR hS
  have hew := (cC_effOf _ _ [] LSub.empty P PMap.empty).mp hcC
  have h₀ := platStart_init (P := platformOf R (orowRF.den Ξ ε (fun _ => []))) hew
  obtain ⟨⟨μ, e⟩, s⟩ := c
  obtain ⟨⟨μ', e'⟩, s'⟩ := c'
  obtain ⟨hcc, hμc, hps⟩ := plain_reach hR hS hcC hcl hc
  obtain ⟨hst, -, -⟩ := plain_rstep (S := orowRF.den Ξ ε (fun _ => [])) hcc hμc
    (platStart_safe hPl platAgree_platformOf h₀ hps) hs
  obtain ⟨hok, hμr⟩ := Targets.raiseOK_of_start hP0 hPl platAgree_platformOf hew
    (raiseOK_of_der_J₁ hP) _ hps
  obtain ⟨hnz, -⟩ := Targets.hndNZ_of_start hPl platAgree_platformOf hew (hndNZ_of_der hJ hP) _ hps
  have hPD := (platData_of_start hPl platAgree_platformOf hew _ hps).1
  change OnPath e at hon
  change HeapKC μ at hμ
  change NoKeptCaptureAt e at hcap
  change Expr.RaiseOK _ e at hok
  change HeapRaiseOK _ μ at hμr
  change e.HndNamesNZ at hnz
  show OnPath e' ∧ HeapKC μ' ∧ kc e' + _ + _ = kc e + _
  cases hst with
  | mach h₁ => exact Targets.kc_step1 hP0 h₁ hok hμr hnz hon hμ hcap
  | @plat μ₀ s₀ s₁ K n i v w o hK hf hco =>
      have hdA : DataVal o.A v := hPD K n i v o rfl hK hf
      have hm := Row.find_mem hf
      have hdB : DataVal o.B w :=
        hPl.typed _ _ o v w hm.1 hdA (by rw [hm.2.1, hm.2.2]; exact hco)
      have hw := kc_of_dataVal hdB
      have hwr : (Expr.val w).RaiseOK (fun m => labQ Ξ m = true) := raiseOK_of_dataVal hdB
      obtain ⟨hKr, hpr⟩ := plug_raiseOK_inv K (plain_perform _) hok
      obtain ⟨hKo, hp⟩ := Targets.onPath_plug_inv K (plain_perform _) (opE_not_isVal false _) hon
      have hpv := (Targets.onPath_app_val (opPayload n i v).2 hp).1
      have hof : OpFree false n K := by simpa [OpFree] using hK
      have nk : ¬ KeepAt (K.plug (performE (.val (opPayload n i v)))) := by
        rintro ⟨K', r, he, hr⟩
        obtain ⟨r', hr'⟩ := Targets.head_of_keepRedex (ℍ := ℍ) hr μ₀
        exact nested_op (r := false) (payloadName_opPayload n i v) hof hr' (by rw [← he]; rfl)
      have nr : ¬ ReraiseAt (K.plug (performE (.val (opPayload n i v)))) := by
        rintro ⟨K', r, he, hr⟩
        obtain ⟨r', hr'⟩ := Targets.head_of_reraiseRedex (ℍ := ℍ) hr μ₀
        exact nested_op (r := false) (payloadName_opPayload n i v) hof hr' (by rw [← he]; rfl)
      have nm : ¬ MergeAt (K.plug (performE (.val (opPayload n i v)))) := by
        rintro ⟨K', r, he, hr⟩
        obtain ⟨r', hr'⟩ := Targets.head_of_mergeRedex (ℍ := ℍ) hr μ₀
        exact nested_op (r := false) (payloadName_opPayload n i v) hof hr' (by rw [← he]; rfl)
      refine ⟨Targets.onPath_plug hP0 K hKr hwr hKo (Targets.onPath_of_kc hw), hμ, ?_⟩
      rw [if_neg nk, if_neg nr, if_neg nm, Targets.kc_plug hP0 K hKr hwr,
        Targets.kc_plug hP0 K hKr hpr, Targets.kc_performE, hpv, hw]

open Classical in
/-- **The count along a run**: from a configuration a typed program's run reaches, whose holders
are on its spine and whose stored values hold none, along a path whose `[op]` steps capture no
context holding a kept error, the holders at the end and the errors re-raised or superseded on the
way are the holders at the start and the errors kept on the way; the end's holders are on its
spine. -/
theorem kc_path {P : Expr} {ε : ORow} {A : OVTy} (hR : R.Respects) (hA : (𝕊).DataTy A)
    (hP : (𝕊).der [] P ((𝕊).F ε A)) :
    ∀ (q : List ((𝕊).Event × (𝕊).RConf R)) (c : (𝕊).RConf R),
      (𝕊).RReach R ((𝕊).rinit R P) c → (𝕊).RPath R c q → OnPath c.1.2 → HeapKC c.1.1 →
      (∀ j, j ≤ q.length → NoKeptCaptureAt ((𝕊).cfgAt c q j).1.2) →
      OnPath ((𝕊).lastC c q).1.2 ∧
        kc ((𝕊).lastC c q).1.2 + reraisesOf c q + mergesOf c q = kc c.1.2 + keepsOf c q
  | [], c, _, _, hon, _, _ => by
      refine ⟨hon, ?_⟩
      simp [keepsOf, reraisesOf, mergesOf, Targets.A.EffectSystem.lastC_nil]
  | (ev, c') :: q, c, hc, hq, hon, hμ, hcap => by
      cases hq with
      | cons hs hq' =>
          have hcap₀ : NoKeptCaptureAt c.1.2 := hcap 0 (Nat.zero_le _)
          obtain ⟨hon', hμ', hcount⟩ := kc_rstep hR hA hP hc hs hon hμ hcap₀
          have hcap' : ∀ j, j ≤ q.length → NoKeptCaptureAt ((𝕊).cfgAt c' q j).1.2 := by
            intro j hj
            have := hcap (j + 1) (by simp; omega)
            rwa [Targets.A.EffectSystem.cfgAt_cons_succ c c' ev q hj] at this
          obtain ⟨ihon, ih⟩ := kc_path hR hA hP q c' (hc.tail ⟨ev, hs⟩) hq' hon' hμ' hcap'
          rw [Targets.A.EffectSystem.lastC_cons, keepsOf_cons, reraisesOf_cons, mergesOf_cons]
          exact ⟨ihon, by omega⟩

/-- **No typed run drops an error at `J₁`, on the runs that capture no context holding a kept
error**, at every effect context: every error kept on such a complete run of a program typed at a
data answer is re-raised at its canceller or loses to an earlier one. -/
theorem noDroppedErrorNKC_J₁At :
    NoDroppedErrorNKC (ℍ := ℍ) orowRF Ξ (OurTyping.ofDer (J1DerAt Ξ)) := by
  intro R hR e ε A _ he hA q hq hcap
  obtain ⟨hon, h⟩ := kc_path hR hA he q _ .refl hq.1 (Targets.onPath_of_kc (kc_of_der_J₁ he))
    Targets.heapKC_empty hcap
  have h₀ : kc ((𝕊).rinit R e).1.2 = 0 := kc_of_der_J₁ he
  have hlast : kc ((𝕊).lastC ((𝕊).rinit R e) q).1.2 = 0 := by
    obtain ⟨⟨v, hv⟩, -⟩ := hq.2
    have hJ := coreClosed_J₁At Ξ
    obtain ⟨hS, -, hcl, hcC⟩ := plain_of_dataTy hJ hA he
    obtain ⟨hcc, -, -⟩ := plain_reach hR hS hcC hcl
      (Targets.A.EffectSystem.rreach_cfgAt hq.1 q.length le_rfl)
    have hl : ((𝕊).lastC ((𝕊).rinit R e) q).1.2 = v.1 := hv
    have hcc' : closedAt 0 ((𝕊).lastC ((𝕊).rinit R e) q).1.2 = true := hcc
    rw [hl] at hcc' hon ⊢
    exact Targets.kc_of_onPath_val (isVal_of_closed_oval v.2 hcc') hon
  omega

end J1

end Targets.Inst

namespace Targets.I
open Targets.Inst (ourInst J₁ J1DerAt)

/-- **No typed run drops an error at `J₁`, on the runs that capture no context holding a kept
error**, at every effect context: every error kept on such a complete run of a program typed at a
data answer is re-raised at its canceller or loses to an earlier one. -/
theorem noDroppedErrorNKC_J₁ {Ξ : EffCtx} : Inst.NoDroppedErrorNKC (ℍ := ℍ) orowRF Ξ J₁ :=
  Inst.noDroppedErrorNKC_J₁At

end Targets.I

end
