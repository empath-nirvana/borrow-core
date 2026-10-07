import Targets.I.Restricted.InstanceProps
import Targets.B.PlatSafe
import Targets.Instance.Platform
import Targets.Instance.J1Checks
import Targets.Base.Closed

/-!
# The interaction — S2, S3 and `LiveOK` at today's kernel (decision D1)

With rows tied to the effect context (decision D1), a typed program's row finds only labels'
operations, at the signatures the effect context declares, which are the types a runner answers
at.  A program typed by today's kernel is closed (`closed_of_der`, from `closedAt_of_derives`) and
in Core's relation at its row read with its row variables empty (`der_cases`, FL
`fl_core_tier1NU`); a run under a runner is a run under the platform the runner gives
(`platformOf`, `Targets/Instance/Platform.lean`).  B's runs give A's:

* **the runs agree step for step**, from a typed program: at a closed configuration whose run under
  the platform continues to an end or a stop of the row (`platSafe_of_ewp`, `driveSafe_cont`), the
  runner's answer is the platform's (`pstep_of_io`), and a step under the runner is the same step
  under the platform (`plain_rstep`) or, under the driver, the drive's step (`drive_rstep`).  So
  what a run under the runner reaches is closed and reached under the platform (`plain_reach`,
  `drive_reach`);
* **LiveOK** (`liveOK_tier1Open`): every such configuration is closed and goes on
  (`goesOn_of_plat`, `goesOn_of_drive`);
* **S3** (`effSafe_ourInst_tier1Open`): a machine run is a run under the runner that answers
  nothing, whose platform answers nothing; a configuration is an answer, steps, or is stopped at an
  operation of its row, and a stop of a row tied to the effect context is a stop in A's sense
  (`stopsIn_of_unanswered`);
* **S2** (`safety_ourInst_tier1Open`): under a runner that answers the row, the platform answers
  the row (`rowLe_platformOf`), and B2 (`adequateRetAt_core`, `safeDriveFrom_of_rel`) gives
  safety, termination at a data answer, and the data answer.

Each holds at every effect context.  `[Core σ=[]]`
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets.Inst
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont performE raiseE opPayload hndE ubindE ccatchE cfinE)
open BoCa.Lifetime (LSub LifeCtx)
open Targets (RowForm EffCtx orowRF orowAlg ORow RowAt RowEnv Platform PStep PSteps Conf DataVal
  CDerivesNU tier1NU fl_core_tier1NU comp_of_FL PlatEnd UnansweredAt PlatSafe platSafe_of_ewp
  platSafe_init psteps_from_val no_pstep_of_val pstep_cases DriveSafe driveSafe_init driveSafe_step
  driveSafe_cont QStep RStep Phase rstep_cases HeapClosed closed_step1 closedAt_plug_iff
  heapClosed_empty step1_plug_var closedAt_of_derives PlatAgree platAgree_of_le PlatStart
  platStart_init platStart_safe driveSafe_of_reach inl_or_inr_of_qStep init nextE opPlug_no_step
  orowRF_den platStart_cont adequateRetAt_core safeDriveFrom_of_rel)

/-! ### Small facts -/

/-- No head step applies a literal. -/
theorem no_head_lit_app {μ μ' : Heap} {c : IntLit} {t a' : Expr} :
    ¬ Head (ℍ := ℍ) μ (.app (.prim (.lit c)) t) μ' a' := by
  intro h
  generalize hE : Expr.app (.prim (.lit c)) t = E at h
  cases h <;> simp_all [hndE, ubindE, ccatchE, cfinE]

/-- A driver's configuration is no plugged operation. -/
theorem drive_ne_opPlug (K : Kont) (r : Bool) (p : Val) (v : Val) :
    K.plug (opE r p) ≠ driveE (.val v) := by
  intro h
  have := plug_eq_drive h (opE_not_isVal r p)
  subst this
  cases r <;> simp [Kont.plug, opE, driveE, driveMark, performE, raiseE] at h

/-- A context that stops no raise of `n` has no handler of `n`. -/
theorem hasHnd_of_catches {n : UInt32} : ∀ (K : Kont), K.Catches n = false → K.HasHnd n = false
  | .hole, _ => rfl
  | .appR f K, h => by
      simp only [Kont.Catches, Bool.or_eq_false_iff] at h
      simp only [Kont.HasHnd, Bool.or_eq_false_iff]
      refine ⟨?_, hasHnd_of_catches K h.2⟩
      have h1 := h.1
      split at h1 <;> simp_all
  | .pairL K _, h | .pairR _ K, h | .letpair K _, h | .case K _ _, h | .appL K _, h | .seq K _, h
  | .inj₁ K, h | .inj₂ K, h => hasHnd_of_catches K h

/-- A context that stops no raise of `n` has no finaliser frame. -/
theorem noUnwind_of_catches {n : UInt32} : ∀ (K : Kont), K.Catches n = false → K.NoUnwind
  | .hole, _ => trivial
  | .appR f K, h => by
      simp only [Kont.Catches, Bool.or_eq_false_iff] at h
      refine ⟨fun x hx => ?_, fun s hs => ?_, noUnwind_of_catches K h.2⟩
      · subst hx; simp at h
      · subst hs; simp at h
  | .pairL K _, h | .pairR _ K, h | .letpair K _, h | .case K _ _, h | .appL K _, h | .seq K _, h
  | .inj₁ K, h | .inj₂ K, h => noUnwind_of_catches K h

/-- A data type of A's has no row: it is the open type of its instance. -/
theorem ofV_den_of_dataTy {RF : RowForm} {J : OurTyping RF} :
    ∀ {A : OVTy}, (ourInst (ℍ := ℍ) RF Ξ J).DataTy A → ∀ η : RowEnv, OVTy.ofV (A.den η) = A
  | _, .unit, _ => rfl
  | _, .zero, _ => rfl
  | _, .tensor hA hB, η => by
      show OVTy.tensor (OVTy.ofV (OVTy.den η _)) (OVTy.ofV (OVTy.den η _)) = _
      rw [ofV_den_of_dataTy hA η, ofV_den_of_dataTy hB η]; rfl
  | _, .sum hA hB, η => by
      show OVTy.sum (OVTy.ofV (OVTy.den η _)) (OVTy.ofV (OVTy.den η _)) = _
      rw [ofV_den_of_dataTy hA η, ofV_den_of_dataTy hB η]; rfl

/-! ### A typed program, read at the empty instance -/

section Read
variable {Ξ : EffCtx}

local notation "𝕊" => ourInst (ℍ := ℍ) orowRF Ξ tier1Open

/-- **A program typed by today's kernel at our instance, read with its row variables empty**: its
type is a returner `F_S A₀` whose row is tied to the effect context, and it is a plain program in
Core's relation there, or a driven program whose step is: the type a loop sum
`F_S(A₁ ⊕ U(Loop_{S₀} A₁ 1))`, the loop's row below the step's and its body positive. -/
theorem der_cases {e : Expr} {C : OCTy} (h : (𝕊).der [] e C) :
    ∃ (S : Row) (A₀ : VTy), C.den (fun _ => []) = CTy.effOf S A₀ ∧ RowAt Ξ S ∧
      (cC (ℍ := ℍ) (CTy.effOf S A₀) [] LSub.empty e PMap.empty ∨
       ∃ (M : Expr) (S₀ : Row) (A₁ : VTy), e = driveE M ∧ RowLe S₀ S ∧
         (CTy.loopEffBody S₀ A₁ .unit).NuOk ∧ A₀ = .sum A₁ (.thunk (CTy.loopEff S₀ A₁ .unit)) ∧
         cC (ℍ := ℍ) (CTy.effOf S A₀) [] LSub.empty M PMap.empty) := by
  obtain ⟨hT, hd⟩ := h
  obtain ⟨S, A₀, hC, hS⟩ := hT _ (envAt_nil Ξ)
  refine ⟨S, A₀, hC, hS, ?_⟩
  rcases hd with ⟨Θ, hΘ, -, -, hd⟩ | ⟨-, M, rfl, hL, Θ, hΘ, -, -, hd⟩
  · have hd₀ := hd _ (models_anyCon_nil hΘ)
    change CDerivesNU LifeCtx.empty [] e (.comp (C.den (fun _ => []))) at hd₀
    rw [hC] at hd₀
    exact .inl (comp_of_FL fl_core_tier1NU (fun _ _ => hd₀))
  · have hd₀ := hd _ (models_anyCon_nil hΘ)
    change CDerivesNU LifeCtx.empty [] M (.comp (C.den (fun _ => []))) at hd₀
    rw [hC] at hd₀
    obtain ⟨S', S₀, A₁, hle, hnu, hC'⟩ := hL (fun _ => [])
    rw [hC] at hC'
    obtain ⟨rfl, rfl⟩ := effOf_inj hC'
    exact .inr ⟨M, S₀, A₁, rfl, hle, hnu, rfl, comp_of_FL fl_core_tier1NU (fun _ _ => hd₀)⟩

/-- **A typed closed program is closed.** -/
theorem closed_of_der {e : Expr} {C : OCTy} (h : (𝕊).der [] e C) : closedAt 0 e = true := by
  obtain ⟨-, hd⟩ := h
  rcases hd with ⟨Θ, hΘ, -, -, hd⟩ | ⟨-, M, rfl, -, Θ, hΘ, -, -, hd⟩
  · have hd₀ := hd _ (models_anyCon_nil hΘ)
    change CDerivesNU LifeCtx.empty [] e (.comp (C.den (fun _ => []))) at hd₀
    simpa using closedAt_of_derives hd₀.toCDerives
  · have hd₀ := hd _ (models_anyCon_nil hΘ)
    change CDerivesNU LifeCtx.empty [] M (.comp (C.den (fun _ => []))) at hd₀
    have := closedAt_of_derives hd₀.toCDerives
    simp only [List.length_nil] at this
    simp [driveE, driveMark, closedAt, this]

end Read

/-! ### The driver's frame -/

theorem driveE_plug (K : Kont) (x : Expr) : driveE (K.plug x) = (Kont.appR driveMark K).plug x := rfl

theorem opFree_drive {r : Bool} {n : UInt32} {K : Kont} :
    OpFree r n (Kont.appR driveMark K) ↔ OpFree r n K := by
  cases r <;> simp [OpFree, Kont.HasHnd, Kont.Catches, driveMark]

theorem noUnwind_drive (K : Kont) : (Kont.appR driveMark K).NoUnwind ↔ K.NoUnwind := by
  simp [Kont.NoUnwind, driveMark]

/-- A stop of the driven term is a stop of the driver's configuration. -/
theorem unanswered_drive {P : Platform} {S : Row} {t : Expr} (h : UnansweredAt P S t) :
    UnansweredAt P S (driveE t) := by
  obtain ⟨r, K, n, i, v, o, rfl, hK, hf, hab, hP⟩ := h
  exact ⟨r, .appR driveMark K, n, i, v, o, rfl, opFree_drive.2 hK, hf, hab, hP⟩

/-- A redex plugged into a driver's configuration sits inside the driven term. -/
theorem plug_eq_driveE {K : Kont} {x t : Expr} (h : K.plug x = driveE t) (hx : ¬ IsVal x)
    (hna : ∀ b, x ≠ .app driveMark b) : ∃ K', K = .appR driveMark K' ∧ t = K'.plug x := by
  cases K with
  | hole => exact absurd h (hna t)
  | appR f K =>
      simp only [Kont.plug, driveE, Expr.app.injEq] at h
      exact ⟨K, by rw [h.1], h.2.symm⟩
  | appL K v =>
      simp only [Kont.plug, driveE, driveMark, Expr.app.injEq] at h
      have h1 := h.1
      cases K <;> simp [Kont.plug] at h1
      subst h1; exact absurd .prim hx
  | _ => simp [Kont.plug, driveE] at h

/-- No head step reduces an application of the driver's mark. -/
theorem head_ne_drive {μ μ' : Heap} {a a' : Expr} (hh : Head (ℍ := ℍ) μ a μ' a') :
    ∀ b, a ≠ .app driveMark b := by
  rintro b rfl; exact no_head_lit_app hh

theorem perform_ne_drive (l : (orowAlg Ξ).Lab) (i : ℕ) (v : OVal) :
    ∀ b, (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).perform l i v ≠ .app driveMark b := by
  intro b h
  obtain ⟨x, hx⟩ := perform_app (ℍ := ℍ) (J := tier1Open) l i v
  rw [hx] at h
  injection h with h₁; injection h₁ with h₂; cases h₂

theorem not_isVal_perform (l : (orowAlg Ξ).Lab) (i : ℕ) (v : OVal) :
    ¬ IsVal ((ourInst (ℍ := ℍ) orowRF Ξ tier1Open).perform l i v) := by
  obtain ⟨x, hx⟩ := perform_app (ℍ := ℍ) (J := tier1Open) l i v
  rw [hx]; intro h; cases h

/-- A driver's configuration at a value takes no step under a platform. -/
theorem no_pstep_drive {P : Platform} {μ : Heap} {v : Val} {s : P.St} {c' : Conf P} :
    ¬ PStep (ℍ := ℍ) P ⟨μ, driveE (.val v), s⟩ c' := by
  intro h
  rcases pstep_cases h with ⟨hs, -⟩ | ⟨K, n, i, u, w, s', o, he, -⟩
  · exact no_step1_drive v hs
  · exact drive_ne_opPlug K false (opPayload n i u) v he.symm

/-- **A driver's configuration at a value goes on under no platform**: it takes no step, and it is
neither an end nor a stop. -/
theorem not_goes_drive {P : Platform} {Q : List SRec → Val → WProp} {S : Row} {μ : Heap} {v : Val}
    {s : P.St}
    (h : ∃ c', PSteps (ℍ := ℍ) P ⟨μ, driveE (.val v), s⟩ c' ∧ (PlatEnd P Q c' ∨ UnansweredAt P S c'.e)) :
    False := by
  obtain ⟨c', hc', hend⟩ := h
  rcases Relation.ReflTransGen.cases_head hc' with rfl | ⟨c₁, h₁, -⟩
  · rcases hend with ⟨w, -, -, -, -, -, he, -⟩ | ⟨r, K, n, i, u, o, he, -⟩
    · have : IsVal (driveE (.val v)) := by rw [show driveE (.val v) = (Expr.val w) from he]; exact w.2
      cases this
    · exact drive_ne_opPlug K r (opPayload n i u) v he.symm
  · exact no_pstep_drive h₁

/-- A steps of our machine, by its three rules. -/
theorem ostep_cases {RF : RowForm} {Ξ : EffCtx} {c c' : Heap × Expr}
    {ev : A.Ev (RF.alg Ξ).Lab OVal Expr} (h : OStep (ℍ := ℍ) RF Ξ c ev c') :
    (∃ (K : Kont) (a a' : Expr), c.2 = K.plug a ∧ Head (ℍ := ℍ) c.1 a c'.1 a' ∧ c'.2 = K.plug a') ∨
    (∃ l : Val, c.2 = driveE (.val (Val.inj₂ l)) ∧ c' = (c.1, driveE (nextE l))) ∨
    (∃ a : Val, c.2 = driveE (.val (Val.inj₁ a)) ∧ c' = (c.1, a.1)) := by
  cases h with
  | mach hh => exact .inl ⟨_, _, _, rfl, hh, rfl⟩
  | again => exact .inr (.inl ⟨_, rfl, rfl⟩)
  | fin => exact .inr (.inr ⟨_, rfl, rfl⟩)

/-- Replacing the plugged term of a closed configuration by a closed term keeps it closed. -/
theorem closedAt_plug_of {K : Kont} {x y : Expr} (hx : closedAt 0 (K.plug x) = true)
    (hy : closedAt 0 y = true) : closedAt 0 (K.plug y) = true := by
  rw [closedAt_plug_iff] at hx ⊢
  simp only [Bool.and_eq_true] at hx ⊢
  exact ⟨hx.1, hy⟩

/-! ### Runs under a runner and under its platform -/

section Sim
variable {Ξ : EffCtx}

local notation "𝕊" => ourInst (ℍ := ℍ) orowRF Ξ tier1Open

variable {R : (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).Runner} {S : Row}
  {Q : List SRec → Val → WProp}

/-- **The runner's answer, at a closed configuration that goes on under its platform, is the
platform's**: every run of the platform from there continues to an end or to a stop of `S` it does
not answer, the configuration takes no machine step and is no end, and the runner answers the
operation, so the platform does; its answer is the runner's (`coOf_some`). -/
theorem pstep_of_io {μ : Heap} {s s' : R.St} {K : Kont} {l : (orowAlg Ξ).Lab} {i : ℕ} {v w : OVal}
    (hcl : closedAt 0 (K.plug ((𝕊).perform l i v)) = true) (hK : K.HasHnd l.1 = false)
    (ha : R.answers l i) (hco : R.co s l i v = some (w, s'))
    (hgo : ∃ c' : Conf (platformOf R S),
      PSteps (ℍ := ℍ) (platformOf R S) ⟨μ, K.plug ((𝕊).perform l i v), s⟩ c' ∧
      (PlatEnd (platformOf R S) Q c' ∨ UnansweredAt (platformOf R S) S c'.e)) :
    PStep (ℍ := ℍ) (platformOf R S) ⟨μ, K.plug ((𝕊).perform l i v), s⟩ ⟨μ, K.plug w.1, s'⟩ ∧
      closedAt 0 w.1 = true := by
  rcases perform_cases (ℍ := ℍ) (J := tier1Open) l i v with ⟨hi, hp⟩ | ⟨-, hp⟩
  swap
  · rw [hp, not_closed_opJunk] at hcl; cases hcl
  have hv : IsVal v.1 := by
    rw [hp] at hcl
    have := closedAt_plug_inv K hcl
    simp only [performE, opArgE, closedAt, Expr.val, Val.prim, Val.i32, Bool.true_and] at this
    exact isVal_of_closed_oval v.2 this
  have hi' : (UInt32.ofNat i).toNat = i := UInt32.toNat_ofNat_of_lt' hi
  have hvv : OVal.ofVal ⟨v.1, hv⟩ = v := Subtype.ext rfl
  have he : K.plug ((𝕊).perform l i v) =
      K.plug (performE (.val (opPayload l.1 (UInt32.ofNat i) ⟨v.1, hv⟩))) := by
    rw [hp]; rfl
  rw [he] at hgo ⊢
  obtain ⟨c', hc', hend⟩ := hgo
  rcases Relation.ReflTransGen.cases_head hc' with rfl | ⟨c₁, h₁, -⟩
  · exfalso
    rcases hend with ⟨w₀, -, -, -, -, -, hw₀, -⟩ | ⟨r, K₁, n₁, i₁, v₁, o, he₁, -, hf, -, hP⟩
    · exact plug_perform_ne_val K _ w₀ hw₀
    · have h' : K.plug (opE false (opPayload l.1 (UInt32.ofNat i) ⟨v.1, hv⟩)) =
          K₁.plug (opE r (opPayload n₁ i₁ v₁)) := he₁
      obtain ⟨rfl, rfl, hpay⟩ := plug_opE_eq h'
      obtain ⟨rfl, rfl, rfl⟩ := opPayload_inj hpay
      have hfP := find_platformOf.2 ⟨hf, l, rfl, hi'.symm ▸ ha⟩
      rw [hP rfl] at hfP; cases hfP
  · rcases pstep_cases h₁ with ⟨hs, -⟩ | ⟨K₂, n₂, i₂, v₂, w₂, s₂, o₂, he₂, -, -, hco₂, rfl⟩
    · exact absurd hs (opPlug_no_step (r := false) (payloadName_opPayload _ _ _)
        (by simpa [OpFree] using hK))
    · obtain ⟨rfl, hpay⟩ := plug_perform_inj he₂
      obtain ⟨rfl, rfl, rfl⟩ := opPayload_inj hpay
      have hco₂' := hco₂
      rw [platformOf_co] at hco₂'
      obtain ⟨l₃, w₃, hl₃, hR₃, hw₃, hcw⟩ := coOf_some hco₂'
      obtain rfl : l₃ = l := Subtype.ext hl₃
      rw [hi', hvv, hco] at hR₃
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hR₃)
      refine ⟨?_, by rw [hw₃]; exact hcw⟩
      rw [hw₃]
      exact h₁

/-- **A step of a plain program under the runner is the same step under its platform**, at a
closed configuration that goes on under the platform: the driver's steps do not apply (a driver's
configuration at a value does not go on, `not_goes_drive`), a machine step is the platform's, and
an answer is the platform's (`pstep_of_io`).  The configuration stays closed. -/
theorem plain_rstep {μ : Heap} {e : Expr} {s s' : R.St} {ev : (𝕊).Event} {c' : Heap × Expr}
    (hcl : closedAt 0 e = true) (hμ : HeapClosed μ)
    (hgo : ∃ c'' : Conf (platformOf R S), PSteps (ℍ := ℍ) (platformOf R S) ⟨μ, e, s⟩ c'' ∧
      (PlatEnd (platformOf R S) Q c'' ∨ UnansweredAt (platformOf R S) S c''.e))
    (h : (𝕊).RStep R ((μ, e), s) ev (c', s')) :
    PStep (ℍ := ℍ) (platformOf R S) ⟨μ, e, s⟩ ⟨c'.1, c'.2, s'⟩ ∧ closedAt 0 c'.2 = true ∧
      HeapClosed c'.1 := by
  cases h with
  | mach h' =>
      rcases ostep_cases h' with ⟨K, a, a', he, hh, he'⟩ | ⟨l, he, -⟩ | ⟨a, he, -⟩
      · simp only at he he'
        subst he
        have hs : Step1 (ℍ := ℍ) μ (K.plug a) c'.1 c'.2 := ⟨K, a, a', rfl, he', hh⟩
        obtain ⟨h₁, h₂⟩ := closed_step1 hs hcl hμ
        exact ⟨PStep.mach hs, h₁, h₂⟩
      · simp only at he; subst he; exact (not_goes_drive hgo).elim
      · simp only at he; subst he; exact (not_goes_drive hgo).elim
  | @io _ _ _ K l i v w hterm hK ha hco =>
      change e = Kont.plug K ((𝕊).perform l i v) at hterm
      subst hterm
      obtain ⟨hst, hw⟩ := pstep_of_io hcl hK ha hco hgo
      exact ⟨hst, closedAt_plug_of hcl hw, hμ⟩

/-- **A step of a driver's configuration under the runner is a step of the drive under its
platform**, at a closed configuration whose driven term goes on under the platform: a step inside
the driven term is the platform's step in the drive phase (`plug_eq_driveE`), `again` is the
drive's, and `fin` returns the step's answer.  The configuration stays closed. -/
theorem drive_rstep {μ : Heap} {t : Expr} {s s' : R.St} {ev : (𝕊).Event} {c' : Heap × Expr}
    (hcl : closedAt 0 t = true) (hμ : HeapClosed μ)
    (hgo : ∃ c'' : Conf (platformOf R S), PSteps (ℍ := ℍ) (platformOf R S) ⟨μ, t, s⟩ c'' ∧
      (PlatEnd (platformOf R S) Q c'' ∨ UnansweredAt (platformOf R S) S c''.e))
    (h : (𝕊).RStep R ((μ, driveE t), s) ev (c', s')) :
    (∃ t', c'.2 = driveE t' ∧ closedAt 0 t' = true ∧ HeapClosed c'.1 ∧
       RStep (ℍ := ℍ) (platformOf R S) (⟨μ, t, s⟩, .drive) (⟨c'.1, t', s'⟩, .drive)) ∨
    (∃ a : Val, t = .val (Val.inj₁ a) ∧ c' = (μ, a.1)) := by
  cases h with
  | mach h' =>
      rcases ostep_cases h' with ⟨K, a, a', he, hh, he'⟩ | ⟨l, he, rfl⟩ | ⟨a, he, rfl⟩
      · simp only at he he'
        obtain ⟨K', rfl, rfl⟩ := plug_eq_driveE he.symm hh.not_isVal (head_ne_drive hh)
        have hs : Step1 (ℍ := ℍ) μ (K'.plug a) c'.1 (K'.plug a') := ⟨K', a, a', rfl, rfl, hh⟩
        obtain ⟨h₁, h₂⟩ := closed_step1 hs hcl hμ
        exact .inl ⟨K'.plug a', he', h₁, h₂, RStep.run (PStep.mach hs)⟩
      · simp only [driveE, Expr.app.injEq, true_and] at he
        subst he
        refine .inl ⟨nextE l, rfl, ?_, hμ, RStep.again⟩
        simp only [Expr.val, Val.inj₂, closedAt] at hcl
        simp [nextE, closedAt, Expr.val, Val.inj₁, Val.unit, hcl]
      · simp only [driveE, Expr.app.injEq, true_and] at he
        exact .inr ⟨a, he, rfl⟩
  | @io _ _ _ K l i v w hterm hK ha hco =>
      change driveE t = Kont.plug K ((𝕊).perform l i v) at hterm
      obtain ⟨K', rfl, rfl⟩ :=
        plug_eq_driveE hterm.symm (not_isVal_perform l i v) (perform_ne_drive l i v)
      change (Kont.appR driveMark K').HasHnd l.1 = false at hK
      have hK' : K'.HasHnd l.1 = false := by simpa [Kont.HasHnd, driveMark] using hK
      obtain ⟨hst, hw⟩ := pstep_of_io hcl hK' ha hco hgo
      exact .inl ⟨K'.plug w.1, rfl, closedAt_plug_of hcl hw, hμ, RStep.run hst⟩

end Sim

/-! ### What a run under a runner reaches -/

section Reach
variable {Ξ : EffCtx}

local notation "𝕊" => ourInst (ℍ := ℍ) orowRF Ξ tier1Open

variable {R : (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).Runner} {S : Row}

/-- The platform of a runner that keeps its protocol, at a row tied to the effect context, agrees
with the row. -/
theorem platAgree_platformOf : PlatAgree (platformOf R S) S :=
  platAgree_of_le platformOf_sub (fun _ _ _ h => h)

/-- **What a plain program's run under a runner reaches** is closed and reached by the same run
under the runner's platform. -/
theorem plain_reach (hR : R.Respects) (hS : RowAt Ξ S) {P : Expr} {A₀ : VTy}
    (hcC : cC (ℍ := ℍ) (CTy.effOf S A₀) [] LSub.empty P PMap.empty) (hP : closedAt 0 P = true)
    {x : (𝕊).RConf R} (h : (𝕊).RReach R ((𝕊).rinit R P) x) :
    closedAt 0 x.1.2 = true ∧ HeapClosed x.1.1 ∧
      PSteps (ℍ := ℍ) (platformOf R S) (init (platformOf R S) P) ⟨x.1.1, x.1.2, x.2⟩ := by
  have hPl := platformOf_respects hR hS
  have h₀ : PlatStart (platformOf R S) S (fun ls v => vC true A₀ ls LSub.empty v)
      (init (platformOf R S) P) := platStart_init ((cC_effOf S A₀ [] LSub.empty P PMap.empty).mp hcC)
  induction h with
  | refl => exact ⟨hP, heapClosed_empty, .refl⟩
  | @tail b c _ hst ih =>
      obtain ⟨ev, hst⟩ := hst
      obtain ⟨hc, hμ, hps⟩ := ih
      obtain ⟨hp, hc', hμ'⟩ := plain_rstep (μ := b.1.1) (e := b.1.2) (s := b.2) (c' := c.1)
        (s' := c.2) hc hμ (platStart_safe hPl platAgree_platformOf h₀ hps) hst
      exact ⟨hc', hμ', hps.tail hp⟩

/-- **What a driven program's run under a runner reaches**: a driver's configuration, closed, whose
driven term the drive reaches under the runner's platform; or, after `fin`, a closed value, the
answer `inl a` of a step the drive reaches. -/
theorem drive_reach (hR : R.Respects) (hS : RowAt Ξ S) {M : Expr} {S₀ : Row} {A₁ : VTy}
    (hle : RowLe S₀ S) (hC : (CTy.loopEffBody S₀ A₁ .unit).NuOk)
    (hcC : cC (ℍ := ℍ) (CTy.effOf S (.sum A₁ (.thunk (CTy.loopEff S₀ A₁ .unit)))) [] LSub.empty M
      PMap.empty) (hM : closedAt 0 M = true)
    {x : (𝕊).RConf R} (h : (𝕊).RReach R ((𝕊).rinit R (driveE M)) x) :
    (∃ t, x.1.2 = driveE t ∧ closedAt 0 t = true ∧ HeapClosed x.1.1 ∧
      Relation.ReflTransGen (RStep (ℍ := ℍ) (platformOf R S)) (init (platformOf R S) M, .drive)
        (⟨x.1.1, t, x.2⟩, .drive)) ∨
    (∃ (a : Val) (μ₀ : Heap) (s₀ : R.St), x.1.2 = a.1 ∧ closedAt 0 a.1 = true ∧
      Relation.ReflTransGen (RStep (ℍ := ℍ) (platformOf R S)) (init (platformOf R S) M, .drive)
        (⟨μ₀, .val (Val.inj₁ a), s₀⟩, .drive)) := by
  have hPl := platformOf_respects hR hS
  induction h with
  | refl => exact .inl ⟨M, rfl, hM, heapClosed_empty, .refl⟩
  | @tail b c _ hst ih =>
      obtain ⟨ev, hst⟩ := hst
      rcases ih with ⟨t, he, hc, hμ, hr⟩ | ⟨a, -, -, he, -, -⟩
      · have hst' : (𝕊).RStep R ((b.1.1, driveE t), b.2) ev (c.1, c.2) := he ▸ hst
        have hds := driveSafe_of_reach hPl platformOf_sub hle hC hcC hr
        rcases drive_rstep hc hμ (driveSafe_cont hPl platformOf_sub hds) hst' with
          ⟨t', he', hc', hμ', hs⟩ | ⟨a, rfl, hc₁⟩
        · exact .inl ⟨t', he', hc', hμ', hr.tail hs⟩
        · refine .inr ⟨a, b.1.1, b.2, by rw [hc₁], ?_, hr⟩
          simpa [Expr.val, Val.inj₁, closedAt] using hc
      · have hst' : (𝕊).RStep R ((b.1.1, a.1), b.2) ev (c.1, c.2) := he ▸ hst
        exact (no_rstep_val R a hst').elim

end Reach

/-! ### LiveOK -/

/-- A configuration whose run under a platform continues to an end or a stop goes on. -/
theorem goesOn_of_plat {RF : RowForm} {Ξ : EffCtx} {P : Platform} {Q : List SRec → Val → WProp}
    {T : Row} {μ : Heap} {e : Expr} {s : P.St}
    (hgo : ∃ c' : Conf P, PSteps (ℍ := ℍ) P ⟨μ, e, s⟩ c' ∧ (PlatEnd P Q c' ∨ UnansweredAt P T c'.e)) :
    GoesOn (ℍ := ℍ) RF Ξ (μ, e) := by
  obtain ⟨c', hc', hend⟩ := hgo
  rcases Relation.ReflTransGen.cases_head hc' with rfl | ⟨c₁, h₁, -⟩
  · rcases hend with ⟨w, -, -, -, -, -, he, -⟩ | ⟨r, K, n, i, v, o, he, hK, -⟩
    · exact .inl ⟨w, he⟩
    · exact .inr (.inr ⟨r, K, opPayload n i v, n, he, rfl, hK⟩)
  · rcases pstep_cases h₁ with ⟨⟨K, a, a', he, -, hh⟩, -⟩ | ⟨K, n, i, v, w, s', o, he, hK, -⟩
    · simp only at he
      subst he
      exact .inr (.inl ⟨_, _, OStep.mach hh⟩)
    · exact .inr (.inr ⟨false, K, opPayload n i v, n, he, rfl, by simpa [OpFree] using hK⟩)

/-- A driver's configuration whose driven term continues, under a platform, to a step's answer or
a stop goes on: at `inl a` by `fin`, at `inr l` by `again`. -/
theorem goesOn_of_drive {RF : RowForm} {Ξ : EffCtx} {P : Platform} {S₀ T : Row} {A : VTy}
    {μ : Heap} {t : Expr} {s : P.St}
    (hgo : ∃ c' : Conf P, PSteps (ℍ := ℍ) P ⟨μ, t, s⟩ c' ∧
      (PlatEnd P (QStep (ℍ := ℍ) S₀ A .unit) c' ∨ UnansweredAt P T c'.e)) :
    GoesOn (ℍ := ℍ) RF Ξ (μ, driveE t) := by
  obtain ⟨c', hc', hend⟩ := hgo
  rcases Relation.ReflTransGen.cases_head hc' with rfl | ⟨c₁, h₁, -⟩
  · rcases hend with ⟨w, ls, ρ, -, -, -, he, hQ, -⟩ | hun
    · simp only at he
      subst he
      rcases inl_or_inr_of_qStep hQ with ⟨a, rfl⟩ | ⟨l, rfl⟩
      · exact .inr (.inl ⟨_, _, OStep.fin⟩)
      · exact .inr (.inl ⟨_, _, OStep.again⟩)
    · obtain ⟨r, K, n, i, v, o, he, hK, -⟩ := unanswered_drive hun
      exact .inr (.inr ⟨r, K, opPayload n i v, n, he, rfl, hK⟩)
  · rcases pstep_cases h₁ with ⟨⟨K, a, a', he, -, hh⟩, -⟩ | ⟨K, n, i, v, w, s', o, he, hK, -⟩
    · simp only at he
      subst he
      exact .inr (.inl ⟨_, _, OStep.mach (K := .appR driveMark K) hh⟩)
    · simp only at he
      subst he
      exact .inr (.inr ⟨false, .appR driveMark K, opPayload n i v, n, rfl, rfl,
        opFree_drive.2 (by simpa [OpFree] using hK)⟩)

/-- **`LiveOK` at today's kernel** (decision D1): every configuration a typed closed program
reaches, under a runner that keeps its protocol, has a closed term and goes on.  A plain program's
run is its run under the runner's platform (`plain_reach`), which continues to an end or a stop
(`platSafe_of_ewp`); a driven program's run is the drive's (`drive_reach`, `driveSafe_cont`), or,
after `fin`, a closed value. -/
theorem liveOK_tier1Open {Ξ : EffCtx} : LiveOK (ℍ := ℍ) orowRF Ξ tier1Open := by
  rintro ⟨μ, e⟩ ⟨P, C, R, s, hR, hP, hreach⟩
  obtain ⟨S, A₀, -, hS, hcases⟩ := der_cases hP
  have hcl := closed_of_der hP
  have hPl := platformOf_respects hR hS
  rcases hcases with hcC | ⟨M, S₀, A₁, rfl, hle, hnu, rfl, hcC⟩
  · obtain ⟨hc, -, hps⟩ := plain_reach hR hS hcC hcl hreach
    refine ⟨hc, goesOn_of_plat (platStart_safe hPl platAgree_platformOf
      (platStart_init ((cC_effOf S _ [] LSub.empty P PMap.empty).mp hcC)) hps)⟩
  · have hM : closedAt 0 M = true := by simpa [driveE, driveMark, closedAt] using hcl
    rcases drive_reach hR hS hle hnu hcC hM hreach with ⟨t, he, hc, -, hr⟩ | ⟨a, -, -, he, hc, -⟩
    · simp only at he
      subst he
      refine ⟨by simp [driveE, driveMark, closedAt, hc], ?_⟩
      exact goesOn_of_drive (driveSafe_cont hPl platformOf_sub
        (driveSafe_of_reach hPl platformOf_sub hle hnu hcC hr))
    · simp only at he
      subst he
      exact ⟨hc, .inl ⟨a, rfl⟩⟩

/-! ### S3 -/

/-- A machine run is a run under every runner, its state unchanged. -/
theorem rreach_of_reach {S : A.EffectSystem} {R : S.Runner} (s : R.St) {c c' : S.Conf}
    (h : S.Reach c c') : S.RReach R (c, s) (c', s) := by
  induction h with
  | refl => exact .refl
  | tail _ hst ih =>
      obtain ⟨ev, hst⟩ := hst
      exact ih.tail ⟨ev, .mach hst⟩

theorem clsOf_eq_abortive {o : OpSig} : clsOf o.q o.B = .abortive ↔ o.abort = true := by
  unfold clsOf OpSig.abort
  by_cases h : (o.B.isZero && o.q != .lin) = true
  · simp [h]
  · rw [if_neg h]
    simp only [Bool.not_eq_true] at h
    simp only [h]
    split <;> simp

section Effects
variable {Ξ : EffCtx}

local notation "𝕊" => ourInst (ℍ := ℍ) orowRF Ξ tier1Open

/-- An operation a row finds with its row variables empty, it has at every reading. -/
theorem has_of_find_den {ε : ORow} {n i : UInt32} {o : OpSig}
    (h : Row.find (orowRF.den Ξ ε (fun _ => [])) n i = some o) (η : Targets.RVar → Row) :
    Targets.Row.Has (orowRF.den Ξ ε η) n i := by
  have h₁ : Row.find ε.ops n i = some o := by
    rw [orowRF_den] at h
    cases ht : ε.tail <;> simp only [ht, List.append_nil] at h <;> exact h
  unfold Targets.Row.Has
  rw [orowRF_den, Row.find_append, h₁]
  rfl

/-- The label of a name that a row tied to the effect context finds, at the signature the effect
context declares. -/
theorem lab_of_rowAt {S : Row} (hS : RowAt Ξ S) {n i : UInt32} {o : OpSig}
    (hf : Row.find S n i = some o) :
    ∃ l : (orowAlg Ξ).Lab, l.1 = n ∧
      ((𝕊).sig l)[i.toNat]? = some ⟨OVTy.ofV o.A, OVTy.ofV o.B, clsOf o.q o.B⟩ := by
  obtain ⟨hn, hlen, hΞ⟩ := hS n i o hf
  have hne : Ξ n ≠ [] := fun h => by simp [h] at hΞ
  exact ⟨⟨n, hn, hne, hlen⟩, rfl, sig_of_rowAt (J := tier1Open) (l := ⟨n, hn, hne, hlen⟩) hΞ⟩

/-- A configuration at a Core value is an answer of A's. -/
theorem isVal_conf (μ : Heap) (w : Val) : (𝕊).IsVal (μ, w.1) :=
  ⟨⟨OVal.ofVal w, rfl⟩, fun _ _ h => no_rstep_val (𝕊).R₀ (s := ()) w (.mach h)⟩

/-- **A stop the platform does not answer, of a row tied to the effect context, is a stop of the
row in A's sense**: the operation is a label's, of the class its signature gives, uncaught. -/
theorem stopsIn_of_unanswered {ε : ORow} {P : Platform} {μ : Heap} {e : Expr}
    (hS : RowAt Ξ (orowRF.den Ξ ε (fun _ => [])))
    (h : UnansweredAt P (orowRF.den Ξ ε (fun _ => [])) e) : (𝕊).StopsIn ε (μ, e) := by
  obtain ⟨r, K, n, i, v, o, rfl, hK, hf, hab, -⟩ := h
  obtain ⟨l, rfl, hsig⟩ := lab_of_rowAt hS hf
  have hhas : (𝕊).has ε l i.toNat := ⟨i.toNat_lt, fun η => by
    show Targets.Row.Has (orowRF.den Ξ ε η) l.1 (UInt32.ofNat i.toNat)
    rw [UInt32.ofNat_toNat]
    exact has_of_find_den hf η⟩
  have hHnd : K.HasHnd l.1 = false := by
    cases r
    · simpa [OpFree] using hK
    · exact hasHnd_of_catches K (by simpa [OpFree] using hK)
  refine ⟨K, l, i.toNat, OVal.ofVal v, _, hsig, hhas, hHnd, ?_⟩
  cases r
  · refine .inl ⟨?_, fun h => ?_⟩
    · show K.plug (opE false (opPayload l.1 i v)) = K.plug ((𝕊).perform l i.toNat (OVal.ofVal v))
      rw [perform_toNat]; rfl
    · rw [clsOf_eq_abortive.1 h] at hab; cases hab
  · refine .inr ⟨?_, clsOf_eq_abortive.2 hab, noUnwind_of_catches K (by simpa [OpFree] using hK)⟩
    show K.plug (opE true (opPayload l.1 i v)) = K.plug ((𝕊).raise l i.toNat (OVal.ofVal v))
    rw [raise_toNat]; rfl

/-- **At a configuration whose run, under a platform that answers nothing, continues to an end or a
stop**: it is an answer, it steps, or it is stopped at an operation of the row. -/
theorem effTri_of_plat {ε : ORow} {P : Platform} {Q : List SRec → Val → WProp} {μ : Heap} {e : Expr}
    {s : P.St} (hS : RowAt Ξ (orowRF.den Ξ ε (fun _ => [])))
    (hnone : ∀ n i o, Row.find P.ops n i ≠ some o)
    (hgo : ∃ c' : Conf P, PSteps (ℍ := ℍ) P ⟨μ, e, s⟩ c' ∧
      (PlatEnd P Q c' ∨ UnansweredAt P (orowRF.den Ξ ε (fun _ => [])) c'.e)) :
    (𝕊).IsVal (μ, e) ∨ (∃ ev c', (𝕊).step (μ, e) ev c') ∨ (𝕊).StopsIn ε (μ, e) := by
  obtain ⟨c', hc', hend⟩ := hgo
  rcases Relation.ReflTransGen.cases_head hc' with rfl | ⟨c₁, h₁, -⟩
  · rcases hend with ⟨w, -, -, -, -, -, he, -⟩ | hun
    · simp only at he
      subst he
      exact .inl (isVal_conf μ w)
    · exact .inr (.inr (stopsIn_of_unanswered hS hun))
  · rcases pstep_cases h₁ with ⟨⟨K, a, a', he, -, hh⟩, -⟩ | ⟨K, n, i, v, w, s', o, -, -, hf, -⟩
    · simp only at he
      subst he
      exact .inr (.inl ⟨_, _, OStep.mach hh⟩)
    · exact (hnone n i o hf).elim

/-- The same at a driver's configuration, its driven term's run continuing to a step's answer or a
stop. -/
theorem effTri_of_drive {ε : ORow} {P : Platform} {S₀ : Row} {A : VTy} {μ : Heap} {t : Expr}
    {s : P.St} (hS : RowAt Ξ (orowRF.den Ξ ε (fun _ => [])))
    (hnone : ∀ n i o, Row.find P.ops n i ≠ some o)
    (hgo : ∃ c' : Conf P, PSteps (ℍ := ℍ) P ⟨μ, t, s⟩ c' ∧
      (PlatEnd P (QStep (ℍ := ℍ) S₀ A .unit) c' ∨
        UnansweredAt P (orowRF.den Ξ ε (fun _ => [])) c'.e)) :
    (𝕊).IsVal (μ, driveE t) ∨ (∃ ev c', (𝕊).step (μ, driveE t) ev c') ∨
      (𝕊).StopsIn ε (μ, driveE t) := by
  obtain ⟨c', hc', hend⟩ := hgo
  rcases Relation.ReflTransGen.cases_head hc' with rfl | ⟨c₁, h₁, -⟩
  · rcases hend with ⟨w, ls, ρ, -, -, -, he, hQ, -⟩ | hun
    · simp only at he
      subst he
      rcases inl_or_inr_of_qStep hQ with ⟨a, rfl⟩ | ⟨l, rfl⟩
      · exact .inr (.inl ⟨_, _, OStep.fin⟩)
      · exact .inr (.inl ⟨_, _, OStep.again⟩)
    · exact .inr (.inr (stopsIn_of_unanswered hS (unanswered_drive hun)))
  · rcases pstep_cases h₁ with ⟨⟨K, a, a', he, -, hh⟩, -⟩ | ⟨K, n, i, v, w, s', o, -, -, hf, -⟩
    · simp only at he
      subst he
      exact .inr (.inl ⟨_, _, OStep.mach (K := .appR driveMark K) hh⟩)
    · exact (hnone n i o hf).elim

/-- **S3 at today's kernel** (decision D1): every configuration a typed closed program reaches is
an answer, steps, or is stopped at an operation of its row.  A machine run is a run under the runner
that answers nothing, whose platform answers nothing; what that run reaches goes on under the
platform (`plain_reach`, `drive_reach`), to an end or a stop of the row (`platSafe_of_ewp`,
`driveSafe_cont`), and a stop of a row tied to the effect context is a stop in A's sense
(`stopsIn_of_unanswered`). -/
theorem effSafe_ourInst_tier1Open : (𝕊).EffSafe := by
  intro e ε A hd c hc
  obtain ⟨μc, ec⟩ := c
  have hr := rreach_of_reach (R := (𝕊).R₀) () hc
  have hR : (𝕊).R₀.Respects := fun _ _ _ h => h.elim
  obtain ⟨S, A₀, hC, hS, hcases⟩ := der_cases hd
  have hC' : CTy.effOf (orowRF.den Ξ ε (fun _ => [])) (A.den (fun _ => [])) = CTy.effOf S A₀ := hC
  obtain ⟨rfl, rfl⟩ := effOf_inj hC'
  have hcl := closed_of_der hd
  have hPl := platformOf_respects hR hS
  have hnone : ∀ n i o, Row.find (platformOf (𝕊).R₀ (orowRF.den Ξ ε (fun _ => []))).ops n i ≠
      some o := by
    intro n i o hf
    obtain ⟨-, l, -, h⟩ := find_platformOf.1 hf
    exact h
  rcases hcases with hcC | ⟨M, S₀, A₁, rfl, hle, hnu, he₀, hcC⟩
  · obtain ⟨-, -, hps⟩ := plain_reach hR hS hcC hcl hr
    exact effTri_of_plat hS hnone (platStart_safe hPl platAgree_platformOf
      (platStart_init ((cC_effOf _ _ [] LSub.empty e PMap.empty).mp hcC)) hps)
  · have hM : closedAt 0 M = true := by simpa [driveE, driveMark, closedAt] using hcl
    rw [he₀] at hcC
    rcases drive_reach hR hS hle hnu hcC hM hr with ⟨t, he, -, -, hrs⟩ | ⟨a, -, -, he, -, -⟩
    · simp only at he
      subst he
      exact effTri_of_drive hS hnone (driveSafe_cont hPl platformOf_sub
        (driveSafe_of_reach hPl platformOf_sub hle hnu hcC hrs))
    · simp only at he
      subst he
      exact .inl (isVal_conf μc a)

end Effects

/-! ### S2 -/

/-- A run along a path reaches its last configuration. -/
theorem rreach_of_path {S : A.EffectSystem} {R : S.Runner} :
    ∀ {c : S.RConf R} {q : List (S.Event × S.RConf R)}, S.RPath R c q → S.RReach R c (S.lastC c q)
  | _, _, .nil => .refl
  | _, _, @A.EffectSystem.RPath.cons _ _ c ev c' q h hp => by
      rw [A.EffectSystem.lastC_cons]
      exact (Relation.ReflTransGen.single ⟨ev, h⟩).trans (rreach_of_path hp)

/-- A loop sum is not data. -/
theorem not_data_thunkSum {A₁ : VTy} {C : CTy} : ¬ (VTy.sum A₁ (.thunk C)).Data := by
  intro h
  cases h with
  | sum _ h₂ => cases h₂

/-- A run of a driver's configuration under a platform stays at the driver's configurations. -/
theorem psteps_drive_shape {P : Platform} {μ : Heap} {t : Expr} {s : P.St} {c : Conf P}
    (h : PSteps (ℍ := ℍ) P ⟨μ, driveE t, s⟩ c) : ∃ t', c.e = driveE t' := by
  induction h with
  | refl => exact ⟨t, rfl⟩
  | tail _ hst ih =>
      obtain ⟨t₁, ht₁⟩ := ih
      rcases pstep_cases hst with ⟨⟨K, a, a', he, he', hh⟩, -⟩ |
        ⟨K, n, i, v, w, s', o, he, -, -, -, rfl⟩
      · rw [ht₁] at he
        obtain ⟨K', rfl, -⟩ := plug_eq_driveE he.symm hh.not_isVal (head_ne_drive hh)
        exact ⟨K'.plug a', he'⟩
      · rw [ht₁] at he
        obtain ⟨K', rfl, -⟩ := plug_eq_driveE he.symm (opE_not_isVal false (opPayload n i v))
          (fun b h => by injection h with h₁; injection h₁ with h₂; cases h₂)
        exact ⟨K'.plug (.val w), rfl⟩

section Safety
variable {Ξ : EffCtx}

local notation "𝕊" => ourInst (ℍ := ℍ) orowRF Ξ tier1Open

variable {R : (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).Runner}

/-- A run under the runner's platform is a run under the runner. -/
theorem rreach_of_psteps {S : Row} {cc cc' : Conf (platformOf R S)}
    (h : PSteps (ℍ := ℍ) (platformOf R S) cc cc') :
    (𝕊).RReach R ((cc.μ, cc.e), cc.s) ((cc'.μ, cc'.e), cc'.s) := by
  induction h with
  | refl => exact .refl
  | tail _ hst ih =>
      obtain ⟨ev, h⟩ := rstep_of_pstep hst
      exact ih.tail ⟨ev, h⟩

/-- A step of the driven term under the runner's platform is a step of the driver's configuration
under the runner. -/
theorem rstep_drive_of_pstep {S : Row} {μ : Heap} {t : Expr} {s : R.St}
    {cc' : Conf (platformOf R S)} (h : PStep (ℍ := ℍ) (platformOf R S) ⟨μ, t, s⟩ cc') :
    ∃ ev, (𝕊).RStep R ((μ, driveE t), s) ev ((cc'.μ, driveE cc'.e), cc'.s) := by
  rcases pstep_cases h with ⟨⟨K, a, a', he, he', hh⟩, hs⟩ |
    ⟨K, n, i, v, w, s', o, he, hK, hf, hco, rfl⟩
  · simp only at he he' hs
    subst he
    rw [he', hs]
    exact ⟨_, .mach (OStep.mach (K := .appR driveMark K) hh)⟩
  · simp only at he
    subst he
    obtain ⟨-, l, rfl, ha⟩ := find_platformOf.1 hf
    rw [platformOf_co] at hco
    obtain ⟨l', w', hl', hR, hw', -⟩ := coOf_some hco
    have hll : l' = l := Subtype.ext hl'
    rw [hll] at hR
    have hst : (𝕊).RStep R ((μ, driveE (K.plug (performE (.val (opPayload l.1 i v))))), s)
        (.io l i.toNat (OVal.ofVal v) w') ((μ, (Kont.appR driveMark K).plug w'.1), s') :=
      A.EffectSystem.RStep.io (S := 𝕊) (R := R)
        (c := (μ, driveE (K.plug (performE (.val (opPayload l.1 i v)))))) (s := s) (s' := s')
        (K := .appR driveMark K) (l := l) (i := i.toNat) (v := OVal.ofVal v) (w := w')
        (by show _ = Kont.plug (.appR driveMark K) ((𝕊).perform l i.toNat (OVal.ofVal v))
            rw [perform_toNat]; rfl)
        (by show (Kont.appR driveMark K).HasHnd l.1 = false
            simpa [Kont.HasHnd, driveMark] using hK) ha hR
    rw [show (Kont.appR driveMark K).plug w'.1 = driveE (K.plug (Expr.val w)) by
      rw [hw']; rfl] at hst
    exact ⟨_, hst⟩

/-- Under a runner that answers the row, its platform answers the row. -/
theorem rowLe_platformOf {ε : ORow} (hS : RowAt Ξ (orowRF.den Ξ ε (fun _ => [])))
    (hans : (𝕊).Answers R ε) :
    RowLe (orowRF.den Ξ ε (fun _ => [])) (platformOf R (orowRF.den Ξ ε (fun _ => []))).ops := by
  intro n i o hf
  obtain ⟨l, rfl, -⟩ := lab_of_rowAt hS hf
  refine find_platformOf.2 ⟨hf, l, rfl, hans l i.toNat ⟨i.toNat_lt, fun η => ?_⟩⟩
  show Targets.Row.Has (orowRF.den Ξ ε η) l.1 (UInt32.ofNat i.toNat)
  rw [UInt32.ofNat_toNat]
  exact has_of_find_den hf η

/-- **S2 at today's kernel** (decision D1): under a runner that keeps its protocol and answers the
row, a typed program at a data answer has every run never stuck, terminating, and ending at a data
value of the answer type; a driven program whose step answers `A ⊕ L` at data `A` has every run
never stuck and ending at a data value of `A`.  The runner's platform answers the row
(`rowLe_platformOf`), so B2 applies: `adequateRetAt_core` to a plain program, whose run is its run
under the platform (`plain_reach`, `plain_rstep`), and `safeDriveFrom_of_rel` to a driven one,
whose run is the drive's (`drive_reach`). -/
theorem safety_ourInst_tier1Open : (𝕊).Safety := by
  intro R hR ε hans
  refine ⟨fun e A hA hd => ?_, fun M A L hA hd => ?_⟩
  · obtain ⟨S, A₀, hC, hS, hcases⟩ := der_cases hd
    have hC' : CTy.effOf (orowRF.den Ξ ε (fun _ => [])) (A.den (fun _ => [])) =
        CTy.effOf S A₀ := hC
    obtain ⟨rfl, rfl⟩ := effOf_inj hC'
    have hdata := data_den_of_dataTy hA (fun _ => [])
    rcases hcases with hcC | ⟨M, S₀, A₁, rfl, -, -, he₀, -⟩
    swap
    · rw [he₀] at hdata; exact (not_data_thunkSum hdata).elim
    have hcl := closed_of_der hd
    have hPl := platformOf_respects hR hS
    have hle := rowLe_platformOf hS hans
    obtain ⟨hsafe, hterm⟩ := adequateRetAt_core (platformOf R _) hPl _ _ e hdata hle hcC
    have h₀ : PlatStart (platformOf R (orowRF.den Ξ ε (fun _ => []))) _
        (fun ls v => vC true (A.den (fun _ => [])) ls LSub.empty v) (init _ e) :=
      platStart_init ((cC_effOf _ _ [] LSub.empty e PMap.empty).mp hcC)
    have hA' : A = OVTy.ofV (A.den (fun _ => [])) := (ofV_den_of_dataTy hA _).symm
    refine ⟨?_, fun _ => ⟨?_, ?_⟩, fun q hq => ?_⟩
    · rintro ⟨⟨μ, e'⟩, s⟩ hx
      obtain ⟨-, -, hps⟩ := plain_reach hR hS hcC hcl hx
      rcases hsafe _ hps with ⟨w, he, -, -⟩ | ⟨cc', hcc'⟩
      · simp only at he
        subst he
        exact .inl (isVal_conf μ w)
      · obtain ⟨ev, hev⟩ := rstep_of_pstep hcc'
        exact .inr ⟨ev, _, hev⟩
    · rintro ⟨⟨μ, e'⟩, s⟩ hx
      obtain ⟨-, -, hps⟩ := plain_reach hR hS hcC hcl hx
      obtain ⟨cc', hcc', w, he, -, -⟩ := hterm.1 _ hps
      refine ⟨((cc'.μ, cc'.e), cc'.s), rreach_of_psteps hcc', ?_⟩
      rw [he]
      exact isVal_conf cc'.μ w
    · rintro ⟨f, hf0, hf⟩
      have hreach : ∀ n, (𝕊).RReach R ((𝕊).rinit R e) (f n) := by
        intro n
        induction n with
        | zero => rw [hf0]; exact .refl
        | succ k ih =>
            obtain ⟨ev, h⟩ := hf k
            exact ih.tail ⟨ev, h⟩
      refine hterm.2 ⟨fun n => ⟨(f n).1.1, (f n).1.2, (f n).2⟩, by simp only [hf0]; rfl,
        fun n => ?_⟩
      obtain ⟨hc, hμ, hps⟩ := plain_reach hR hS hcC hcl (hreach n)
      obtain ⟨ev, h⟩ := hf n
      exact (plain_rstep (μ := (f n).1.1) (e := (f n).1.2) (s := (f n).2) (c' := (f (n + 1)).1)
        (s' := (f (n + 1)).2) hc hμ (platStart_safe hPl platAgree_platformOf h₀ hps) h).1
    · obtain ⟨hpath, ⟨v, hv⟩, -⟩ := hq
      have hx := rreach_of_path hpath
      obtain ⟨hc, -, hps⟩ := plain_reach hR hS hcC hcl hx
      have hv' : ((𝕊).lastC ((𝕊).rinit R e) q).1.2 = v.1 := hv
      have hcv : IsVal ((𝕊).lastC ((𝕊).rinit R e) q).1.2 :=
        isVal_of_closed_oval (hv' ▸ v.2) hc
      obtain ⟨cc', hcc', w, he, hw, -⟩ := hterm.1 _ hps
      obtain rfl := psteps_from_val (v := ⟨_, hcv⟩) rfl hcc'
      exact ⟨OVal.ofVal w, he, dataVal_ofVal hA hA' hw⟩
  · obtain ⟨S, A₀, hC, hS, hcases⟩ := der_cases hd
    have hC' : CTy.effOf (orowRF.den Ξ ε (fun _ => [])) ((OVTy.sum A L).den (fun _ => [])) =
        CTy.effOf S A₀ := hC
    obtain ⟨rfl, rfl⟩ := effOf_inj hC'
    have hPl := platformOf_respects hR hS
    have hle := rowLe_platformOf hS hans
    have hcl : closedAt 0 (driveE M) = true := closed_of_der hd
    have hM : closedAt 0 M = true := by simpa [driveE, driveMark, closedAt] using hcl
    rcases hcases with hcC | ⟨M', S₀, A₁, hMM, hle₀, hnu, he₀, hcC⟩
    · exfalso
      obtain ⟨c', hc', w, -, -, -, -, -, he, -⟩ := platStart_cont hPl hle
        (platStart_init ((cC_effOf _ _ [] LSub.empty _ PMap.empty).mp hcC)) .refl
      obtain ⟨t', ht'⟩ := psteps_drive_shape hc'
      have : IsVal (driveE t') := by rw [← ht', he]; exact w.2
      cases this
    · have hMM' : driveE M = driveE M' := hMM
      injection hMM' with h₁ h₂
      subst h₂
      have he₁ : VTy.sum (A.den (fun _ => [])) (L.den (fun _ => [])) =
          .sum A₁ (.thunk (CTy.loopEff S₀ A₁ .unit)) := he₀
      obtain ⟨hA₁, -⟩ := VTy.sum.inj he₁
      have hdata : A₁.Data := hA₁ ▸ data_den_of_dataTy hA _
      rw [he₀] at hcC
      have hsd := safeDriveFrom_of_rel hPl hle hle₀ hdata hnu hcC
      have hA' : A = OVTy.ofV A₁ := hA₁ ▸ (ofV_den_of_dataTy hA _).symm
      refine ⟨?_, fun q hq => ?_⟩
      · rintro ⟨⟨μ, e'⟩, s⟩ hx
        rcases drive_reach hR hS hle₀ hnu hcC hM hx with ⟨t, he, -, -, hrs⟩ | ⟨a, -, -, he, -, -⟩
        · simp only at he
          subst he
          right
          rcases hsd _ hrs with ⟨a, hta, -, -⟩ | ⟨rc', hrc'⟩
          · simp only at hta
            subst hta
            exact ⟨_, _, .mach OStep.fin⟩
          · rcases rstep_cases hrc' with ⟨hp, -⟩ | ⟨hph, -⟩ | ⟨-, l, hel, -⟩
            · obtain ⟨ev, hev⟩ := rstep_drive_of_pstep hp
              exact ⟨ev, _, hev⟩
            · cases hph
            · simp only at hel
              subst hel
              exact ⟨_, _, .mach OStep.again⟩
        · simp only at he
          subst he
          exact .inl (isVal_conf μ a)
      · obtain ⟨hpath, ⟨v, hv⟩, -⟩ := hq
        have hx := rreach_of_path hpath
        rcases drive_reach hR hS hle₀ hnu hcC hM hx with ⟨t, he, -, -, -⟩ |
          ⟨a, μ₀, s₀, he, -, hrs⟩
        · exfalso
          have hv' : v.1 = driveE t := by rw [← he]; exact hv.symm
          have h₂ : IsOVal (driveE t) := hv' ▸ v.2
          exact not_isOVal_prim_app (p := .lit (.u8 0)) (by decide) t h₂
        · refine ⟨OVal.ofVal a, he, ?_⟩
          rcases hsd _ hrs with ⟨a', ha', hda, -⟩ | ⟨rc', hrc'⟩
          · have haa : a = a' := Val.inj₁_inj' (Subtype.ext (by simpa using ha'))
            subst haa
            exact dataVal_ofVal hA hA' hda
          · exfalso
            rcases rstep_cases hrc' with ⟨hp, -⟩ | ⟨hph, -⟩ | ⟨-, l, hel, -⟩
            · exact no_pstep_of_val rfl hp
            · cases hph
            · simp [Expr.val, Val.inj₁, Val.inj₂] at hel

end Safety

end Targets.Inst

end
