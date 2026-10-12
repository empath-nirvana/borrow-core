import Targets.I.J1
import Targets.Instance.AlgSim

/-!
# The interaction — algebraicity at `J₁`

Algebraicity as restated (a finaliser's start observed but not its code, `A.EffectSystem.AlgLaw`)
holds at our instance at every typing system whose typed programs' runs are `AlgGood`
(`Inst.algLaw_of_good`, `Targets/Instance/AlgSim.lean`).  At a typing system whose closed programs
are Core's (`CoreClosed`: `J₁` at every effect context, today's kernel) four of `AlgGood`'s five
parts are facts of Core's relation:

* **closed, going on**: `LiveOK` (`liveOK_of_coreClosed`);
* **data answers** (`lamFree_answer_of_coreClosed`): a configuration a typed program at a data
  answer reaches at a value is at a data value — the run under the runner's platform continues to
  an end in the program's postcondition or to a stop of its row (`platStart_safe`), and a value
  takes no step;
* **the platform asked at data** (`lamFree_io_of_coreClosed`): an operation the runner answers is
  asked at a data argument — every run of a program safe under the platform restricted to data
  arguments (`Platform.restrict`) keeps the protocol (`platData_of_start`, after B5's
  `platData_of_safe`), and the operation is the platform's (a stop it does not answer would be a
  stop of the row the runner answers).

The fifth, that every error a typed program's run keeps at a running finaliser's `cfin` frame holds
no λ, is the hypothesis `KeptLamFree`.  It is what the simulation reads: `AlgRel` relates λ-terms
structurally, so two related kept errors are equal terms when they hold no λ, and their `finEnd`
labels are then equal, as decision D4 observes them.  `CfinQuiet` (no `[cfin-raise]` step at all)
gives it (`keptLamFree_of_cfinQuiet`), and fails at `J₁` (`not_cfinQuiet_J₁`: SPEC §27 types a
finaliser that raises to a live handler).  `KeptLamFree` is not proved here: Core's relation gives
a raised argument's type inside `[then]`'s compatibility, and no lemma carries a fact of the
relation to the configurations of a run.

So algebraicity as restated holds at `J₁` given `KeptLamFree` (`I.algLaw_J₁_of`).  `[Core σ=[]]`
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets.Inst
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont performE raiseE opPayload hndE ubindE ccatchE cfinE)
open BoCa.Lifetime (LSub LifeCtx)
open Targets (RowForm EffCtx orowRF orowAlg ORow RowAt RowEnv RowCtx Platform PStep PSteps Conf
  DataVal PlatEnd UnansweredAt PlatAgree PlatStart platStart_init platStart_safe psteps_from_val
  pstep_cases init opPlug_no_step PlatData Platform.restrict restrict_respects pstep_restrict)

/-! ### The platform's protocol on every run from a start -/

/-- **Where the restricted platform continues, the protocol holds**: an operation the platform
answers, stopped at a configuration from which the run under the restricted platform continues to
an end or to a stop it does not answer, is asked at a data argument. -/
theorem platData_of_cont {P : Platform} {S : Row} {Q : List SRec → Val → WProp} {c : Conf P}
    (h : ∃ c', PSteps (ℍ := ℍ) P.restrict c.toRestrict c' ∧
      (PlatEnd P.restrict Q c' ∨ UnansweredAt P.restrict S c'.e)) :
    PlatData P c := by
  intro K n i v o he hK hf
  obtain ⟨c', hc', hend⟩ := h
  rcases Relation.ReflTransGen.cases_head hc' with rfl | ⟨c₁, h₁, -⟩
  · exfalso
    rcases hend with ⟨w, -, -, -, -, -, hw, -⟩ | ⟨r, K', n', i', v', o', he', hK', -, -, hP⟩
    · exact plug_perform_ne_val K _ w (he.symm.trans hw)
    · have h' : K.plug (opE false (opPayload n i v)) = K'.plug (opE r (opPayload n' i' v')) :=
        he.symm.trans he'
      obtain ⟨rfl, rfl, hpay⟩ := plug_opE_eq h'
      obtain ⟨rfl, rfl, rfl⟩ := opPayload_inj hpay
      have := hP rfl
      simp only [Platform.restrict] at this
      rw [hf] at this
      cases this
  · rcases pstep_cases h₁ with ⟨hs, -⟩ | ⟨K₂, n₂, i₂, v₂, w₂, s₂, o₂, he₂, -, hf₂, hco₂, -⟩
    · exact absurd (show Step1 (ℍ := ℍ) c.μ c.e _ _ from hs)
        (by rw [he]; exact opPlug_no_step (r := false) (payloadName_opPayload n i v) hK)
    · change c.e = _ at he₂
      rw [he] at he₂
      obtain ⟨rfl, hp⟩ := plug_perform_inj he₂
      obtain ⟨rfl, rfl, rfl⟩ := opPayload_inj hp
      simp only [Platform.restrict] at hco₂
      split_ifs at hco₂ with hd
      obtain ⟨o'', hf'', hd''⟩ := hd
      rw [hf] at hf''
      cases hf''
      exact hd''

/-- **Every run from a start in Core's relation keeps the platform's protocol**: each configuration
it reaches under a platform that keeps its protocol and agrees with the row asks the platform at
data arguments only; the run is also a run under the restricted platform. -/
theorem platData_of_start {P : Platform} (hP : P.Respects) {S : Row} (hag : PlatAgree P S)
    {Q : List SRec → Val → WProp} {e : Expr}
    (h₀ : ewpTS (ℍ := ℍ) [] e (opTable (Row.tab S LSub.empty)) Q PMap.empty) :
    ∀ c, PSteps (ℍ := ℍ) P (init P e) c →
      PlatData P c ∧ PSteps (ℍ := ℍ) P.restrict (init P.restrict e) c.toRestrict := by
  have hP' := restrict_respects hP
  have hag' : PlatAgree P.restrict S := fun n i o o' h₁ h₂ => hag n i o o' h₁ h₂
  have hst : PlatStart P.restrict S Q (init P.restrict e) := platStart_init h₀
  intro c h
  induction h with
  | refl =>
      have hr : PSteps (ℍ := ℍ) P.restrict (init P.restrict e) (init P e).toRestrict := .refl
      exact ⟨platData_of_cont (platStart_safe hP' hag' hst hr), hr⟩
  | tail _ hbc ih =>
      obtain ⟨hPD, hr⟩ := ih
      have hr' := hr.tail (pstep_restrict hPD hbc)
      exact ⟨platData_of_cont (platStart_safe hP' hag' hst hr'), hr'⟩

/-! ### What a typed program's runs give algebraicity -/

section Facts
variable {Ξ : EffCtx} {D : RowCtx → LifeCtx → Ctx OVTy → Expr → OJdg → Prop}

local notation "𝕊" => ourInst (ℍ := ℍ) orowRF Ξ (OurTyping.ofDer D)

variable {R : (ourInst (ℍ := ℍ) orowRF Ξ (OurTyping.ofDer D)).Runner}

/-- A program typed at a data answer is a plain program in Core's relation at its row, read with
its row variables empty, at a data type. -/
theorem plain_of_dataTy (hJ : CoreClosed (OurTyping.ofDer D)) {P : Expr} {ε : ORow} {A : OVTy}
    (hA : (𝕊).DataTy A) (hP : (𝕊).der [] P ((𝕊).F ε A)) :
    RowAt Ξ (orowRF.den Ξ ε (fun _ => [])) ∧ (A.den (fun _ => [])).Data ∧ closedAt 0 P = true ∧
      cC (ℍ := ℍ) (CTy.effOf (orowRF.den Ξ ε (fun _ => [])) (A.den (fun _ => []))) [] LSub.empty P
        PMap.empty := by
  obtain ⟨S, A₀, hC, hS, hcases⟩ := der_cases hJ hP
  have hC' : CTy.effOf (orowRF.den Ξ ε (fun _ => [])) (A.den (fun _ => [])) = CTy.effOf S A₀ := hC
  obtain ⟨rfl, rfl⟩ := effOf_inj hC'
  have hdata := data_den_of_dataTy hA (fun _ => [])
  refine ⟨hS, hdata, closed_of_der hJ hP, ?_⟩
  rcases hcases with hcC | ⟨M, S₀, A₁, rfl, -, -, he₀, -⟩
  · exact hcC
  · rw [he₀] at hdata; exact (not_data_thunkSum hdata).elim

/-- **A typed program at a data answer answers data**: a configuration its run reaches at a value is
at a data value of the answer type, so at a term with no λ. -/
theorem lamFree_answer_of_coreClosed (hJ : CoreClosed (OurTyping.ofDer D)) (hR : R.Respects)
    {P : Expr} {ε : ORow} {A : OVTy} (hA : (𝕊).DataTy A) (hP : (𝕊).der [] P ((𝕊).F ε A))
    {x : (𝕊).RConf R} (hx : (𝕊).RReach R ((𝕊).rinit R P) x) (hv : IsVal x.1.2) :
    lamFree x.1.2 = true := by
  obtain ⟨hS, hdata, hcl, hcC⟩ := plain_of_dataTy hJ hA hP
  have hPl := platformOf_respects hR hS
  obtain ⟨-, -, hps⟩ := plain_reach hR hS hcC hcl hx
  have h₀ : PlatStart (platformOf R (orowRF.den Ξ ε (fun _ => []))) _
      (fun ls v => vC true (A.den (fun _ => [])) ls LSub.empty v) (init _ P) :=
    platStart_init ((cC_effOf _ _ [] LSub.empty P PMap.empty).mp hcC)
  obtain ⟨c', hc', hend⟩ := platStart_safe hPl platAgree_platformOf h₀ hps
  obtain rfl := psteps_from_val (v := ⟨x.1.2, hv⟩) rfl hc'
  rcases hend with ⟨w, ls, ρ, -, -, -, he, hQ, -⟩ | ⟨r, K, n, i, v, o, he, -⟩
  · change x.1.2 = w.1 at he
    rw [he]
    exact lamFree_of_dataVal ((vC_data hdata).mp hQ).2
  · change x.1.2 = K.plug (opE r (opPayload n i v)) at he
    exact absurd (K.isVal_of_plug (he ▸ hv)) (opE_not_isVal r _)

/-- **A typed program asks the runner at data arguments**: at a configuration its run reaches, an
operation no handler of its context catches and the runner answers is at an argument with no λ. -/
theorem lamFree_io_of_coreClosed (hJ : CoreClosed (OurTyping.ofDer D)) (hR : R.Respects)
    {P : Expr} {ε : ORow} {A : OVTy} (hA : (𝕊).DataTy A) (hP : (𝕊).der [] P ((𝕊).F ε A))
    {x : (𝕊).RConf R} (hx : (𝕊).RReach R ((𝕊).rinit R P) x) {K : Kont} {l : (orowAlg Ξ).Lab}
    {i : ℕ} {v : OVal} (hterm : x.1.2 = K.plug ((𝕊).perform l i v)) (hK : K.HasHnd l.1 = false)
    (ha : R.answers l i) : lamFree v.1 = true := by
  obtain ⟨hS, -, hcl, hcC⟩ := plain_of_dataTy hJ hA hP
  have hPl := platformOf_respects hR hS
  obtain ⟨hc, -, hps⟩ := plain_reach hR hS hcC hcl hx
  have hew := (cC_effOf _ _ [] LSub.empty P PMap.empty).mp hcC
  have hPD := (platData_of_start hPl platAgree_platformOf hew _ hps).1
  rcases perform_cases (ℍ := ℍ) (J := OurTyping.ofDer D) l i v with ⟨hi, hp⟩ | ⟨-, hp⟩
  swap
  · rw [hterm, hp, not_closed_opJunk] at hc; cases hc
  have hvcl : closedAt 0 v.1 = true := by
    rw [hterm, hp] at hc
    have := closedAt_plug_inv K hc
    simp only [performE, opArgE, closedAt, Expr.val, Val.prim, Val.i32, Bool.true_and] at this
    exact this
  let v₀ : Val := ⟨v.1, isVal_of_closed_oval v.2 hvcl⟩
  have he₀ : x.1.2 = K.plug (performE (.val (opPayload l.1 (UInt32.ofNat i) v₀))) := by
    rw [hterm, hp]; rfl
  have hi' : (UInt32.ofNat i).toNat = i := UInt32.toNat_ofNat_of_lt' hi
  -- the operation is the platform's: a stop it does not answer would be a stop of the row the
  -- runner answers
  have hfo : ∃ o, Row.find (platformOf R (orowRF.den Ξ ε (fun _ => []))).ops l.1
      (UInt32.ofNat i) = some o := by
    have h₀ : PlatStart (platformOf R (orowRF.den Ξ ε (fun _ => []))) _
        (fun ls v => vC true (A.den (fun _ => [])) ls LSub.empty v) (init _ P) := platStart_init hew
    obtain ⟨c', hc', hend⟩ := platStart_safe hPl platAgree_platformOf h₀ hps
    rcases Relation.ReflTransGen.cases_head hc' with rfl | ⟨c₁, h₁, -⟩
    · exfalso
      rcases hend with ⟨w, -, -, -, -, -, hw, -⟩ | ⟨r, K', n', i', v', o', he', hK', hf', -, hP'⟩
      · exact plug_perform_ne_val K _ w (he₀.symm.trans hw)
      · have h' : K.plug (opE false (opPayload l.1 (UInt32.ofNat i) v₀)) =
            K'.plug (opE r (opPayload n' i' v')) := he₀.symm.trans he'
        obtain ⟨rfl, rfl, hpay⟩ := plug_opE_eq h'
        obtain ⟨rfl, rfl, rfl⟩ := opPayload_inj hpay
        have hfP := find_platformOf.2 ⟨hf', l, rfl, hi'.symm ▸ ha⟩
        rw [hP' rfl] at hfP; cases hfP
    · rcases pstep_cases h₁ with ⟨hs, -⟩ | ⟨K₂, n₂, i₂, v₂, w₂, s₂, o₂, he₂, -, hf₂, -, -⟩
      · exact absurd (show Step1 (ℍ := ℍ) x.1.1 x.1.2 _ _ from hs)
          (by rw [he₀]; exact opPlug_no_step (r := false) (payloadName_opPayload _ _ _) hK)
      · change x.1.2 = _ at he₂
        rw [he₀] at he₂
        obtain ⟨rfl, hp'⟩ := plug_perform_inj he₂
        obtain ⟨rfl, rfl, rfl⟩ := opPayload_inj hp'
        exact ⟨o₂, hf₂⟩
  obtain ⟨o, hf⟩ := hfo
  exact lamFree_of_dataVal (hPD K l.1 (UInt32.ofNat i) v₀ o he₀ hK hf)

/-- **What a typed program's runs give algebraicity**, given that every error they keep holds no
λ: every configuration its run reaches is `AlgGood`. -/
theorem algGood_of_coreClosed (hJ : CoreClosed (OurTyping.ofDer D))
    (hk : KeptLamFree (ℍ := ℍ) orowRF Ξ (OurTyping.ofDer D)) (hR : R.Respects) {P : Expr}
    {ε : ORow} {A : OVTy} (hA : (𝕊).DataTy A) (hP : (𝕊).der [] P ((𝕊).F ε A))
    {x : (𝕊).RConf R} (hx : (𝕊).RReach R ((𝕊).rinit R P) x) : AlgGood R x := by
  have hlive : (𝕊).Live x.1 := ⟨P, _, R, x.2, hR, hP, hx⟩
  obtain ⟨hc, hgo⟩ := liveOK_of_coreClosed hJ x.1 hlive
  exact ⟨hc, hgo, fun K l i v hterm hK ha => lamFree_io_of_coreClosed hJ hR hA hP hx hterm hK ha,
    fun K₀ s K m j w he hK => hk x.1 hlive K₀ s K m j w he hK,
    lamFree_answer_of_coreClosed hJ hR hA hP hx⟩

end Facts

end Targets.Inst

namespace Targets.I
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open Targets.Inst (ourInst J₁ J1DerAt coreClosed_J₁At KeptLamFree)

/-- **Algebraicity at `J₁`, a finaliser's start observed but not its code**, at every effect
context, given that every error a typed program's run keeps holds no λ.  The two sides run step for
step alike (`Inst.algLaw_of_good`); a typed program's runs are closed and go on, answer data and ask
the runner at data (`Inst.algGood_of_coreClosed`). -/
theorem algLaw_J₁_of {Ξ : EffCtx} (hk : KeptLamFree (ℍ := ℍ) orowRF Ξ J₁) :
    (ourInst (ℍ := ℍ) orowRF Ξ J₁).AlgLaw := by
  show (ourInst (ℍ := ℍ) orowRF Ξ (Inst.OurTyping.ofDer (J1DerAt Ξ))).AlgLaw
  exact Inst.algLaw_of_good (fun _ _ _ _ _ hR hA hP hx =>
    Inst.algGood_of_coreClosed (D := J1DerAt Ξ) (coreClosed_J₁At Ξ) hk hR hA hP hx)

end Targets.I

end
