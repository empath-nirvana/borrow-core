import Targets.I.J1
import Targets.Instance.Theories

/-!
# The interaction — the answering class at `J₁`: the laws of handling and the theory of state

`J₁`'s reached configurations are closed (`LiveOK`, from Core's relation and B2's runs,
`liveOK_J₁`), and its typed closed values are closed (`closed_of_derV_J₁`).  So the
Instance's results at the answering class hold at `J₁`, at every effect context:

* **D1.h4** (`state_correct_J₁`): the state-passing handler of `stateCo` is a model of global
  state's four laws, by the comodel reduction (`ansCorrect_of_comodel`);
* **D1.h1 at the answering class** (`tailLaw_quiet_J₁`, `algLaw_quiet_J₁`): the tail-resumptive
  law and algebraicity hold at every configuration a typed program reaches, for an operation whose
  clause is tail-resumptive with code that runs quietly.

`[Core σ=[]]`
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets.I
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Kont)
open Targets.Inst (OVal OVTy ourInst J₁ J1Der Quiet)

variable {Ξ : EffCtx}

/-- **The handler of global state is correct at `J₁`** (D1.h4 (b), (c)), at every effect context,
carrier and label. -/
theorem state_correct_J₁ (T : OVTy) (l : (orowAlg Ξ).Lab) :
    (ourInst (ℍ := ℍ) orowRF Ξ J₁).AnsCorrect ((ourInst (ℍ := ℍ) orowRF Ξ J₁).stateTheory T) l
      (ourInst (ℍ := ℍ) orowRF Ξ J₁).stateCo T :=
  Inst.state_correct liveOK_J₁ Inst.closed_of_derV_J₁ T l

/-- **The tail-resumptive law at the answering class, at `J₁`.** -/
theorem tailLaw_quiet_J₁ {l : (orowAlg Ξ).Lab} {r : OVal} {cs : List OVal} {K : Kont} {i : ℕ}
    {v c : OVal} {w : Val} (hi : i < 2 ^ 32)
    (hK : (ourInst (ℍ := ℍ) orowRF Ξ J₁).catches K l = false)
    (hci : cs[i]? = some ((ourInst (ℍ := ℍ) orowRF Ξ J₁).tailCl c)) (hc : closedAt 0 c.1 = true)
    (hq : Quiet (ℍ := ℍ) (.app c.1 v.1) (.val w)) :
    (ourInst (ℍ := ℍ) orowRF Ξ J₁).RunsAlike
      ((ourInst (ℍ := ℍ) orowRF Ξ J₁).handle l ((ourInst (ℍ := ℍ) orowRF Ξ J₁).hnd r cs)
        ((ourInst (ℍ := ℍ) orowRF Ξ J₁).plug K ((ourInst (ℍ := ℍ) orowRF Ξ J₁).perform l i v)))
      ((ourInst (ℍ := ℍ) orowRF Ξ J₁).handle l ((ourInst (ℍ := ℍ) orowRF Ξ J₁).hnd r cs)
        ((ourInst (ℍ := ℍ) orowRF Ξ J₁).plug K
          ((ourInst (ℍ := ℍ) orowRF Ξ J₁).app ((ourInst (ℍ := ℍ) orowRF Ξ J₁).force c) v))) :=
  Inst.tailLaw_quiet liveOK_J₁ hi hK hci hc hq

/-- **Algebraicity at the answering class, at `J₁`.** -/
theorem algLaw_quiet_J₁ {l : (orowAlg Ξ).Lab} {r : OVal} {cs : List OVal} {K : Kont} {i : ℕ}
    {v c : OVal} {w : Val} {M N : Expr} (hi : i < 2 ^ 32)
    (hK : (ourInst (ℍ := ℍ) orowRF Ξ J₁).catches K l = false)
    (hci : cs[i]? = some ((ourInst (ℍ := ℍ) orowRF Ξ J₁).tailCl c)) (hc : closedAt 0 c.1 = true)
    (hq : Quiet (ℍ := ℍ) (.app c.1 v.1) (.val w)) :
    (ourInst (ℍ := ℍ) orowRF Ξ J₁).RunsAlike
      ((ourInst (ℍ := ℍ) orowRF Ξ J₁).handle l ((ourInst (ℍ := ℍ) orowRF Ξ J₁).hnd r cs)
        ((ourInst (ℍ := ℍ) orowRF Ξ J₁).plug K ((ourInst (ℍ := ℍ) orowRF Ξ J₁).bind
          ((ourInst (ℍ := ℍ) orowRF Ξ J₁).bind ((ourInst (ℍ := ℍ) orowRF Ξ J₁).perform l i v) M) N)))
      ((ourInst (ℍ := ℍ) orowRF Ξ J₁).handle l ((ourInst (ℍ := ℍ) orowRF Ξ J₁).hnd r cs)
        ((ourInst (ℍ := ℍ) orowRF Ξ J₁).plug K ((ourInst (ℍ := ℍ) orowRF Ξ J₁).bind
          ((ourInst (ℍ := ℍ) orowRF Ξ J₁).perform l i v) ((ourInst (ℍ := ℍ) orowRF Ξ J₁).bind M N)))) :=
  Inst.algLaw_quiet liveOK_J₁ hi hK hci hc hq

end Targets.I

end
