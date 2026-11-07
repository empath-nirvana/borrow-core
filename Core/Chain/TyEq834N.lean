import Core.Chain.Iface834N
import Core.RelMu
import Core.ShapeMu

/-!
# The relation reads a type only up to `TyEq`  `[spec §62]`

`docs/new-core/scope-831-interface.md` §2, unit L2 (V1): Core's `vC_tyEq`/`cC_tyEq`
(`Core/RelationFacts.lean`, `vCE_tyEq`/`cC_tyEq_aux`) at the chain, by the same induction on the
type, under type-variable environments related by Core's `EnvEq` (`EnvEqN`). `Imm`'s witness
is closed under `TyEq` by Core's `CohE.tyEq`; `⊸`, `U` read `forceE` alike (`forceE_of_cTyEq`); an
effect row's entries read `B.isZero` alike (`TyEq.isZero_eq`, `capB_congr`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel (LtLife substAll)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- `ImmWitW` is closed under `TyEq` (Core's `CohE.tyEq` at the witness). -/
theorem immWitW_tyEq {A A' : VTy} {δ δ' : LSub} (h : TyEq A δ A' δ') (I : List SRec) (l : Loc)
    (s : LSet) : ImmWitW I l s A δ = ImmWitW I l s A' δ' := by
  unfold ImmWitW
  apply propext
  constructor
  · rintro ⟨x, hx, hs, d, hd, hc⟩; exact ⟨x, hx, hs, d, hd, hc.tyEq h.symm⟩
  · rintro ⟨x, hx, hs, d, hd, hc⟩; exact ⟨x, hx, hs, d, hd, hc.tyEq h⟩

/-- Two environments hold the same candidates at types `TyEq` at `δ` and `δ'` (Core's `EnvEq`). -/
def EnvEqN (η η' : Option (Nat → TEntN)) (δ δ' : LSub) : Prop :=
  ∀ n, (tEnvN η n).P = (tEnvN η' n).P ∧ TyEq (tEnvN η n).ty δ (tEnvN η' n).ty δ'

theorem envEqN_none (δ δ' : LSub) : EnvEqN none none δ δ' := fun n => ⟨rfl, show n = n from rfl⟩

theorem envEqN_tClose {η η' : Option (Nat → TEntN)} {δ δ' : LSub} (hη : EnvEqN η η' δ δ')
    {A A' : VTy} (h : TyEq A δ A' δ') : TyEq (tCloseN η A) δ (tCloseN η' A') δ' := by
  rw [tCloseN_eq, tCloseN_eq]
  exact TyEq.subst A _ _ h (fun n => (hη n).2)

/-- `ν`'s one-entry environments at `TyEq` closed types are related. -/
theorem envEqN_nu {T T' : VTy} {P : LocTy → Nat → Val → WRes → Prop} {δ δ' : LSub}
    (hT : TyEq T δ T' δ') : EnvEqN (nuEnvN T P) (nuEnvN T' P) δ δ' := fun n => by
  cases n with
  | zero => exact ⟨rfl, hT⟩
  | succ n => exact ⟨rfl, show n = n from rfl⟩

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
