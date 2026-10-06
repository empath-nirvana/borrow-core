import Targets.Statements.EndState
import Targets.Statements.Linearity

/-!
# Targets — the corollaries of done (DESIGN §1.0)

* `typedSound_of_soundness`: T1 gives `TypedSound` at every program the typing system closes at a
  data answer.
* `i2Prog_of_endState : EndStateAt J M Adm RF → I2Prog J`, from `AcceptsTier2` and `Soundness`.
* `i1Prog_of_endState : EndStateAt J M Adm RF → I1Prog J`, from `ExtendsNU` (through
  `tier1NU`'s derivation of `storeCancel`, `d_storeCancelNU`), `AcceptsTier2` and `Soundness`.
* `p8a_of_endState : EndStateAt J M Adm RF → P8a J`, the conjunct `ReleasedOnceAll`.

Generic: each holds at every typing system and world.  `d_storeCancelNU` is Core's
`d_storeCancel` (`Core/EffPrograms.lean`) with the premise `Row.NU [suspSig]` at its four effect
rules: `susp` is affine.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.EffPrograms
open BoCa.Lifetime (LifeCtx)
open BoCa.Programs (alloc' free')

/-- T1 gives `TypedSound` at a program closed at a data answer. -/
theorem typedSound_of_soundness {J : TypingJ} {e : Expr} {A : VTy}
    (hS : Soundness (ℍ := ℍ) J) (hA : A.Data) (h : J.closed e (.ret A)) :
    TypedSound (ℍ := ℍ) J e A :=
  ⟨h, fun P hP => (hS P hP).1 [] A e hA (fun _ _ _ h => by simp [Row.find] at h) h⟩

/-- **I2 at the program level**, from done. -/
theorem i2Prog_of_endState {J : TypingJ} {M : SemWorld} {Adm : OpAdm} {RF : RowForm}
    (h : EndStateAt (ℍ := ℍ) J M Adm RF) : I2Prog (ℍ := ℍ) J := by
  obtain ⟨-, -, -, -, ⟨h02, h04, h12, -⟩, -, ⟨-, -, hS, -⟩⟩ := h
  have hF : VTy.Data Flag := .sum (.unit 0) (.unit 0)
  exact ⟨typedSound_of_soundness hS hF h02, typedSound_of_soundness hS (.tensor hF hF) h04,
    typedSound_of_soundness hS hF h12⟩

/-! ### `storeCancel` in the unr-free fragment -/

theorem nu_susp : Row.NU [suspSig] := by
  intro n i o h
  simp only [Row.find, List.find?_cons, List.find?_nil] at h
  split at h
  · cases h; right; decide
  · cases h

theorem d_performerNU : CDerivesNU LifeCtx.empty [⟨retTy [] .unit .unit, false⟩,
    ⟨clausesTy [] .unit Es, false⟩] performer (.comp (CTy.effOf [suspSig] .unit)) := by
  have hΓ : Ctx.Dead ([⟨retTy [] .unit .unit, false⟩, ⟨clausesTy [] .unit Es, false⟩] : Ctx VTy) :=
    .cons (.cons .nil)
  refine .bind (A := .ref Flag) (deadSplit hΓ)
    (.ret (.lolliE (deadSplit hΓ) (.sumI₁ (.unitI hΓ.toP)) (.alloc hΓ.toP))) ?_
  have hΓ₁ : Ctx.Dead ((⟨.ref Flag, false⟩ : Slot VTy) :: _) := .cons hΓ
  have hΓ₂ : Ctx.Dead ((⟨.unit, false⟩ : Slot VTy) :: ⟨.ref Flag, false⟩ :: _) := .cons hΓ₁
  -- `drop (free r)` with `r` at index 1, under a dead slot at index 0
  have hdrop : CDerivesNU LifeCtx.empty (⟨.unit, false⟩ :: ⟨.ref Flag, true⟩ ::
      [⟨retTy [] .unit .unit, false⟩, ⟨clausesTy [] .unit Es, false⟩])
      (dropB (.app free' (.var 1))) (.val .unit) :=
    .ofRet (.sumE (.dead (.left (deadSplit hΓ)))
      (.lolliE (.dead (.left (deadSplit hΓ))) (.var (.there (.here hΓ.toP))) (.free hΓ₂.toP))
      (.ret (.var (.here hΓ₂.toP))) (.ret (.var (.here hΓ₂.toP))))
  refine .effThen (A := .unit) nu_susp (.right (deadSplit hΓ)) (by simp [Row.NZ, suspSig])
    (by simp [Row.Uniq]) (fun h => absurd h susp_not_unr)
    (.effPerform (o := suspSig) nu_susp rfl rfl (.unitI hΓ₁.toP)) ?_ ?_
  · refine .unitE (.right (.left (deadSplit hΓ))) hdrop ?_
    exact .effSub (S := []) nu_susp (fun _ _ _ h => by simp [Row.find] at h)
      (.ret (.var (.here hΓ₁.toP)))
  · show CDerivesNU _ _ _ (.comp (.ret .unit))
    exact .ret hdrop

theorem d_hrSNU : CDerivesNU LifeCtx.empty [⟨clausesTy [] .unit Es, false⟩] hrS
    (.val (retTy [] .unit .unit)) :=
  .bangThunkV (persistent_dead (.cons .nil)) rfl (.lam (.ret (.var (.here (.cons .nil)))))

theorem d_clSNU : CDerivesNU LifeCtx.empty [] clS (.val (clauseTy [] .unit (.aff, .unit, .unit))) := by
  refine .bangThunkV (persistent_dead .nil) rfl (.lam ?_)
  refine .tensorE (.left .nil) (.var (.here .nil)) ?_
  refine .unitE (.right (.left (.dead .nil))) (.var (.there (.here (.cons .nil)))) ?_
  refine .bind (.left (.dead (.dead .nil)))
    (.ret (.lolliE (.left (.dead (.dead .nil))) (.var (.here (.cons (.cons .nil))))
      (.alloc (.cons (.cons (.cons .nil)))))) ?_
  refine .bind (.left (.dead (.dead (.dead .nil))))
    (.ret (.lolliE (.left (.dead (.dead (.dead .nil)))) (.var (.here (.cons (.cons (.cons .nil)))))
      (.free (.cons (.cons (.cons (.cons .nil))))))) ?_
  exact .proj₂ (.force (C := .amp (.arr .unit (CTy.effOf [] .unit)) (CTy.effOf [] .unit))
    (.here (.cons (.cons (.cons (.cons .nil))))))

/-- **`storeCancel` is typed by the unr-free fragment of tier 1.** -/
theorem d_storeCancelNU : CDerivesNU LifeCtx.empty [] storeCancel (.comp (.ret .unit)) := by
  refine .bind .nil (.ret (.tensorI .nil d_clSNU (.unitI .nil))) ?_
  refine .bind (.right .nil) (.ret d_hrSNU) ?_
  exact .effHandle (S := []) (E := Es) (n := 4) (A := .unit) (R := .unit) nu_susp
    (.left (.left .nil)) (.left (.right .nil)) (.here (.cons .nil)) (.there (.here .nil))
    (by decide) (by simp) (by simp) d_performerNU

/-- **I1 at the program level**, from done. -/
theorem i1Prog_of_endState {J : TypingJ} {M : SemWorld} {Adm : OpAdm} {RF : RowForm}
    (h : EndStateAt (ℍ := ℍ) J M Adm RF) : I1Prog (ℍ := ℍ) J := by
  obtain ⟨-, -, -, -, ⟨-, -, -, h17⟩, -, ⟨⟨hsub, -⟩, -, hS, -⟩⟩ := h
  have hF : VTy.Data Flag := .sum (.unit 0) (.unit 0)
  have hsc : J.closed storeCancel (.ret .unit) :=
    hsub [] LifeCtx.empty (fun _ => []) storeCancel (fun _ => .comp (.ret .unit))
      (fun _ _ => d_storeCancelNU)
  exact ⟨typedSound_of_soundness hS (.unit 0) hsc, typedSound_of_soundness hS hF h17⟩

/-- **P8.a**, from done: the conjunct `ReleasedOnceAll`. -/
theorem p8a_of_endState {J : TypingJ} {M : SemWorld} {Adm : OpAdm} {RF : RowForm}
    (h : EndStateAt (ℍ := ℍ) J M Adm RF) : P8a (ℍ := ℍ) J := by
  obtain ⟨-, -, -, -, -, -, ⟨-, -, -, -, hR, -⟩⟩ := h
  exact hR

end Targets

end
