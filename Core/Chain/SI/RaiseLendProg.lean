import Core.Chain.SI.StopRaiseN

/-!
# The test: an ordinary `raise` under a live `mut` lend, the lender's cell released on the unwind

    progRaise = hnd_E eH ((λc. ubind (λ_. dU c, λ_. dU c) (c := 5; raise E ())) (alloc 1))

    dU c = (λ_. ()) (free c)        eH: E ↦ λ_. ()   (abortive)

The cell is lent `mut` to `c := 5; raise E ()` (`erwp_M_frameR`): the borrow writes and the
`raise` leaves the lend with the borrow live. The lender's `raise` carries the lend's claim; the
finaliser frame's `[finalise]` runs `dU c`, which frees the cell, and the `raise` reaches the
handler owning nothing. `progRaise_orDiverges`.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core.Chain.SI.RaiseLendProg
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel.Core.Chain.SI.LendProg
open BoCa.BoLo (Heap Step1 Steps Head Kont performE raiseE cancelVal opPayload freeE hndE hndVal
  clauseAt capTag ubindE)

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

/-! ### The table -/

/-- `E : 1 ↠ 0`, abortive, carrying `()`. -/
def eEnt : OpEntN := ⟨.lin, true, unitP, unitP, none, extF⟩

/-- Under the handler: `E`. -/
def TE : OpTabN := fun m i => if m = 7 ∧ i = 0 then some eEnt else none

theorem TE_cases {m i : UInt32} {en : OpEntN} (h : TE m i = some en) :
    m = 7 ∧ i = 0 ∧ en = eEnt := by
  unfold TE at h
  split_ifs at h with h₁
  · exact ⟨h₁.1, h₁.2, (Option.some.inj h).symm⟩

theorem TE_down : TE.Down where
  pa := fun _ _ en h _ _ _ _ hA => by obtain ⟨-, -, rfl⟩ := TE_cases h; exact hA
  fin := fun _ _ en P h hP => by rw [(TE_cases h).2.2] at hP; cases hP
  wcl := fun _ _ en h => by rw [(TE_cases h).2.2]; exact extF_left

theorem TE_lendOKR (A : Life) : TE.LendOKR A where
  entry := fun _ _ en h ha => by rw [(TE_cases h).2.2] at ha; cases ha
  pa := fun _ _ en h _ _ _ ρ hA => by
    obtain ⟨-, -, rfl⟩ := TE_cases h
    obtain ⟨-, rfl⟩ := hA
    exact inStratum_empty A
  pb := fun _ _ en h _ _ _ ρ hB => by
    obtain ⟨-, -, rfl⟩ := TE_cases h
    obtain ⟨-, rfl⟩ := hB
    exact inStratum_empty _

/-! ### The lent computation -/

/-- `raise E ()`. -/
def raiseX : Expr := raiseE (.val (opPayload 7 0 Val.unit))

/-- The lent computation: `ℓ := 5; raise E ()`. -/
def lendR (l : Loc) : Expr := .seq (wrL l) raiseX

/-- **The borrowed computation**: the borrow writes (6.66 at the index), and the `raise` stops
with the borrow as garbage. -/
theorem lendR_ok (l : Loc) (A : Life) (u : Val) (k : Nat) (ls : List SRec) (BM : WRes)
    (hBM : ResU.CompS PMap.empty (ResU.single l (CellU.mutOf A u PMap.empty (inStratum_empty A)
      (famF A k) rfl)) BM) :
    erwp (ℍ := ℍ) (Φ₀.set l A (famF A)) (opTableN TE) (MFPost l A (famF A) QF) k ls
      (lendR l) BM := by
  have hΦ' := LocFam.set_down (l := l) Φ₀_down (famF_down A)
  have hFl : Φ₀.set l A (famF A) l = some ⟨A, famF A⟩ := by simp [LocFam.set]
  obtain rfl := eq_of_compS_empty_left hBM
  refine erwp_bindR (K := .seq .hole raiseX) hΦ' (opTableN_local TE) ?_
  refine rwp_M_antiFrame hΦ' hFl (ResU.comp_empty_right _) ?_
  intro W X hW hX
  obtain rfl := eq_of_compS_empty_left hW
  obtain rfl := eq_of_compS_empty_left hX
  refine rwp_store ls l u (Val.i32 5) _ ⟨_, PMap.empty, ResU.comp_empty_right _, rfl, ?_⟩
  intro ρ₁ ρ₂ h₁ hc
  subst h₁
  obtain rfl := eq_of_compS_empty_left hc
  refine ⟨Val.i32 5, PMap.empty, inStratum_empty A, rfl, PMap.empty, PMap.empty,
    ResU.comp_empty_right _, ResU.comp_empty_right _, fun X hX => ?_⟩
  obtain rfl := eq_of_compS_empty_left hX
  refine erwp_det hΦ' (opTableN_down TE_down) (fun _ _ _ _ h => h)
    (fun μ => step1Only_plug (Head.seq μ _) rfl .hole) ?_
  rw [Kont.plug_hole, erwp_eq]
  exact rwpG_here (final_opPlug (K := .hole) (r := true) (payloadName_opPayload 7 0 Val.unit)
    (by simp [OpFree, Kont.Catches])) (Or.inr (Or.inr ⟨.hole, 7, 0, Val.unit, eEnt,
      pure_sep_mk ⟨rfl, rfl, by simp [TE], rfl⟩ ⟨PMap.empty, _, compS_empty_left _,
        ⟨⟨rfl, rfl⟩, noOwn_empty⟩, noOwn_single_mut l⟩⟩))

/-! ### The finaliser -/

/-- `λ_. (λ_. ()) (free ℓ)`. -/
def dU (l : Loc) : Val :=
  Val.lam (.app (.val (Val.lam (.val .unit))) (freeE (.val (Val.loc l))))

/-- **The finaliser consumes the claim and answers `()`.** -/
theorem dU_ok (A : Life) (l : Loc) (k : Nat) (ls : List SRec) (ρ : WRes)
    (h : claimR l A (famF A) k ρ) :
    rwp (ℍ := ℍ) Φ₀ (fun _ _ v ρ' => v = Val.unit ∧ ρ' = PMap.empty) k ls
      (.app (.val (dU l)) (.val .unit)) ρ := by
  obtain ⟨w, σ, hσ, hF, hc⟩ := h
  have hσ0 : σ = PMap.empty := hF
  subst hσ0
  obtain rfl := ResU.CompS.functional hc (ResU.comp_empty_right _)
  have hQD : PostG.Down (valPostN (fun _ _ v ρ' => v = Val.unit ∧ ρ' = PMap.empty)) :=
    fun _ _ _ _ ⟨v, hv, hq⟩ => ⟨v, hv, hq⟩
  rw [rwp_iff_rwpG]
  refine rwpG_det Φ₀_down hQD (fun μ => step1Only_plug (Head.beta μ _ Val.unit) rfl .hole) ?_
  have e : Kont.hole.plug (Expr.subst 0 Val.unit
      (.app (.val (Val.lam (.val .unit))) (freeE (.val (Val.loc l))))) =
      (Kont.appR (.val (Val.lam (.val .unit))) .hole).plug
        (.app (.val (.prim .free)) (.val (.loc l))) := by
    simp [Expr.subst, Kont.plug, freeE, Val.loc, Expr.val, Val.prim, Val.lam, Val.unit]
  rw [e, ← rwp_iff_rwpG]
  refine rwp_bind Φ₀_down _ (rwp_free ls l w _ ⟨_, PMap.empty, ResU.comp_empty_right _, rfl, ?_⟩)
  rw [rwp_iff_rwpG]
  refine rwpG_det Φ₀_down hQD (fun μ => step1Only_plug (Head.beta μ _ w) rfl .hole) ?_
  have e₂ : Kont.hole.plug (Expr.subst 0 w (.val Val.unit)) = (Val.unit).1 := by
    simp [Expr.subst, Kont.plug, Val.unit]
  rw [e₂, ← rwp_iff_rwpG]
  exact rwp_val ⟨rfl, rfl⟩

/-! ### The body and the program -/

/-- `λc. ubind (dU c, dU c) (c := 5; raise E ())`, its body. -/
def bodyRF : Expr :=
  .app (.app (.val (.prim .ubind))
    (.pair (.val (Val.lam (.app (.val (Val.lam (.val .unit))) (freeE (.var 1)))))
      (.val (Val.lam (.app (.val (Val.lam (.val .unit))) (freeE (.var 1)))))))
    (.seq (.app (.app (.val (.prim .store)) (.var 0)) (.val (Val.i32 5))) raiseX)

/-- `(λc. ubind (dU c, dU c) (c := 5; raise E ())) (alloc 1)`. -/
def bodyR : Expr :=
  .app (.val (Val.lam bodyRF)) (.app (.val (.prim .alloc)) (.val (Val.i32 1)))

theorem bodyRF_subst (l : Loc) :
    Expr.subst 0 (Val.loc l) bodyRF = ubindE (Val.pair (dU l) (dU l)) (lendR l) := by
  simp [bodyRF, dU, ubindE, Expr.subst, Val.pair, Val.lam, Val.loc, freeE, Expr.val,
    Expr.shift, Val.prim, lendR, wrL, raiseX, raiseE, opPayload, Val.storeV, Val.i32, Val.unit]

theorem bodyR_ok (A : Life) (n : Nat) :
    erwp (ℍ := ℍ) Φ₀ (opTableN TE) QZ n [] bodyR (PMap.empty : WRes) := by
  have hD := opTableN_down TE_down
  refine erwp_alloc Φ₀_down (opTableN_local _) (.appR (.val (Val.lam bodyRF)) .hole) (Val.i32 1)
    (fun l σ₁ σ₂ hcell hc => ?_)
  obtain rfl := eq_of_compS_empty_left hc
  refine erwp_det Φ₀_down hD QZ_down (fun μ => step1Only_plug (Head.beta μ _ _) rfl .hole) ?_
  rw [Kont.plug_hole, bodyRF_subst]
  refine erwp_ubindRaise Φ₀_down TE_down
    (fun _ _ en h ha => by rw [(TE_cases h).2.2] at ha; cases ha)
    (fun _ _ en h _ => by rw [(TE_cases h).1]; decide)
    (fun _ _ en h _ _ _ _ _ _ hA => by obtain ⟨-, -, rfl⟩ := TE_cases h; exact hA)
    (dU l) (dU l) (dU_ok A l) QZ_down (Qin := QF) (fun _ _ _ _ h => h.elim) _ _ _ _ ?_
  subst hcell
  exact erwp_M_frameR (famF_down A) (TE_lendOKR A) _ _ le_rfl [] (lendR l) (Val.i32 1)
    PMap.empty _ PMap.empty _ (inStratum_empty A) (inStratum_empty _) (famF A _) (fun _ _ h => h)
    rfl (ResU.comp_empty_right _) (ResU.comp_empty_right _) (lendR_ok l A (Val.i32 1) _ [])

/-- The abortive clause `λ_. ()`. -/
def clE : Val := Val.lam (.val .unit)

/-- `hnd_E`. -/
def eH : Val := hndVal 7 (qualsVal [.lin]) FileProg.idV (Val.pair clE .unit)

theorem erwp_eH :
    ∀ n ls e ρ, erwp (ℍ := ℍ) Φ₀ (opTableN TE) QZ n ls e ρ →
      erwp (ℍ := ℍ) Φ₀ (opTableN OpTabN.empty) QZ n ls (hndE eH e) ρ := by
  refine erwp_handle Φ₀_down TE OpTabN.empty TE_down empty_down 7
    (fun m i hm => by simp [TE, OpTabN.empty, hm]) _ _ _ QZ QZ QZ_down ?_
    (fun _ => none) ?_ (fun k ls v ρ hv => erwp_idV Φ₀_down empty_down hv) ?_
  · intro i en hT ha
    rw [(TE_cases hT).2.2] at ha; cases ha
  · intro i en hT ha
    rw [(TE_cases hT).2.2] at ha; cases ha
  · intro i en hT
    obtain ⟨-, rfl, rfl⟩ := TE_cases hT
    refine ⟨clE, FileProg.clauseAt_pair0 _ _, fun h => (by cases h), fun _ k ls v ρ hv => ?_⟩
    obtain ⟨rfl, rfl⟩ := hv
    refine erwp_det Φ₀_down (opTableN_down empty_down) QZ_down
      (fun μ => step1Only_plug (Head.beta μ _ Val.unit) rfl .hole) ?_
    have e : Kont.hole.plug (Expr.subst 0 Val.unit (.val Val.unit)) = (Val.unit).1 := by
      simp [Expr.subst, Kont.plug, Val.unit]
    rw [e]
    exact erwp_val rfl

/-- `hnd_E eH bodyR`. -/
def progRaise : Expr := hndE eH bodyR

theorem progRaise_ok (n : Nat) :
    erwp (ℍ := ℍ) Φ₀ (opTableN OpTabN.empty) QZ n [] progRaise (PMap.empty : WRes) :=
  erwp_eH n [] _ _ (bodyR_ok 0 n)

/-- **The `raise` test.** A cell lent `mut` to a computation that writes and raises with the
borrow live; the `raise` unwinds through the lend to the finaliser frame, whose finaliser takes
the lend's claim and frees the cell, and the handler answers `()`. Every configuration a run
reaches is a value or steps, a value only at the empty memory, and every `free` finds its
cell. -/
theorem progRaise_orDiverges : OrDiverges (ℍ := ℍ) progRaise :=
  erwp_adequacy (Φ := Φ₀) (fun _ _ _ _ h => h) progRaise_ok

end BoCa.Fig16.LogRel.Core.Chain.SI.RaiseLendProg

end
