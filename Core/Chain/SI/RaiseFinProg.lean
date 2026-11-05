import Core.Chain.SI.FinPerformN
import Core.Chain.SI.RaiseLendProg

/-!
# The test: a finaliser that performs, on the unwind of a `raise` through a live `mut` lend

    progRaiseC = hnd_E eH (hnd_C cH (
                   (λc. ubind (λ_. dC c, λ_. dC c) (c := 5; raise E ())) (alloc 1)))

    dC c = (λ_. (λ_. ()) (free c)) (close ())        cH: close ↦ λ(v, κ). κ ()

`RaiseLendProg`'s program with the finaliser closing through a capability first: `close` is a
must-resume operation of the row, handled outside the finaliser frame. At `[finalise]` the
`raise`'s resource rides along `dC c`'s stop at `close` (`erwp_ubindRaiseF`), the handler
resumes, the cell is freed, and the `raise` reaches `hnd_E` owning nothing.
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

/-- `close : 1 ↠^lin 1`, resumed under `extF`. -/
def cEnt : OpEntN := ⟨.lin, false, unitP, unitP, none, extF⟩

/-- Under both handlers: `close` and `E`. -/
def TEC : OpTabN := fun m i => if m = 8 ∧ i = 0 then some cEnt else TE m i

theorem TEC_cases {m i : UInt32} {en : OpEntN} (h : TEC m i = some en) :
    (m = 8 ∧ i = 0 ∧ en = cEnt) ∨ (m = 7 ∧ i = 0 ∧ en = eEnt) := by
  unfold TEC at h
  split_ifs at h with h₁
  · exact .inl ⟨h₁.1, h₁.2, (Option.some.inj h).symm⟩
  · exact .inr (TE_cases h)

theorem TEC_ent {m i : UInt32} {en : OpEntN} (h : TEC m i = some en) : en = cEnt ∨ en = eEnt := by
  rcases TEC_cases h with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩
  · exact .inl rfl
  · exact .inr rfl

theorem TEC_down : TEC.Down where
  pa := fun _ _ en h _ _ _ _ hA => by rcases TEC_ent h with rfl | rfl <;> exact hA
  fin := fun _ _ en P h hP => by rcases TEC_ent h with rfl | rfl <;> cases hP
  wcl := fun _ _ en h => by rcases TEC_ent h with rfl | rfl <;> exact extF_left

theorem TEC_lendOKR (A : Life) : TEC.LendOKR A where
  entry := fun _ _ en h ha => by
    rcases TEC_ent h with rfl | rfl
    · exact ⟨rfl, rfl⟩
    · cases ha
  pa := fun _ _ en h _ _ _ ρ hA => by
    rcases TEC_ent h with rfl | rfl <;>
    · obtain ⟨-, rfl⟩ := hA
      exact inStratum_empty A
  pb := fun _ _ en h _ _ _ ρ hB => by
    rcases TEC_ent h with rfl | rfl <;>
    · obtain ⟨-, rfl⟩ := hB
      exact inStratum_empty _

/-- **The borrowed computation at `TEC`.** -/
theorem lendRC_ok (l : Loc) (A : Life) (u : Val) (k : Nat) (ls : List SRec) (BM : WRes)
    (hBM : ResU.CompS PMap.empty (ResU.single l (CellU.mutOf A u PMap.empty (inStratum_empty A)
      (famF A k) rfl)) BM) :
    erwp (ℍ := ℍ) (Φ₀.set l A (famF A)) (opTableN TEC) (MFPost l A (famF A) QF) k ls
      (lendR l) BM := by
  have hΦ' := LocFam.set_down (l := l) Φ₀_down (famF_down A)
  have hFl : Φ₀.set l A (famF A) l = some ⟨A, famF A⟩ := by simp [LocFam.set]
  obtain rfl := eq_of_compS_empty_left hBM
  refine erwp_bindR (K := .seq .hole raiseX) hΦ' (opTableN_local TEC) ?_
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
  refine erwp_det hΦ' (opTableN_down TEC_down) (fun _ _ _ _ h => h)
    (fun μ => step1Only_plug (Head.seq μ _) rfl .hole) ?_
  rw [Kont.plug_hole, erwp_eq]
  exact rwpG_here (final_opPlug (K := .hole) (r := true) (payloadName_opPayload 7 0 Val.unit)
    (by simp [OpFree, Kont.Catches])) (Or.inr (Or.inr ⟨.hole, 7, 0, Val.unit, eEnt,
      pure_sep_mk ⟨rfl, rfl, by simp [TEC, TE], rfl⟩ ⟨PMap.empty, _, compS_empty_left _,
        ⟨⟨rfl, rfl⟩, noOwn_empty⟩, noOwn_single_mut l⟩⟩))

/-- `close ()`. -/
def closeE : Expr := performE (.val (opPayload 8 0 Val.unit))

/-- `λ_. (λ_. (λ_. ()) (free ℓ)) (close ())`. -/
def dC (l : Loc) : Val := Val.lam (.app (.val (dU l)) closeE)

/-- **The finaliser performs `close`, then consumes the claim and answers `()`.** -/
theorem dC_ok (A : Life) (l : Loc) (k : Nat) (ls : List SRec) (ρ : WRes)
    (h : claimR l A (famF A) k ρ) :
    erwp (ℍ := ℍ) Φ₀ (opTableN TEC) (fun _ _ v ρ' => v = Val.unit ∧ ρ' = PMap.empty) k ls
      (.app (.val (dC l)) (.val .unit)) ρ := by
  have hQ : PostN.Down (fun _ _ v ρ' => v = Val.unit ∧ ρ' = PMap.empty) := fun _ _ _ _ h => h
  refine erwp_det Φ₀_down (opTableN_down TEC_down) hQ
    (fun μ => step1Only_plug (Head.beta μ _ Val.unit) rfl .hole) ?_
  have e : Kont.hole.plug (Expr.subst 0 Val.unit (.app (.val (dU l)) closeE)) =
      (Kont.appR (.val (dU l)) .hole).plug (performE (.val (opPayload 8 0 Val.unit))) := by
    simp [Expr.subst, Kont.plug, dU, closeE, freeE, Val.loc, Expr.val, Val.prim, Val.lam,
      Val.unit, performE, opPayload, Val.pair, Val.i32]
  rw [e]
  obtain ⟨w, σ, hσ, hF, hc⟩ := h
  refine erwp_perform (T := TEC) (en := cEnt) (K := .appR (.val (dU l)) .hole)
    rfl (by simp [TEC]) rfl rfl (compS_empty_left _) ⟨rfl, rfl⟩
    (fun ls' _ k' hk' w' σB XB hB hXB => ?_)
  obtain ⟨rfl, rfl⟩ := hB
  obtain rfl := ResU.CompS.functional hXB (ResU.comp_empty_right _)
  exact erwp_of_rwp (dU_ok A l k' ls' _ ⟨w, σ, hσ, hF, hc⟩)

/-- `λc. ubind (dC c, dC c) (c := 5; raise E ())`, its body. -/
def bodyRCF : Expr :=
  .app (.app (.val (.prim .ubind))
    (.pair (.val (Val.lam (.app (.val (Val.lam (.app (.val (Val.lam (.val .unit)))
        (freeE (.var 2))))) closeE)))
      (.val (Val.lam (.app (.val (Val.lam (.app (.val (Val.lam (.val .unit)))
        (freeE (.var 2))))) closeE)))))
    (.seq (.app (.app (.val (.prim .store)) (.var 0)) (.val (Val.i32 5))) raiseX)

/-- `(λc. ubind (dC c, dC c) (c := 5; raise E ())) (alloc 1)`. -/
def bodyRC : Expr :=
  .app (.val (Val.lam bodyRCF)) (.app (.val (.prim .alloc)) (.val (Val.i32 1)))

theorem bodyRCF_subst (l : Loc) :
    Expr.subst 0 (Val.loc l) bodyRCF = ubindE (Val.pair (dC l) (dC l)) (lendR l) := by
  simp [bodyRCF, dC, dU, closeE, ubindE, Expr.subst, Val.pair, Val.lam, Val.loc, freeE,
    Expr.val, Expr.shift, Val.prim, lendR, wrL, raiseX, raiseE, performE, opPayload, Val.storeV,
    Val.i32, Val.unit]

theorem bodyRC_ok (A : Life) (n : Nat) :
    erwp (ℍ := ℍ) Φ₀ (opTableN TEC) QZ n [] bodyRC (PMap.empty : WRes) := by
  have hD := opTableN_down TEC_down
  refine erwp_alloc Φ₀_down (opTableN_local _) (.appR (.val (Val.lam bodyRCF)) .hole) (Val.i32 1)
    (fun l σ₁ σ₂ hcell hc => ?_)
  obtain rfl := eq_of_compS_empty_left hc
  refine erwp_det Φ₀_down hD QZ_down (fun μ => step1Only_plug (Head.beta μ _ _) rfl .hole) ?_
  rw [Kont.plug_hole, bodyRCF_subst]
  refine erwp_ubindRaiseF Φ₀_down TEC_down (fun _ _ en h ha => (TEC_lendOKR A).entry _ _ en h ha)
    (fun _ _ en h => by rcases TEC_ent h with rfl | rfl <;> rfl)
    (fun _ _ en h ha => by
      rcases TEC_cases h with ⟨-, -, rfl⟩ | ⟨rfl, -, -⟩
      · cases ha
      · decide)
    (fun _ _ en h _ _ _ _ _ _ hA => by rcases TEC_ent h with rfl | rfl <;> exact hA)
    (dC l) (dC l) (dC_ok A l) QZ_down (Qin := QF) (fun _ _ _ _ h => h.elim) _ _ _ _ ?_
  subst hcell
  exact erwp_M_frameR (famF_down A) (TEC_lendOKR A) _ _ le_rfl [] (lendR l) (Val.i32 1)
    PMap.empty _ PMap.empty _ (inStratum_empty A) (inStratum_empty _) (famF A _) (fun _ _ h => h)
    rfl (ResU.comp_empty_right _) (ResU.comp_empty_right _) (lendRC_ok l A (Val.i32 1) _ [])

/-- `hnd_C`: `close` resumed at once. -/
def cH : Val := hndVal 8 (qualsVal [.lin]) Stage1.idV (Val.pair (Stage1.resumeCl Val.unit) .unit)

theorem erwp_cH :
    ∀ n ls e ρ, erwp (ℍ := ℍ) Φ₀ (opTableN TEC) QZ n ls e ρ →
      erwp (ℍ := ℍ) Φ₀ (opTableN TE) QZ n ls (hndE cH e) ρ := by
  refine erwp_handle Φ₀_down TEC TE TEC_down TE_down 8
    (fun m i hm => by simp [TEC, hm]) _ _ _ QZ QZ QZ_down ?_ (fun _ => none)
    (fun _ en hT _ hq' _ hTk => by cases hTk)
    (fun k ls v ρ hv => erwp_idV Φ₀_down TE_down hv) ?_
  · intro i en hT _
    rcases TEC_cases hT with ⟨-, rfl, rfl⟩ | ⟨h7, -, -⟩
    · exact Stage1.capTag_one .lin
    · exact absurd h7 (by decide)
  · intro i en hT
    rcases TEC_cases hT with ⟨-, rfl, rfl⟩ | ⟨h7, -, -⟩
    · refine ⟨Stage1.resumeCl Val.unit, Stage1.clauseAt_pair0 _ _, fun _ k ls v κ ρ hsep => ?_,
        fun h => (by cases h)⟩
      obtain ⟨ρa, ρk, hc, ⟨-, rfl⟩, -, hK⟩ := hsep
      obtain rfl : ρ = ρk := eq_of_compS_empty_left hc
      refine erwp_resumeCl Φ₀_down TE_down QZ_down rfl fun k' hk' => ?_
      exact (hK ls (extF_refl ls _) k' hk').1 Val.unit PMap.empty ρ ⟨rfl, rfl⟩
        (ResU.comp_empty_right ρ)
    · exact absurd h7 (by decide)

/-- `hnd_E eH (hnd_C cH bodyRC)`. -/
def progRaiseC : Expr := hndE eH (hndE cH bodyRC)

theorem progRaiseC_ok (n : Nat) :
    erwp (ℍ := ℍ) Φ₀ (opTableN OpTabN.empty) QZ n [] progRaiseC (PMap.empty : WRes) :=
  erwp_eH n [] _ _ (erwp_cH n [] _ _ (bodyRC_ok 0 n))

/-- **The performing-finaliser test.** A cell lent `mut` to a computation that writes and
raises with the borrow live; at `[finalise]` the finaliser performs `close`, which the handler
outside resumes, then frees the cell; the `raise` reaches its handler owning nothing. Every
configuration a run reaches is a value or steps, a value only at the empty memory, and every
`free` finds its cell. -/
theorem progRaiseC_orDiverges : OrDiverges (ℍ := ℍ) progRaiseC :=
  erwp_adequacy (Φ := Φ₀) (fun _ _ _ _ h => h) progRaiseC_ok

end BoCa.Fig16.LogRel.Core.Chain.SI.RaiseLendProg

end
