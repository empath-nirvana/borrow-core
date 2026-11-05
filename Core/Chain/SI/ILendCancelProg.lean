import Core.Chain.SI.IStopCancelN
import Core.Chain.SI.ILendProg
import Core.Chain.SI.LendCancelProg

/-!
# The test, the cancel case: an `imm` lend live across a `yield` whose `κ` the scheduler cancels

    progILendCancel = hnd_Div rtH (
                      hnd_Y yCancel (                       -- y : 1 ↠^cancel 1; κ stored, cancelled
                        (λc. ubind (λ_. free c, λ_. free c) (iterate (fI, c))) (alloc ())))

Each turn lends the cell `imm` to `y (); !s` (`erwp_I_frameC`). The scheduler stores the first
`y`'s `κ`, takes it back and cancels it: the cancel run unwinds through the lend (the lender's
cancel run ends carrying the lend's claim `ℓ ↦ own(()) ● ∅`, `claimI`) to the finaliser frame,
whose `D = λ_. free c` consumes the claim (`erwp_ubindClaim`). `progILendCancel_orDiverges`.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core.Chain.SI.ILendProg
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel.Core.Chain.SI.LendProg
open BoCa.BoLo (Heap Step1 Steps Head Kont performE raiseE cancelVal opPayload freeE hndE hndVal
  clauseAt capTag ubindE)
open BoCa.Lifetime (LSub)

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

theorem T2C_ilendOKC (A : Life) : (T2C (ℍ := ℍ)).ILendOKC A where
  entry := (T2C_lendOKC A).entry
  pa := fun _ _ en h _ _ _ ρ hA => by
    rcases T2C_ent h with rfl | rfl <;>
    · obtain ⟨-, rfl⟩ := hA
      exact inStratum_empty A
  pb := fun _ _ en h _ _ _ ρ hB => by
    rcases T2C_ent h with rfl | rfl <;>
    · obtain ⟨-, rfl⟩ := hB
      exact inStratum_empty A
  paExt := fun _ _ en h _ _ _ _ _ _ hA => by rcases T2C_ent h with rfl | rfl <;> exact hA
  pbExt := fun _ _ en h _ _ _ _ _ _ hB => by rcases T2C_ent h with rfl | rfl <;> exact hB

theorem empty_ilendOK (A : Life) : OpTabN.empty.ILendOK A where
  entry := fun _ _ _ h => by cases h
  pa := fun _ _ _ h => by cases h
  pb := fun _ _ _ h => by cases h
  paExt := fun _ _ _ h => by cases h
  pbExt := fun _ _ _ h => by cases h

/-- The body's table: `T2C` with the `imm` lend's claim at `ℓ`. -/
abbrev T2I (l : Loc) : OpTabN :=
  @OpTabN.claimT ℍ _ (T2C (ℍ := ℍ)) Φ₀ OpTabN.empty (claimI l Val.unit PMap.empty)

theorem T2I_down (l : Loc) : (T2I (ℍ := ℍ) l).Down where
  pa := fun _ _ en' h _ _ _ _ hA => by
    obtain ⟨en, hT, rfl⟩ := claimT_some h
    by_cases hq : en.q = .cancel
    · rw [if_pos hq] at hA ⊢; exact T2C_down.pa _ _ en hT _ _ _ _ hA
    · rw [if_neg hq] at hA ⊢; exact T2C_down.pa _ _ en hT _ _ _ _ hA
  fin := fun _ _ en' P h hP => by
    obtain ⟨en, hT, rfl⟩ := claimT_some h
    by_cases hq : en.q = .cancel
    · rw [if_pos hq] at hP
      cases hP
      exact fun k ls e ρ hk => erwp_le Φ₀_down (cancelTabR_local _ _)
        (cancelTabR_down empty_down (fun _ _ h => h)) falsePost_down (Nat.le_succ _) hk
    · rw [if_neg hq] at hP; exact T2C_down.fin _ _ en _ hT hP
  wcl := fun _ _ en' h => by
    obtain ⟨en, hT, rfl⟩ := claimT_some h
    by_cases hq : en.q = .cancel
    · rw [if_pos hq]; exact T2C_down.wcl _ _ en hT
    · rw [if_neg hq]; exact T2C_down.wcl _ _ en hT

/-- **The borrowed computation, `y` cancellable**: its cancel run is the `raise` at once, the
borrow garbage. -/
theorem lendI_okC (l : Loc) (A : Life) (k : Nat) (ls : List SRec) (BI : WRes)
    (hBI : ResU.CompS PMap.empty (ResU.single l (CellU.immOf (LSet.singleton A) Val.unit
      PMap.empty (inStratum_empty A))) BI) :
    erwp (ℍ := ℍ) Φ₀ (opTableN (T2C (ℍ := ℍ))) (IFPost l Val.unit PU A (Qown l)) k ls
      (lendIE l) BI := by
  obtain rfl := eq_of_compS_empty_left hBI
  have hKH : ∀ m, (Kont.seq .hole (ldL l)).HasHnd m = false := fun m => by simp [Kont.HasHnd]
  have hKC : ∀ m, (Kont.seq .hole (ldL l)).Catches m = false := fun m => by simp [Kont.Catches]
  refine erwp_performG (T := T2C) (en := yCEnt) (K := .seq .hole (ldL l)) (hKH 6)
    (by simp [T2C]) rfl (compS_empty_left _) ⟨rfl, rfl⟩ (fun h => by cases h)
    (fun ls' _ k' hk' w σB XB hB hXB => ?_) (fun ls' _ _ P hP => ?_)
  · obtain ⟨rfl, rfl⟩ := hB
    obtain rfl := ResU.CompS.functional hXB (ResU.comp_empty_right _)
    cases k' with
    | zero => exact erwp_zero
    | succ k₀ =>
    refine erwp_step (opTableN_local _) (fun μ => step1Only_plug (Head.seq μ _) rfl .hole) ?_
    refine erwp_of_rwp (rwp_dump (rwp_load_I ls' l A (fun w _ => w = Val.unit) _ ⟨_, PMap.empty,
      ResU.comp_empty_right _, ⟨LSet.singleton A, Val.unit, PMap.empty, inStratum_empty A, rfl,
        rfl, le_refl _⟩, fun w ρc X hc hX => ?_⟩))
    obtain rfl := eq_of_compS_empty_left hX
    obtain ⟨s, u', σ, hs, rfl, ⟨-, -, -, -, hw⟩, -⟩ := hc
    refine ⟨noOwn_single_imm l _ _ _ _, fun ρl Y hl hY ρv Z hv hZ => ?_, inStratum_empty A⟩
    subst hl
    obtain rfl := eq_of_compS_empty_left hY
    have hv' : ρv = PMap.empty := hv
    subst hv'
    obtain rfl := ResU.CompS.functional hZ (ResU.comp_empty_right _)
    exact ⟨hw, rfl⟩
  · -- the cancel run: `raise cancel` under the plain context, the borrow garbage
    cases hP
    show erwp (ℍ := ℍ) Φ₀ (cancelTabN OpTabN.empty) (fun _ _ _ _ => False) k ls' _ _
    rw [dead_plain _ hKH (hKC 0), erwp_eq]
    exact rwpG_here (final_opPlug (r := true) (payloadName_cancelVal none) (hKC 0))
      (Or.inr (Or.inl ⟨_, none, pure_sep_mk ⟨rfl, hKC 0⟩
        ⟨PMap.empty, _, compS_empty_left _, emp_empty, noOwn_single_imm l _ _ _ _⟩⟩))

/-- The loop's invariant over a fixed cell holding `()`. -/
def ILu (l : Loc) : Val → WProp := fun s ρ => s = Val.loc l ∧ ptoOwn l Val.unit ρ

theorem T2I_ctxClosed (l : Loc) (K : Kont) (hH : ∀ m, K.HasHnd m = false)
    (hC : ∀ m, K.Catches m = false) : (T2I (ℍ := ℍ) l).CtxClosed K :=
  claimT_ctxClosed Φ₀_down K hH hC T2C_finNone (empty_ctxClosed K)

/-- **A turn, `y` cancellable**: the lend by `erwp_I_frameC` at a lifetime below the list's
records. -/
theorem turnI_okC (l : Loc) (k : Nat) (s : Val) (ls : List SRec) (ρ : WRes) (hI : ILu l s ρ) :
    erwp (ℍ := ℍ) Φ₀ (opTableN (T2I (ℍ := ℍ) l)) (turnPostN (ILu l) QF) k ls
      (.app (.app (.val fI) (.val s)) (.val nextV)) ρ := by
  obtain ⟨rfl, rfl⟩ := hI
  have hD := opTableN_down (T2I_down (ℍ := ℍ) l)
  have hTP : (turnPostN (ILu l) QF).Down := fun _ _ _ _ h => by
    rcases h with ⟨x, hx, hq⟩ | h
    · exact .inl ⟨x, hx, hq⟩
    · exact .inr h
  refine erwp_det Φ₀_down hD hTP
    (fun μ => step1Only_plug (Head.beta μ _ (Val.loc l)) rfl (.appL .hole nextV)) ?_
  have e₁ : (Kont.appL .hole nextV).plug (Expr.subst 0 (Val.loc l)
      (.lam (.case (.var 0) (.seq (.seq FileProg.yE (.app (.val (.prim .load)) (.var 2)))
        (.inj₂ (.var 2))) (.val .unit)))) =
      Kont.hole.plug (.app (.val (Val.lam (.case (.var 0)
        (.seq (.seq FileProg.yE (ldL l)) (.inj₂ (.val (Val.loc l)))) (.val .unit)))) (.val nextV)) := by
    simp [Expr.subst, Expr.shift, Kont.plug, FileProg.yE, ldL, performE, opPayload, Val.pair,
      Val.i32, Val.unit, Val.lam, Val.loc, Expr.val, Val.prim, Val.shift]
  rw [e₁]
  refine erwp_det Φ₀_down hD hTP (fun μ => step1Only_plug (Head.beta μ _ nextV) rfl .hole) ?_
  have e₂ : Kont.hole.plug (Expr.subst 0 nextV (.case (.var 0)
        (.seq (.seq FileProg.yE (ldL l)) (.inj₂ (.val (Val.loc l)))) (.val .unit))) =
      Kont.hole.plug (.case (.val (Val.inj₁ Val.unit))
        (.seq (.seq FileProg.yE (ldL l)) (.inj₂ (.val (Val.loc l)))) (.val .unit)) := by
    simp [Expr.subst, Kont.plug, FileProg.yE, ldL, performE, opPayload, Val.pair, Val.i32,
      Val.unit, nextV, Val.inj₁, Val.loc, Expr.val, Val.prim]
  rw [e₂]
  refine erwp_det Φ₀_down hD hTP
    (fun μ => step1Only_plug (Head.case₁ μ Val.unit _ _) rfl .hole) ?_
  have e₃ : Kont.hole.plug (Expr.subst 0 Val.unit
        (.seq (.seq FileProg.yE (ldL l)) (.inj₂ (.val (Val.loc l))))) =
      (Kont.seq .hole (.inj₂ (.val (Val.loc l)))).plug (lendIE l) := by
    simp [Expr.subst, Kont.plug, FileProg.yE, ldL, lendIE, performE, opPayload, Val.pair, Val.i32,
      Val.unit, Val.loc, Expr.val, Val.prim]
  rw [e₃]
  refine erwp_bind_le (Q' := Qown l) Φ₀_down _ (fun m => by simp [Kont.HasHnd])
    (fun m => by simp [Kont.Catches])
    (T2I_ctxClosed l _ (fun m => by simp [Kont.HasHnd]) (fun m => by simp [Kont.Catches]))
    k ?_ k le_rfl ls _ _ ?_
  · rintro k' ls' v σ - ⟨hv, rfl⟩
    obtain rfl : v = Val.unit := hv
    refine erwp_det Φ₀_down hD hTP (fun μ => step1Only_plug (Head.seq μ _) rfl .hole) ?_
    exact erwp_val (v := Val.inj₂ (Val.loc l)) (.inr ⟨Val.loc l, rfl, rfl, rfl⟩)
  · obtain ⟨A, -⟩ := exists_fresh ls
    have hshape : vShape .unk δ₀ Val.unit (PMap.empty : WRes) := ⟨rfl, trivial⟩
    have hadm : AdmWf .unk δ₀ := fun _ h => h.elim
    obtain ⟨ds, hds⟩ := lineage_list (r := ⟨l, Val.unit, PMap.empty, .unk, δ₀⟩) hshape hadm
      (ExW.empty_of_all_imm (fun _ _ h => by simp at h))
    exact erwp_I_frameC (Φ := Φ₀) l .unk δ₀ hadm Val.unit PU (fun _ ρ h => ⟨h, trivial⟩)
      (fun _ _ _ _ h => h) (T2C_ilendOKC A) (empty_ilendOK A) T2C_fin (inStratum_empty A) hshape
      (ResU.comp_empty_right _) hds (fun _ _ _ _ _ _ h => h) k ls (lendIE l) PMap.empty _
      (inStratum_empty A) rfl (ResU.comp_empty_right _) (lendI_okC l A k _)

/-! ### The body: the cell, its finaliser, the loop -/

/-- `λc. ubind (λ_. free c, λ_. free c) (iterate (fI, c))`, its body. -/
def bodyICF : Expr :=
  .app (.app (.val (.prim .ubind)) (.pair (.val (Val.lam (freeE (.var 1))))
    (.val (Val.lam (freeE (.var 1)))))) (.app (.val (.prim .iterate)) (.pair (.val fI) (.var 0)))

/-- `(λc. ubind (λ_. free c, λ_. free c) (iterate (fI, c))) (alloc ())`. -/
def bodyIC : Expr :=
  .app (.val (Val.lam bodyICF)) (.app (.val (.prim .alloc)) (.val Val.unit))

theorem bodyICF_subst (l : Loc) :
    Expr.subst 0 (Val.loc l) bodyICF =
      ubindE (Val.pair (dF l) (dF l)) (iterateE fI (Val.loc l)) := by
  simp [bodyICF, dF, ubindE, Expr.subst, iterateE, Val.pair, Val.lam, Val.loc, freeE, Expr.val,
    Expr.shift, Val.prim, subst_closedAt _ _ (show closedAt 0 fI.1 = true from rfl) (Nat.zero_le _)]

/-- **The finaliser consumes the `imm` lend's claim.** -/
theorem dFI_ok (l : Loc) (k : Nat) (ls : List SRec) (ρ : WRes)
    (h : claimI l Val.unit PMap.empty k ρ) :
    rwp (ℍ := ℍ) Φ₀ (fun _ _ _ ρ' => ρ' = PMap.empty) k ls (.app (.val (dF l)) (.val .unit)) ρ := by
  obtain rfl := ResU.CompS.functional h (ResU.comp_empty_right _)
  rw [rwp_iff_rwpG]
  refine rwpG_det Φ₀_down (fun _ _ _ _ ⟨v, hv, hq⟩ => ⟨v, hv, hq⟩)
    (fun μ => step1Only_plug (Head.beta μ _ Val.unit) rfl .hole) ?_
  have e : Kont.hole.plug (Expr.subst 0 Val.unit (freeE (.val (Val.loc l)))) =
      (.app (.val (.prim .free)) (.val (.loc l)) : Expr) := by
    simp [Expr.subst, Kont.plug, freeE, Val.loc, Expr.val, Val.prim]
  rw [e, ← rwp_iff_rwpG]
  exact rwp_free ls l Val.unit _ ⟨_, PMap.empty, ResU.comp_empty_right _, rfl, rfl⟩

theorem bodyI_okC (n : Nat) :
    erwp (ℍ := ℍ) Φ₀ (opTableN (T2C (ℍ := ℍ))) QZ n [] bodyIC (PMap.empty : WRes) := by
  have hD := opTableN_down (T2C_down (ℍ := ℍ))
  refine erwp_alloc Φ₀_down (opTableN_local _) (.appR (.val (Val.lam bodyICF)) .hole) Val.unit
    (fun l σ₁ σ₂ hcell hc => ?_)
  obtain rfl := eq_of_compS_empty_left hc
  refine erwp_det Φ₀_down hD QZ_down (fun μ => step1Only_plug (Head.beta μ _ _) rfl .hole) ?_
  rw [Kont.plug_hole, bodyICF_subst]
  refine erwp_ubindClaim Φ₀_down T2C_down empty_down (fun _ _ _ h => by cases h) T2C_e T2C_fin
    (dF l) (dF l) (dFI_ok l) QZ_down (Qin := QF) (fun _ _ _ _ h => h.elim) _ _ _ _ ?_
  refine erwp_iterate Φ₀_down (T2I_down l)
    (T2I_ctxClosed l _ (fun m => by simp [iterK, Kont.HasHnd])
      (fun m => by simp [iterK, Kont.Catches])) QF_down rfl (I := ILu l) (en := tickEnt)
    (by simp [OpTabN.claimT, T2C, T1, tickEnt, FileProg.divEff_ne6]) rfl rfl
    (fun _ _ => ⟨rfl, rfl⟩) (fun _ _ _ _ h => h) (fun s ρ ⟨hs, _⟩ => by subst hs; rfl)
    (fun k s ls ρ hI => turnI_okC l k s ls ρ hI) _ _ _ _ ⟨rfl, hcell⟩

/-- `hnd_Div rtH (hnd_Y yCancel bodyIC)`. -/
def progILendCancel : Expr := hndE DivRuntime.rtH (hndE yHC bodyIC)

theorem progILendCancel_ok (n : Nat) :
    erwp (ℍ := ℍ) Φ₀ (opTableN OpTabN.empty) QZ n [] progILendCancel (PMap.empty : WRes) :=
  erwp_rtH Φ₀_down n [] _ _ (erwp_yHC n [] _ _ (bodyI_okC n))

/-- **The `imm` cancel test.** A cell lent `imm` across a cancellable `y` on a loop with no
bound; the scheduler stores `κ` and cancels it; the cancel unwinds through the lend to the
finaliser frame, whose finaliser takes the lend's claim and releases the cell. Every
configuration a run reaches is a value or steps, a value only at the empty memory, and every
`free` finds its cell. No fuel. -/
theorem progILendCancel_orDiverges : OrDiverges (ℍ := ℍ) progILendCancel :=
  erwp_adequacy (Φ := Φ₀) (fun _ _ _ _ h => h) progILendCancel_ok

end BoCa.Fig16.LogRel.Core.Chain.SI.ILendProg

end
