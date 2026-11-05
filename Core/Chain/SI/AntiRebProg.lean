import Core.Chain.SI.IStopF
import Core.Chain.SI.AntiLendProg
import Core.Chain.SI.RebProg

/-!
# The test: an `imm` reborrow of a boxed field, through a `mut` borrow, across a `yield`

The program is `RebProg.progReb`:

    fR = λs. λb. case b { next → (λx. y (); (λz. ()) (!x)) (!s); inr s | close → () }

with the state `c ↦ own(d) ● d ↦ own(u₀) ● e ↦ own(())` (`d` a `ref` to a thunk). There each
turn lends `c` `imm`. Here each turn is a `&mut self` method: `c` is lent `mut` (`erwp_M_frame`),
the method opens the borrow (`erwp_M_antiFrame`), lends the opened cell `imm` (`erwp_I_frameF`),
loads `d` through it and reborrows the field at a shorter lifetime (`erwp_reborrow`, at the
canonical image); the reborrow is live across `y`, whose `κ` the scheduler stores and resumes.

At the stop the reborrow folds (`erwp_reborrow`), the Imm Frame folds `c` back to `own` with its content
unchanged (the guard `ImmFold`), the anti-frame seals `c` with that content (`CellFold`), and the
outer lend folds `c` to `own`. At the resume each is undone in the reverse order.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core.Chain.SI.AntiRebProg
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel.Core.Chain.SI.LendProg
open BoCa.Fig16.LogRel.Core.Chain.SI.ILendProg
open BoCa.Fig16.LogRel.Core.Chain.SI.RebProg
open BoCa.Fig16.LogRel.Core.Chain.SI.AntiLendProg
open BoCa.BoLo (Heap Step1 Steps Head Kont performE raiseE cancelVal opPayload freeE hndE hndVal
  clauseAt capTag)
open BoCa.Lifetime (LSub LifeVar)

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

/-- The value's family: `d`, with `d ↦ own(u₀) ● e ↦ own(())`. -/
def famR (A : Life) : Nat → Val → SPropS Loc Val A := fun _ v r =>
  ∃ (d e : Loc), v = Val.loc d ∧
    ResU.CompS (ResU.single d (CellU.ownOf u₀)) (ResU.single e (CellU.ownOf .unit)) r.1

theorem famR_down (A : Life) : DownFam A (famR A) := fun _ _ _ h => h

/-- The method's end: the value whole again. -/
def QR (c : Loc) : PostN := fun _ _ v ρ => v = Val.unit ∧ ∃ (d e : Loc) (R₀ : WRes),
  ResU.CompS (ResU.single d (CellU.ownOf u₀)) (ResU.single e (CellU.ownOf .unit)) R₀ ∧
  ResU.CompS (ResU.single c (CellU.ownOf (.loc d))) R₀ ρ

/-- The anti-frame's postcondition: the borrow released, then the lender's. -/
def QDR (c : Loc) (A : Life) : PostN :=
  fun k ls v X => NoOwn X ∧ MFPost c A (famR A) (QR c) k ls v PMap.empty

/-- **The opened borrow**: lent `imm` at a lifetime below the list's records, the field
reborrowed inside across `y`; at a stop the Imm Frame's fold is the seal's guard. -/
theorem openR_ok {Φ : LocFam} (hΦ : Φ.Down) (c d e : Loc) (R₀ : WRes)
    (hR₀ : ResU.CompS (ResU.single d (CellU.ownOf u₀)) (ResU.single e (CellU.ownOf .unit)) R₀)
    (Ao : Life) (k : Nat) (ls : List SRec) (X : WRes)
    (hX : ResU.CompS R₀ (ResU.single c (CellU.ownOf (.loc d))) X) :
    erwp (ℍ := ℍ) Φ (opTableG T2 (CellFold c Ao (famR Ao)))
      (AFPost c Ao (famR Ao) (QDR c Ao)) k ls (lendRE c) X := by
  obtain ⟨A, -⟩ := exists_fresh ls
  have hshape : vShape rT δ₀ (.loc d) R₀ :=
    ⟨d, u₀, pure_sep_mk rfl ⟨_, _, hR₀, rfl, trivial⟩⟩
  have hadm : AdmWf rT δ₀ := fun y hy => by simp [rT, VFree, CFree] at hy
  have hex : ExS R₀ R₀ := (ExS.split hR₀).mpr ⟨_, _, ExW.single_own d u₀,
    ExW.single_own e Val.unit, hR₀⟩
  obtain ⟨ds, hds⟩ := lineage_list (r := recR c d R₀) hshape hadm hex
  have houtP : R₀.InStratum A := R₀_inStratum A hR₀
  have hI := erwp_I_frameF (Φ := Φ) c rT δ₀ hadm (.loc d) (PR d R₀)
    (fun _ ρ' h => by obtain ⟨-, rfl⟩ := h; exact hshape)
    (fun _ _ _ _ h => h) (T2_ilendOK A) (fun _ _ _ _ _ _ h => h) k ls (lendRE c)
    R₀ X PMap.empty X houtP (inStratum_empty A) ⟨rfl, rfl⟩ (ResU.CompS.comm hX)
    (ResU.comp_empty_right _) ds hds
    (lendR_ok hΦ c d e R₀ hR₀ A houtP k ls ds)
  refine erwp_mono (fun k ls' v ρ h => ?_) (opTableG_mono fun k ls' ρ h => ?_) _ _ _ _ hI
  · -- the return: `c` and its content handed back, sealed
    obtain ⟨rfl, hρ⟩ := h
    refine ⟨Val.loc d, R₀, R₀_inStratum Ao hR₀, ⟨d, e, rfl, hR₀⟩, PMap.empty, R₀, hρ,
      ResU.comp_empty_right _, fun Y hY => ?_⟩
    obtain rfl := eq_of_compS_empty_left hY
    refine ⟨noOwn_single_mut c, inStratum_empty Ao, fun w' Y hY σ ⟨hσ, d', e', hw', hσ'⟩ Z hZ =>
      ⟨rfl, d', e', σ, hσ', ?_⟩⟩
    obtain rfl := eq_of_compS_empty_left hY
    subst hw'
    exact hZ
  · -- a stop: `c` and its content, whole, in the share
    obtain ⟨R, hR⟩ := h
    obtain ⟨rest, h1, h2⟩ := compS_reassoc (ResU.CompS.comm hX) hR
    exact ⟨Val.loc d, R₀, R₀_inStratum Ao hR₀, ⟨d, e, rfl, hR₀⟩, R, rest, h2, h1⟩

/-- **The method**: `c` lent `mut` (outside), the borrow opened for the body, released at the
end. -/
theorem methodR_ok {Φ : LocFam} (hΦ : Φ.Down) (c d e : Loc) (R₀ : WRes)
    (hR₀ : ResU.CompS (ResU.single d (CellU.ownOf u₀)) (ResU.single e (CellU.ownOf .unit)) R₀)
    (Ao : Life) (k : Nat) (ls : List SRec) (BM : WRes)
    (hBM : ResU.CompS PMap.empty (ResU.single c (CellU.mutOf Ao (.loc d) R₀
      (R₀_inStratum Ao hR₀) (famR Ao k) ⟨d, e, rfl, hR₀⟩)) BM) :
    erwp (ℍ := ℍ) (Φ.set c Ao (famR Ao)) (opTableN T2) (MFPost c Ao (famR Ao) (QR c)) k ls
      (lendRE c) BM := by
  have hΦ' := LocFam.set_down (l := c) hΦ (famR_down Ao)
  have hFl : Φ.set c Ao (famR Ao) c = some ⟨Ao, famR Ao⟩ := by simp [LocFam.set]
  obtain rfl := eq_of_compS_empty_left hBM
  refine erwp_dump (opTableN_local T2) k ls _ _ (erwp_M_antiFrame hΦ' hFl T2_afOK k ls
    (lendRE c) (.loc d) R₀ (R₀_inStratum Ao hR₀) k ⟨d, e, rfl, hR₀⟩ PMap.empty _
    (ResU.comp_empty_right _) fun W X hW hX => ?_)
  obtain rfl := eq_of_compS_empty_left hX
  exact openR_ok hΦ' c d e R₀ hR₀ Ao k ls _ hW

/-- **A turn**: three steps to `(λx. y (); (λz. ()) (!x)) (!c); inr c`, the method under `c`'s
`mut` lend, then `inr c`. -/
theorem turnRM_ok {Φ : LocFam} (hΦ : Φ.Down) (Ao : Life) (k : Nat) (s : Val) (ls : List SRec)
    (ρ : WRes) (hI : IR s ρ) :
    erwp (ℍ := ℍ) Φ (opTableN T2) (turnPostN IR QZ) k ls
      (.app (.app (.val fR) (.val s)) (.val nextV)) ρ := by
  obtain ⟨c, d, e, R₀, rfl, hR₀, hρ⟩ := hI
  have hD := opTableN_down T2_down
  have hTP : (turnPostN IR QZ).Down := fun _ _ _ _ h => by
    rcases h with ⟨x, hx, hq⟩ | h
    · exact .inl ⟨x, hx, hq⟩
    · exact .inr h
  refine erwp_det hΦ hD hTP
    (fun μ => step1Only_plug (Head.beta μ _ (Val.loc c)) rfl (.appL .hole nextV)) ?_
  have e₁ : (Kont.appL .hole nextV).plug (Expr.subst 0 (Val.loc c)
      (.lam (.case (.var 0) (.seq (.app (.val lamX) (.app (.val (.prim .load)) (.var 2)))
        (.inj₂ (.var 2))) (.val .unit)))) =
      Kont.hole.plug (.app (.val (Val.lam (.case (.var 0)
        (.seq (lendRE c) (.inj₂ (.val (Val.loc c)))) (.val .unit)))) (.val nextV)) := by
    simp [Expr.subst, Expr.shift, Kont.plug, lamX, discardV, lendRE, ldR, FileProg.yE, performE,
      opPayload, Val.pair, Val.i32, Val.unit, Val.lam, Val.loc, Expr.val, Val.prim, Val.shift]
  rw [e₁]
  refine erwp_det hΦ hD hTP (fun μ => step1Only_plug (Head.beta μ _ nextV) rfl .hole) ?_
  have e₂ : Kont.hole.plug (Expr.subst 0 nextV (.case (.var 0)
        (.seq (lendRE c) (.inj₂ (.val (Val.loc c)))) (.val .unit))) =
      Kont.hole.plug (.case (.val (Val.inj₁ Val.unit))
        (.seq (lendRE c) (.inj₂ (.val (Val.loc c)))) (.val .unit)) := by
    simp [Expr.subst, Kont.plug, lamX, discardV, lendRE, ldR, FileProg.yE, performE, opPayload,
      Val.pair, Val.i32, Val.unit, nextV, Val.inj₁, Val.loc, Expr.val, Val.prim, Val.lam]
  rw [e₂]
  refine erwp_det hΦ hD hTP (fun μ => step1Only_plug (Head.case₁ μ Val.unit _ _) rfl .hole) ?_
  have e₃ : Kont.hole.plug (Expr.subst 0 Val.unit
        (.seq (lendRE c) (.inj₂ (.val (Val.loc c))))) =
      (Kont.seq .hole (.inj₂ (.val (Val.loc c)))).plug (lendRE c) := by
    simp [Expr.subst, Kont.plug, lamX, discardV, lendRE, ldR, FileProg.yE, performE, opPayload,
      Val.pair, Val.i32, Val.unit, Val.loc, Expr.val, Val.prim, Val.lam]
  rw [e₃]
  refine erwp_bind_le (Q' := QR c) hΦ _ (fun m => by simp [Kont.HasHnd])
    (fun m => by simp [Kont.Catches]) (OpTabN.ctxClosed_of_fin T2_fin _) k ?_ k le_rfl ls _ _ ?_
  · rintro k' ls' v σ - ⟨rfl, d', e', R₀', hR₀', hσ⟩
    refine erwp_det hΦ hD hTP (fun μ => step1Only_plug (Head.seq μ _) rfl .hole) ?_
    exact erwp_val (v := Val.inj₂ (Val.loc c)) (.inr ⟨Val.loc c, rfl, c, d', e', R₀', rfl, hR₀', hσ⟩)
  · -- `c` lent `mut` for the method
    exact erwp_M_frame (famR_down Ao) (T2_lendOK Ao) k k le_rfl ls (lendRE c) (.loc d) R₀ ρ
      PMap.empty ρ (R₀_inStratum Ao hR₀) (inStratum_empty _) (famR Ao k) (fun _ _ h => h)
      ⟨d, e, rfl, hR₀⟩ hρ (ResU.comp_empty_right _) (methodR_ok hΦ c d e R₀ hR₀ Ao k ls)

theorem bodyRM_ok (n : Nat) :
    erwp (ℍ := ℍ) Φ₀ (opTableN T2) QZ n [] bodyR (PMap.empty : WRes) := by
  have hD := opTableN_down T2_down
  have hL := opTableN_local T2
  refine erwp_alloc Φ₀_down hL (.appR (.val lamE) .hole) Val.unit (fun e σ₁ σ₂ hcell hc => ?_)
  obtain rfl := eq_of_compS_empty_left hc
  refine erwp_det Φ₀_down hD QZ_down (fun μ => step1Only_plug (Head.beta μ _ _) rfl .hole) ?_
  have h₁ : Kont.hole.plug (Expr.subst 0 (Val.loc e)
      (.app (.val lamD) (.app (.val (.prim .alloc)) (.val u₀)))) =
      (Kont.appR (.val lamD) .hole).plug (.app (.val (.prim .alloc)) (.val u₀)) := by
    simp [Expr.subst, Kont.plug, lamD, lamC, fR, lamX, discardV, u₀, FileProg.idV, FileProg.yE,
      performE, opPayload, Val.pair, Val.i32, Val.unit, Val.loc, Expr.val, Val.prim, Val.lam]
  rw [h₁]
  refine erwp_alloc Φ₀_down hL (.appR (.val lamD) .hole) u₀ (fun d τ₁ τ₂ hcd hcd' => ?_)
  refine erwp_det Φ₀_down hD QZ_down (fun μ => step1Only_plug (Head.beta μ _ _) rfl .hole) ?_
  have h₂ : Kont.hole.plug (Expr.subst 0 (Val.loc d)
      (.app (.val lamC) (.app (.val (.prim .alloc)) (.var 0)))) =
      (Kont.appR (.val lamC) .hole).plug (.app (.val (.prim .alloc)) (.val (Val.loc d))) := by
    simp [Expr.subst, Kont.plug, lamC, fR, lamX, discardV, FileProg.yE, performE, opPayload,
      Val.pair, Val.i32, Val.unit, Val.loc, Expr.val, Val.prim, Val.lam]
  rw [h₂]
  refine erwp_alloc Φ₀_down hL (.appR (.val lamC) .hole) (Val.loc d)
    (fun c υ₁ υ₂ hcc hcc' => ?_)
  refine erwp_det Φ₀_down hD QZ_down (fun μ => step1Only_plug (Head.beta μ _ _) rfl .hole) ?_
  have h₃ : Kont.hole.plug (Expr.subst 0 (Val.loc c)
      (.app (.val (.prim .iterate)) (.pair (.val fR) (.var 0)))) = iterateE fR (Val.loc c) := by
    simp [Expr.subst, Kont.plug, iterateE, Val.pair, Val.loc, Expr.val, Val.prim,
      subst_closedAt _ _ (show closedAt 0 fR.1 = true from rfl) (Nat.zero_le _)]
  rw [h₃]
  subst hcell hcd hcc
  exact erwp_iterate Φ₀_down T2_down (OpTabN.ctxClosed_of_fin T2_fin _) QZ_down rfl (I := IR)
    (en := tickEnt) (by simp [T2, T1, FileProg.divEff_ne6]) rfl rfl
    (fun _ _ => ⟨rfl, rfl⟩) (fun _ _ _ _ h => h) IR_closed
    (fun k s ls ρ hI => turnRM_ok Φ₀_down 0 k s ls ρ hI) _ _ _ _
    ⟨c, d, e, _, rfl, ResU.CompS.comm hcd', ResU.CompS.comm hcc'⟩

theorem progReb_okM (n : Nat) :
    erwp (ℍ := ℍ) Φ₀ (opTableN OpTabN.empty) QZ n [] progReb (PMap.empty : WRes) :=
  erwp_rtH Φ₀_down n [] _ _ (erwp_yH Φ₀_down n [] _ _ (bodyRM_ok n))

/-- **The test.** On every turn of a loop with no bound, a value is lent `mut` to a method,
which opens the borrow, lends it `imm`, and reborrows a boxed field (a `ref` to a thunk) at a
shorter lifetime, live across `y`, under a scheduler that stores the continuation in a cell and
resumes it, under the runtime's `Div` handler: every configuration a run reaches is a value or
steps, a value only at the empty memory, and every `free` finds its cell. No fuel. -/
theorem progReb_orDivergesM : OrDiverges (ℍ := ℍ) progReb :=
  erwp_adequacy (Φ := Φ₀) (fun _ _ _ _ h => h) progReb_okM

end BoCa.Fig16.LogRel.Core.Chain.SI.AntiRebProg

end
