import Core.Chain.SI.AntiStopN
import Core.Chain.SI.LendProg

/-!
# The test: a field of a `mut`-borrowed value borrowed `mut` across a `yield`

    progAnti = hnd_Div rtH (hnd_Y yStore (
                 (λd. (λc. iterate (fA, c)) (alloc d)) (alloc 1)))

    fA = λs. λb. case b { next → (λx. y (); x := 5) (!s); inr s | close → () }

The state `s` is `c ↦ own(d) ● d ↦ own(u)`: a value whose field is a box. Each turn is a
`&mut self` method: it lends `c` `mut` (`erwp_M_frame`), and the borrowed run opens the borrow
(the Mut Anti-Frame, `erwp_M_antiFrame`), reads the field `d` out of it, lends the field `mut`
(`erwp_M_frameF`) and holds that borrow across `y`, whose `κ` the scheduler stores in a cell,
takes back and resumes; after the resume the field borrow writes, and every borrow ends. No
segmentation in the term: the program is one turn of three nested borrows with a stop inside.

At the stop the field's lend folds the field back into `own` (the Mut Frame's fold, `erwp_M_frame`), the opened `c`,
framed beside it (`erwpG_frame`), is sealed again with the field as its content (the guard
`CellFold c A boxF` from `CellFold d A famF`), and the outer lend folds `c` back to `own`. At the
resume each is undone in the reverse order.

`progAnti_orDiverges`: every configuration a run reaches is a value or steps, a value only at
the empty memory, and every `free` finds its cell. No fuel.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core.Chain.SI.AntiLendProg
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel.Core.Chain.SI.LendProg
open BoCa.BoLo (Heap Step1 Steps Head Kont performE raiseE cancelVal opPayload freeE hndE hndVal
  clauseAt capTag)

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

theorem T2_afOK : T2.AFOK := fun _ _ en h _ => by
  rcases ent_cases h with rfl | rfl <;> exact ⟨rfl, rfl⟩

/-- The value's family: a location whose cell holds anything, owned. -/
def boxF (A : Life) : Nat → Val → SPropS Loc Val A := fun _ v r =>
  ∃ (d : Loc) (w : Val), v = Val.loc d ∧ r.1 = ResU.single d (CellU.ownOf w)

theorem boxF_down (A : Life) : DownFam A (boxF A) := fun _ _ _ h => h

theorem inStratum_own (A : Life) (d : Loc) (w : Val) :
    ResU.InStratum A (ResU.single d (CellU.ownOf w)) :=
  ResU.inStratum_single d (CellU.inStratum_ownOf A w)

/-- `!ℓ`. -/
def ldA (l : Loc) : Expr := .app (.val (.prim .load)) (.val (Val.loc l))

/-- `λx. y (); x := 5`. -/
def lamW : Val :=
  Val.lam (.seq FileProg.yE (.app (.app (.val (.prim .store)) (.var 0)) (.val (Val.i32 5))))

/-- The method's body: `(λx. y (); x := 5) (!c)`. -/
def fieldE (c : Loc) : Expr := .app (.val lamW) (ldA c)

/-- The method's end: `()`, and the value whole again. -/
def QA (c : Loc) : PostN := fun _ _ v ρ => v = Val.unit ∧ ∃ (d : Loc) (u : Val),
  ResU.CompS (ResU.single c (CellU.ownOf (.loc d))) (ResU.single d (CellU.ownOf u)) ρ

/-- The anti-frame's postcondition: the borrow released, then the lender's. -/
def QD (c : Loc) (A : Life) : PostN :=
  fun k ls v X => NoOwn X ∧ MFPost c A (boxF A) (QA c) k ls v PMap.empty

/-- **The opened borrow**: `!c` reads the field out of the opened cell, the field is lent `mut`
across `y` with the opened cell framed, and at the end the cell is sealed with the field as its
content. At a stop the field's fold and the frame give the seal's guard. -/
theorem open_ok {Φ : LocFam} (hΦ : Φ.Down) (c d : Loc) (u : Val) (A : Life) (k : Nat)
    (ls : List SRec) (X : WRes)
    (hX : ResU.CompS (ResU.single d (CellU.ownOf u)) (ResU.single c (CellU.ownOf (.loc d))) X) :
    erwp (ℍ := ℍ) Φ (opTableG T2 (CellFold c A (boxF A))) (AFPost c A (boxF A) (QD c A)) k ls
      (fieldE c) X := by
  have hL := opTableG_local T2 (CellFold c A (boxF A))
  have hplug : fieldE c = (Kont.appR (.val lamW) .hole).plug (ldA c) := rfl
  rw [hplug]
  refine erwp_bindR hΦ hL _ (rwp_load ls c (.loc d) _ ⟨_, _, ResU.CompS.comm hX, rfl,
    fun ρ₁ ρ₂ h₁ hc => ?_⟩)
  subst h₁
  generalize k - 1 = k'
  cases k' with
  | zero => exact erwp_zero
  | succ k₀ =>
  refine erwp_step hL (fun μ => step1Only_plug (Head.beta μ _ (Val.loc d)) rfl .hole) ?_
  have e₁ : Kont.hole.plug (Expr.subst 0 (Val.loc d)
      (.seq FileProg.yE (.app (.app (.val (.prim .store)) (.var 0)) (.val (Val.i32 5))))) =
      lendE d := by
    simp [Expr.subst, Kont.plug, FileProg.yE, lendE, wrL, performE, opPayload, Val.pair,
      Val.i32, Val.unit, Val.loc, Expr.val, Val.prim, Val.lam, Val.storeV]
  rw [e₁]
  -- the field's lend, the opened cell framed beside it
  have hfr := erwpG_frame (Φ := Φ) T2_afOK (G := CellFold d A (famF A)) (Q := Qlend d)
    (fun _ ρ => ρ = ResU.single c (CellU.ownOf (.loc d))) (fun _ _ _ _ h => h) k₀ ls (lendE d)
    _ _ _ hc rfl
    (erwp_M_frameF (famF_down A) (T2_lendOK A) k₀ k₀ le_rfl ls (lendE d) u PMap.empty _
      PMap.empty _ (inStratum_empty A) (inStratum_empty _) (famF A k₀) (fun _ _ h => h) rfl
      (ResU.comp_empty_right _) (ResU.comp_empty_right _) (lend_ok hΦ d A u k₀ ls))
  refine erwp_mono (fun k ls' v ρ h => ?_) (opTableG_mono fun k ls' ρ h => ?_) _ _ _ _ hfr
  · -- the return: the field handed back, sealed into `c`
    obtain ⟨ρ₁, ρ₂, hc₁, ⟨rfl, w, rfl⟩, rfl⟩ := h
    refine ⟨Val.loc d, ResU.single d (CellU.ownOf w), inStratum_own A d w, ⟨d, w, rfl, rfl⟩,
      PMap.empty, _, ResU.CompS.comm hc₁, ResU.comp_empty_right _, fun X hX => ?_⟩
    obtain rfl := eq_of_compS_empty_left hX
    refine ⟨noOwn_single_mut c, inStratum_empty A, fun w' Y hY σ ⟨hσ, d', u', hw', hσ'⟩ Z hZ =>
      ⟨rfl, d', u', ?_⟩⟩
    obtain rfl := eq_of_compS_empty_left hY
    subst hw'
    have : σ = ResU.single d' (CellU.ownOf u') := hσ'
    subst this
    exact hZ
  · -- a stop: the field folded, the opened cell beside it
    obtain ⟨ρ₁, ρ₂, hc₁, ⟨w, χ, hχ, hw, R, rest, hr1, hr2⟩, rfl⟩ := h
    have hχ0 : χ = PMap.empty := hw
    subst hχ0
    obtain rfl := eq_of_compS_empty_left hr2
    exact ⟨Val.loc d, ResU.single d (CellU.ownOf w), inStratum_own A d w, ⟨d, w, rfl, rfl⟩, _,
      ρ₁, ResU.CompS.comm hc₁, hr1⟩

/-- **The method**: `c` lent `mut` (outside), the borrow opened by the anti-frame for the body,
and released at the end. -/
theorem method_ok {Φ : LocFam} (hΦ : Φ.Down) (c d : Loc) (u : Val) (A : Life) (k : Nat)
    (ls : List SRec) (BM : WRes)
    (hBM : ResU.CompS PMap.empty (ResU.single c (CellU.mutOf A (.loc d)
      (ResU.single d (CellU.ownOf u)) (inStratum_own A d u) (boxF A k) ⟨d, u, rfl, rfl⟩)) BM) :
    erwp (ℍ := ℍ) (Φ.set c A (boxF A)) (opTableN T2) (MFPost c A (boxF A) (QA c)) k ls
      (fieldE c) BM := by
  have hΦ' := LocFam.set_down (l := c) hΦ (boxF_down A)
  have hFl : Φ.set c A (boxF A) c = some ⟨A, boxF A⟩ := by simp [LocFam.set]
  obtain rfl := eq_of_compS_empty_left hBM
  refine erwp_dump (opTableN_local T2) k ls _ _ (erwp_M_antiFrame hΦ' hFl T2_afOK k ls (fieldE c)
    (.loc d) _ (inStratum_own A d u) k ⟨d, u, rfl, rfl⟩ PMap.empty _ (ResU.comp_empty_right _)
    fun W X hW hX => ?_)
  obtain rfl := eq_of_compS_empty_left hX
  exact open_ok hΦ' c d u A k ls _ hW

/-! ### The turn and the program -/

/-- The loop's invariant: the state is `c ↦ own(d) ● d ↦ own(u)`. -/
def IA : Val → WProp := fun s ρ => ∃ (c d : Loc) (u : Val), s = Val.loc c ∧
  ResU.CompS (ResU.single c (CellU.ownOf (.loc d))) (ResU.single d (CellU.ownOf u)) ρ

theorem IA_closed : ∀ s ρ, IA s ρ → closedAt 0 s.1 = true := by
  rintro s ρ ⟨c, -, -, rfl, -⟩
  rfl

/-- `λs. λb. case b {next → (λx. y (); x := 5) (!s); inr s | close → ()}`. -/
def fA : Val :=
  Val.lam (.lam (.case (.var 0) (.seq (.app (.val lamW) (.app (.val (.prim .load)) (.var 2)))
    (.inj₂ (.var 2))) (.val .unit)))

/-- **A turn**: three steps to `(λx. y (); x := 5) (!c); inr c`, the method under `c`'s `mut`
lend, then `inr c`. -/
theorem turnA_ok {Φ : LocFam} (hΦ : Φ.Down) (A : Life) (k : Nat) (s : Val) (ls : List SRec)
    (ρ : WRes) (hI : IA s ρ) :
    erwp (ℍ := ℍ) Φ (opTableN T2) (turnPostN IA QZ) k ls
      (.app (.app (.val fA) (.val s)) (.val nextV)) ρ := by
  obtain ⟨c, d, u, rfl, hρ⟩ := hI
  have hD := opTableN_down T2_down
  have hTP : (turnPostN IA QZ).Down := fun _ _ _ _ h => by
    rcases h with ⟨x, hx, hq⟩ | h
    · exact .inl ⟨x, hx, hq⟩
    · exact .inr h
  refine erwp_det hΦ hD hTP
    (fun μ => step1Only_plug (Head.beta μ _ (Val.loc c)) rfl (.appL .hole nextV)) ?_
  have e₁ : (Kont.appL .hole nextV).plug (Expr.subst 0 (Val.loc c)
      (.lam (.case (.var 0) (.seq (.app (.val lamW) (.app (.val (.prim .load)) (.var 2)))
        (.inj₂ (.var 2))) (.val .unit)))) =
      Kont.hole.plug (.app (.val (Val.lam (.case (.var 0)
        (.seq (fieldE c) (.inj₂ (.val (Val.loc c)))) (.val .unit)))) (.val nextV)) := by
    simp [Expr.subst, Expr.shift, Kont.plug, lamW, fieldE, ldA, FileProg.yE, performE, opPayload,
      Val.pair, Val.i32, Val.unit, Val.lam, Val.loc, Expr.val, Val.prim, Val.shift]
  rw [e₁]
  refine erwp_det hΦ hD hTP (fun μ => step1Only_plug (Head.beta μ _ nextV) rfl .hole) ?_
  have e₂ : Kont.hole.plug (Expr.subst 0 nextV (.case (.var 0)
        (.seq (fieldE c) (.inj₂ (.val (Val.loc c)))) (.val .unit))) =
      Kont.hole.plug (.case (.val (Val.inj₁ Val.unit))
        (.seq (fieldE c) (.inj₂ (.val (Val.loc c)))) (.val .unit)) := by
    simp [Expr.subst, Kont.plug, lamW, fieldE, ldA, FileProg.yE, performE, opPayload, Val.pair,
      Val.i32, Val.unit, nextV, Val.inj₁, Val.loc, Expr.val, Val.prim, Val.lam]
  rw [e₂]
  refine erwp_det hΦ hD hTP (fun μ => step1Only_plug (Head.case₁ μ Val.unit _ _) rfl .hole) ?_
  have e₃ : Kont.hole.plug (Expr.subst 0 Val.unit
        (.seq (fieldE c) (.inj₂ (.val (Val.loc c))))) =
      (Kont.seq .hole (.inj₂ (.val (Val.loc c)))).plug (fieldE c) := by
    simp [Expr.subst, Kont.plug, lamW, fieldE, ldA, FileProg.yE, performE, opPayload, Val.pair,
      Val.i32, Val.unit, Val.loc, Expr.val, Val.prim, Val.lam]
  rw [e₃]
  refine erwp_bind_le (Q' := QA c) hΦ _ (fun m => by simp [Kont.HasHnd])
    (fun m => by simp [Kont.Catches]) (OpTabN.ctxClosed_of_fin T2_fin _) k ?_ k le_rfl ls _ _ ?_
  · rintro k' ls' v σ - ⟨rfl, d', u', hσ⟩
    refine erwp_det hΦ hD hTP (fun μ => step1Only_plug (Head.seq μ _) rfl .hole) ?_
    exact erwp_val (v := Val.inj₂ (Val.loc c)) (.inr ⟨Val.loc c, rfl, c, d', u', rfl, hσ⟩)
  · -- `c` lent `mut` for the method
    exact erwp_M_frame (boxF_down A) (T2_lendOK A) k k le_rfl ls (fieldE c) (.loc d)
      (ResU.single d (CellU.ownOf u)) ρ PMap.empty ρ (inStratum_own A d u) (inStratum_empty _)
      (boxF A k) (fun _ _ h => h) ⟨d, u, rfl, rfl⟩ hρ (ResU.comp_empty_right _)
      (method_ok hΦ c d u A k ls)

/-- `(λc. iterate (fA, c))`. -/
def lamCA : Val := Val.lam (.app (.val (.prim .iterate)) (.pair (.val fA) (.var 0)))

/-- `(λd. lamCA (alloc d))`. -/
def lamDA : Val := Val.lam (.app (.val lamCA) (.app (.val (.prim .alloc)) (.var 0)))

/-- `lamDA (alloc 1)`. -/
def bodyA : Expr := .app (.val lamDA) (.app (.val (.prim .alloc)) (.val (Val.i32 1)))

/-- `hnd_Div rtH (hnd_Y yStore bodyA)`. -/
def progAnti : Expr := hndE DivRuntime.rtH (hndE yH bodyA)

theorem bodyA_ok (A : Life) (n : Nat) :
    erwp (ℍ := ℍ) Φ₀ (opTableN T2) QZ n [] bodyA (PMap.empty : WRes) := by
  have hD := opTableN_down T2_down
  have hL := opTableN_local T2
  refine erwp_alloc Φ₀_down hL (.appR (.val lamDA) .hole) (Val.i32 1)
    (fun d τ₁ τ₂ hcd hcd' => ?_)
  obtain rfl := eq_of_compS_empty_left hcd'
  refine erwp_det Φ₀_down hD QZ_down (fun μ => step1Only_plug (Head.beta μ _ _) rfl .hole) ?_
  have h₂ : Kont.hole.plug (Expr.subst 0 (Val.loc d)
      (.app (.val lamCA) (.app (.val (.prim .alloc)) (.var 0)))) =
      (Kont.appR (.val lamCA) .hole).plug (.app (.val (.prim .alloc)) (.val (Val.loc d))) := by
    simp [Expr.subst, Kont.plug, lamCA, fA, lamW, FileProg.yE, performE, opPayload,
      Val.pair, Val.i32, Val.unit, Val.loc, Expr.val, Val.prim, Val.lam]
  rw [h₂]
  refine erwp_alloc Φ₀_down hL (.appR (.val lamCA) .hole) (Val.loc d)
    (fun c υ₁ υ₂ hcc hcc' => ?_)
  refine erwp_det Φ₀_down hD QZ_down (fun μ => step1Only_plug (Head.beta μ _ _) rfl .hole) ?_
  have h₃ : Kont.hole.plug (Expr.subst 0 (Val.loc c)
      (.app (.val (.prim .iterate)) (.pair (.val fA) (.var 0)))) = iterateE fA (Val.loc c) := by
    simp [Expr.subst, Kont.plug, iterateE, Val.pair, Val.loc, Expr.val, Val.prim,
      subst_closedAt _ _ (show closedAt 0 fA.1 = true from rfl) (Nat.zero_le _)]
  rw [h₃]
  subst hcd hcc
  exact erwp_iterate Φ₀_down T2_down (OpTabN.ctxClosed_of_fin T2_fin _) QZ_down rfl (I := IA)
    (en := tickEnt) (by simp [T2, T1, FileProg.divEff_ne6]) rfl rfl
    (fun _ _ => ⟨rfl, rfl⟩) (fun _ _ _ _ h => h) IA_closed
    (fun k s ls ρ hI => turnA_ok Φ₀_down A k s ls ρ hI) _ _ _ _
    ⟨c, d, Val.i32 1, rfl, ResU.CompS.comm hcc'⟩

theorem progAnti_ok (n : Nat) :
    erwp (ℍ := ℍ) Φ₀ (opTableN OpTabN.empty) QZ n [] progAnti (PMap.empty : WRes) :=
  erwp_rtH Φ₀_down n [] _ _ (erwp_yH Φ₀_down n [] _ _ (bodyA_ok 0 n))

/-- **The test.** On every turn of a loop with no bound, a value with a boxed field is lent
`mut` to a method, which opens the borrow, lends the field `mut` and holds that borrow across
`y`, under a scheduler that stores the continuation in a cell and resumes it, under the
runtime's `Div` handler: every configuration a run reaches is a value or steps, a value only at
the empty memory, and every `free` finds its cell. No fuel. -/
theorem progAnti_orDiverges : OrDiverges (ℍ := ℍ) progAnti :=
  erwp_adequacy (Φ := Φ₀) (fun _ _ _ _ h => h) progAnti_ok

/-- `erwp_withbor3`'s added hypotheses hold together: at `T2`, with the integer family at both
lifetimes. -/
theorem withbor3_hyps (α β : Life) :
    T2.LendOK α ∧ T2.AFOK ∧ ∀ k v χ (h : χ.InStratum α), famF α k v ⟨χ, h⟩ →
      ∃ h' : χ.InStratum β, famF β k v ⟨χ, h'⟩ := by
  refine ⟨T2_lendOK α, T2_afOK, fun k v χ h hF => ?_⟩
  have hχ : χ = PMap.empty := hF
  subst hχ
  exact ⟨inStratum_empty β, rfl⟩

end BoCa.Fig16.LogRel.Core.Chain.SI.AntiLendProg

end
