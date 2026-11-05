import Core.Chain.SI.IStopN
import Core.Chain.SI.LendProg

/-!
# The test: an `imm` lend live across a `yield`, under a scheduler that stores `κ`, around a
loop with no bound — `OrDiverges`, with no fuel

    progILend = hnd_Div rtH (hnd_Y yStore (λc. iterate (fI, c)) (alloc ()))

    fI = λs. λb. case b { next → (y (); !s); inr s | close → () }

Each turn lends the cell `imm` to `y (); !s`: the lend is live across `y`, whose `κ` the
scheduler stores in a cell, takes back and resumes; after the resume the borrow reads, and the
lend ends. The lend is the logical Imm Frame (`erwp_I_frame`, `SI/IStopN.lean`), entered at a
lifetime below every record of the turn's list; the term is not cut at the `y`.
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
  clauseAt capTag)
open BoCa.Lifetime (LSub)

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

/-- **`T2` may be stopped at under a live `imm` lend at any lifetime.** -/
theorem T2_ilendOK (A : Life) : T2.ILendOK A where
  entry := (T2_lendOK A).entry
  pa := fun _ _ en h _ _ _ ρ hA => by
    rcases ent_cases h with rfl | rfl <;>
    · obtain ⟨-, rfl⟩ := hA
      intro l ψ hl; simp at hl
  pb := fun _ _ en h _ _ _ ρ hB => by
    rcases ent_cases h with rfl | rfl <;>
    · obtain ⟨-, rfl⟩ := hB
      intro l ψ hl; simp at hl
  paExt := fun _ _ en h _ _ _ _ _ _ hA => by rcases ent_cases h with rfl | rfl <;> exact hA
  pbExt := fun _ _ en h _ _ _ _ _ _ hB => by rcases ent_cases h with rfl | rfl <;> exact hB

/-- The empty lifetime substitution. -/
def δ₀ : LSub := ⟨[]⟩

/-- The loop's invariant: the state is a location the turn owns, holding `()`. -/
def ILU : Val → WProp := fun s ρ => ∃ l, s = Val.loc l ∧ ptoOwn l Val.unit ρ

theorem ILU_closed : ∀ s ρ, ILU s ρ → closedAt 0 s.1 = true := by
  rintro s ρ ⟨l, rfl, -⟩
  rfl

/-- The lent cell's payload: owning nothing, at type `unk`. -/
def PU : List SRec → Val → WProp := fun _ _ ρ => ρ = PMap.empty

/-- The lend's end: the cell owned again. -/
def Qown (l : Loc) : PostN := fun _ _ w ρ => w = Val.unit ∧ ptoOwn l Val.unit ρ

/-- `!ℓ`. -/
def ldL (l : Loc) : Expr := .app (.val (.prim .load)) (.val (Val.loc l))

/-- The lent computation: `y (); !ℓ`. -/
def lendIE (l : Loc) : Expr := .seq FileProg.yE (ldL l)

/-- **The borrowed computation**: from the borrow alone, `y ()` stops with the borrow in its
continuation's share; after the resume the borrow reads (6.143 at the index) and is released. -/
theorem lendI_ok {Φ : LocFam} (l : Loc) (A : Life) (k : Nat)
    (ls : List SRec) (BI : WRes)
    (hBI : ResU.CompS PMap.empty (ResU.single l (CellU.immOf (LSet.singleton A) Val.unit PMap.empty
      (inStratum_empty A))) BI) :
    erwp (ℍ := ℍ) Φ (opTableN T2) (IFPost l Val.unit PU A (Qown l)) k ls (lendIE l) BI := by
  obtain rfl := eq_of_compS_empty_left hBI
  refine erwp_perform (T := T2) (en := yEnt) (K := .seq .hole (ldL l)) (by simp [Kont.HasHnd])
    (by simp [T2]) rfl rfl (compS_empty_left _) ⟨rfl, rfl⟩
    (fun ls' _ k' hk' w σB XB hB hXB => ?_)
  obtain ⟨rfl, rfl⟩ := hB
  obtain rfl := ResU.CompS.functional hXB (ResU.comp_empty_right _)
  cases k' with
  | zero => exact erwp_zero
  | succ k₀ =>
  refine erwp_step (opTableN_local T2) (fun μ => step1Only_plug (Head.seq μ _) rfl .hole) ?_
  refine erwp_of_rwp (rwp_dump (rwp_load_I ls' l A (fun w _ => w = Val.unit) _ ⟨_, PMap.empty,
    ResU.comp_empty_right _, ⟨LSet.singleton A, Val.unit, PMap.empty, inStratum_empty A, rfl, rfl,
      le_refl _⟩, fun w ρc X hc hX => ?_⟩))
  obtain rfl := eq_of_compS_empty_left hX
  obtain ⟨s, u', σ, hs, rfl, ⟨-, -, -, -, hw⟩, -⟩ := hc
  refine ⟨noOwn_single_imm l _ _ _ _, fun ρl Y hl hY ρv Z hv hZ => ?_, inStratum_empty A⟩
  subst hl
  obtain rfl := eq_of_compS_empty_left hY
  have hv' : ρv = PMap.empty := hv
  subst hv'
  obtain rfl := ResU.CompS.functional hZ (ResU.comp_empty_right _)
  exact ⟨hw, rfl⟩

/-- `λs. λb. case b {next → (y (); !s); inr s | close → ()}`. -/
def fI : Val :=
  Val.lam (.lam (.case (.var 0) (.seq (.seq FileProg.yE
    (.app (.val (.prim .load)) (.var 2))) (.inj₂ (.var 2))) (.val .unit)))

/-- **A turn**: three steps to `(y (); !ℓ); inr ℓ`, the lend by `erwp_I_frame` around
`y (); !ℓ` at a lifetime below the list's records, then `inr ℓ`. -/
theorem turnI_ok {Φ : LocFam} (hΦ : Φ.Down) (k : Nat) (s : Val) (ls : List SRec)
    (ρ : WRes) (hI : ILU s ρ) :
    erwp (ℍ := ℍ) Φ (opTableN T2) (turnPostN ILU QZ) k ls
      (.app (.app (.val fI) (.val s)) (.val nextV)) ρ := by
  obtain ⟨l, rfl, rfl⟩ := hI
  set u : Val := Val.unit
  have hD := opTableN_down T2_down
  have hTP : (turnPostN ILU QZ).Down := fun _ _ _ _ h => by
    rcases h with ⟨x, hx, hq⟩ | h
    · exact .inl ⟨x, hx, hq⟩
    · exact .inr h
  refine erwp_det hΦ hD hTP
    (fun μ => step1Only_plug (Head.beta μ _ (Val.loc l)) rfl (.appL .hole nextV)) ?_
  have e₁ : (Kont.appL .hole nextV).plug (Expr.subst 0 (Val.loc l)
      (.lam (.case (.var 0) (.seq (.seq FileProg.yE (.app (.val (.prim .load)) (.var 2)))
        (.inj₂ (.var 2))) (.val .unit)))) =
      Kont.hole.plug (.app (.val (Val.lam (.case (.var 0)
        (.seq (.seq FileProg.yE (ldL l)) (.inj₂ (.val (Val.loc l)))) (.val .unit)))) (.val nextV)) := by
    simp [Expr.subst, Expr.shift, Kont.plug, FileProg.yE, ldL, performE, opPayload, Val.pair,
      Val.i32, Val.unit, Val.lam, Val.loc, Expr.val, Val.prim, Val.shift]
  rw [e₁]
  refine erwp_det hΦ hD hTP (fun μ => step1Only_plug (Head.beta μ _ nextV) rfl .hole) ?_
  have e₂ : Kont.hole.plug (Expr.subst 0 nextV (.case (.var 0)
        (.seq (.seq FileProg.yE (ldL l)) (.inj₂ (.val (Val.loc l)))) (.val .unit))) =
      Kont.hole.plug (.case (.val (Val.inj₁ Val.unit))
        (.seq (.seq FileProg.yE (ldL l)) (.inj₂ (.val (Val.loc l)))) (.val .unit)) := by
    simp [Expr.subst, Kont.plug, FileProg.yE, ldL, performE, opPayload, Val.pair, Val.i32,
      Val.unit, nextV, Val.inj₁, Val.loc, Expr.val, Val.prim]
  rw [e₂]
  refine erwp_det hΦ hD hTP (fun μ => step1Only_plug (Head.case₁ μ Val.unit _ _) rfl .hole) ?_
  have e₃ : Kont.hole.plug (Expr.subst 0 Val.unit
        (.seq (.seq FileProg.yE (ldL l)) (.inj₂ (.val (Val.loc l))))) =
      (Kont.seq .hole (.inj₂ (.val (Val.loc l)))).plug (lendIE l) := by
    simp [Expr.subst, Kont.plug, FileProg.yE, ldL, lendIE, performE, opPayload, Val.pair, Val.i32,
      Val.unit, Val.loc, Expr.val, Val.prim]
  rw [e₃]
  refine erwp_bind_le (Q' := Qown l) hΦ _ (fun m => by simp [Kont.HasHnd])
    (fun m => by simp [Kont.Catches]) (OpTabN.ctxClosed_of_fin T2_fin _) k ?_ k le_rfl ls _ _ ?_
  · rintro k' ls' v σ - ⟨hv, rfl⟩
    obtain rfl : v = Val.unit := hv
    refine erwp_det hΦ hD hTP (fun μ => step1Only_plug (Head.seq μ _) rfl .hole) ?_
    exact erwp_val (v := Val.inj₂ (Val.loc l)) (.inr ⟨Val.loc l, rfl, l, rfl, rfl⟩)
  · -- the lend, at a lifetime below every record of the list
    obtain ⟨A, -⟩ := exists_fresh ls
    have hshape : vShape .unk δ₀ u (PMap.empty : WRes) := ⟨rfl, trivial⟩
    have hadm : AdmWf .unk δ₀ := fun _ h => h.elim
    obtain ⟨ds, hds⟩ := lineage_list (r := ⟨l, u, PMap.empty, .unk, δ₀⟩) hshape hadm
      (ExW.empty_of_all_imm (fun _ _ h => by simp at h))
    exact erwp_I_frame l .unk δ₀ hadm u PU (fun _ ρ h => ⟨h, trivial⟩)
      (fun _ _ _ _ h => h) (T2_ilendOK A) (fun _ _ _ _ _ _ h => h) k ls (lendIE l)
      PMap.empty _ PMap.empty _ (inStratum_empty A) (inStratum_empty A) rfl
      (ResU.comp_empty_right _) (ResU.comp_empty_right _) ds hds
      (lendI_ok l A k _)

/-! ### The program -/

/-- `(λc. iterate (fI, c)) (alloc ())`. -/
def bodyI : Expr :=
  .app (.val (Val.lam (.app (.val (.prim .iterate)) (.pair (.val fI) (.var 0)))))
    (.app (.val (.prim .alloc)) (.val Val.unit))

/-- `hnd_Div rtH (hnd_Y yStore bodyI)`. -/
def progILend : Expr := hndE DivRuntime.rtH (hndE yH bodyI)

theorem bodyI_ok (n : Nat) :
    erwp (ℍ := ℍ) Φ₀ (opTableN T2) QZ n [] bodyI (PMap.empty : WRes) := by
  have hD := opTableN_down T2_down
  refine erwp_alloc Φ₀_down (opTableN_local T2) (.appR (.val (Val.lam
    (.app (.val (.prim .iterate)) (.pair (.val fI) (.var 0))))) 
    .hole) Val.unit (fun l σ₁ σ₂ hcell hc => ?_)
  obtain rfl := eq_of_compS_empty_left hc
  refine erwp_det Φ₀_down hD QZ_down (fun μ => step1Only_plug (Head.beta μ _ _) rfl .hole) ?_
  have e : Kont.hole.plug (Expr.subst 0 (Val.loc l)
      (.app (.val (.prim .iterate)) (.pair (.val fI) (.var 0)))) = iterateE fI (Val.loc l) := by
    simp [Expr.subst, Kont.plug, iterateE, Val.pair, Val.loc, Expr.val, Val.prim,
      subst_closedAt _ _ (show closedAt 0 fI.1 = true from rfl) (Nat.zero_le _)]
  rw [e]
  exact erwp_iterate Φ₀_down T2_down (OpTabN.ctxClosed_of_fin T2_fin _) QZ_down rfl (I := ILU)
    (en := tickEnt) (by simp [T2, T1, FileProg.divEff_ne6]) rfl rfl
    (fun _ _ => ⟨rfl, rfl⟩) (fun _ _ _ _ h => h) ILU_closed
    (fun k s ls ρ hI => turnI_ok Φ₀_down k s ls ρ hI) _ _ _ _ ⟨l, rfl, hcell⟩

theorem progILend_ok (n : Nat) :
    erwp (ℍ := ℍ) Φ₀ (opTableN OpTabN.empty) QZ n [] progILend (PMap.empty : WRes) :=
  erwp_rtH Φ₀_down n [] _ _ (erwp_yH Φ₀_down n [] _ _ (bodyI_ok n))

/-- **The `imm` test.** A cell lent `imm` across `y` on every turn of a loop with no bound,
under a scheduler that stores the continuation in a cell and resumes it, under the runtime's
`Div` handler: every configuration a run reaches is a value or steps, a value only at the empty
memory, and every `free` finds its cell. No fuel. -/
theorem progILend_orDiverges : OrDiverges (ℍ := ℍ) progILend :=
  erwp_adequacy (Φ := Φ₀) (fun _ _ _ _ h => h) progILend_ok

end BoCa.Fig16.LogRel.Core.Chain.SI.ILendProg

end
