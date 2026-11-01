import DtorUnwind.SI.LendProg
import DtorUnwind.SI.ForestN

/-!
# The forest test: a `mut` lend live across a `yield`, the continuation resumed at `ExtK`

`SI/LendProg.lean`'s program, unchanged, with both operations' world condition `ExtK A` (the
continuation's stack holds the lend at `A`) in place of `sameW`, and the lend taken by
`erwp_M_frameK`. The scheduler stores `κ` in a cell, takes it back and resumes it; the loop has
no bound; the runtime answers every tick. `progLendK_orDiverges`: `OrDiverges`, no fuel.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core.DtorUnwind.SI.ForestLendProg
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.DtorUnwind.SI
open BoCa.Fig16.LogRel.Core.DtorUnwind.SI.LendProg
open BoCa.BoLo (Heap Step1 Steps Head Kont performE raiseE cancelVal opPayload freeE hndE hndVal
  clauseAt capTag)

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

/-- `tick : 1 ↠^lin Next`, resumed at `ExtK A`. -/
def tickEntK (A : Life) : OpEntN := ⟨.lin, false, unitP, nextP, none, ExtK A⟩

/-- `y : 1 ↠^lin 1`, resumed at `ExtK A`. -/
def yEntK (A : Life) : OpEntN := ⟨.lin, false, unitP, unitP, none, ExtK A⟩

def T1K (A : Life) : OpTabN := fun m i => if m = divEff ∧ i = 0 then some (tickEntK A) else none

def T2K (A : Life) : OpTabN := fun m i => if m = 6 ∧ i = 0 then some (yEntK A) else T1K A m i

theorem T1K_cases {A : Life} {m i : UInt32} {en : OpEntN} (h : T1K A m i = some en) :
    m = divEff ∧ i = 0 ∧ en = tickEntK A := by
  unfold T1K at h
  split_ifs at h with h₁
  · exact ⟨h₁.1, h₁.2, (Option.some.inj h).symm⟩

theorem T2K_cases {A : Life} {m i : UInt32} {en : OpEntN} (h : T2K A m i = some en) :
    (m = 6 ∧ i = 0 ∧ en = yEntK A) ∨ (m = divEff ∧ i = 0 ∧ en = tickEntK A) := by
  unfold T2K at h
  split_ifs at h with h₁
  · exact .inl ⟨h₁.1, h₁.2, (Option.some.inj h).symm⟩
  · exact .inr (T1K_cases h)

theorem entK_cases {A : Life} {m i : UInt32} {en : OpEntN} (h : T2K A m i = some en) :
    en = yEntK A ∨ en = tickEntK A := by
  rcases T2K_cases h with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩
  · exact .inl rfl
  · exact .inr rfl

theorem T2K_down (A : Life) : (T2K A).Down where
  pa := fun _ _ en h _ _ _ _ hA => by rcases entK_cases h with he | he <;> subst he <;> exact hA
  fin := fun _ _ en P h hP => by rcases entK_cases h with rfl | rfl <;> cases hP
  wcl := fun _ _ en h => by rcases entK_cases h with rfl | rfl <;> exact extK_left

theorem T1K_down (A : Life) : (T1K A).Down where
  pa := fun _ _ en h _ _ _ _ hA => by obtain ⟨-, -, rfl⟩ := T1K_cases h; exact hA
  fin := fun _ _ en P h hP => by rw [(T1K_cases h).2.2] at hP; cases hP
  wcl := fun _ _ en h => by rw [(T1K_cases h).2.2]; exact extK_left

theorem T2K_fin (A : Life) : ∀ m i en, T2K A m i = some en → en.fin = none := fun _ _ en h => by
  rcases entK_cases h with rfl | rfl <;> rfl

/-- **`T2K A` may be stopped at under a live lend at `A`**, its continuations resumed at
`ExtK A`. -/
theorem T2K_lendOKK (A : Life) : (T2K A).LendOKK A where
  entry := fun _ _ en h => by
    rcases entK_cases h with rfl | rfl <;> exact ⟨rfl, rfl, wcUnfold_extK le_rfl⟩
  pa := fun _ _ en h _ _ _ ρ hA => by
    rcases entK_cases h with rfl | rfl <;>
    · obtain ⟨-, rfl⟩ := hA
      intro l ψ hl; simp at hl
  pb := fun _ _ en h _ _ _ ρ hB => by
    rcases entK_cases h with rfl | rfl <;>
    · obtain ⟨-, rfl⟩ := hB
      intro l ψ hl; simp at hl

/-! ### The handlers: both resume at the list they were handed -/

theorem erwp_yHK {Φ : LocFam} (hΦ : Φ.Down) (A : Life) :
    ∀ n ls e ρ, erwp (ℍ := ℍ) Φ (opTableN (T2K A)) QZ n ls e ρ →
      erwp (ℍ := ℍ) Φ (opTableN (T1K A)) QZ n ls (hndE yH e) ρ := by
  refine erwp_handle hΦ (T2K A) (T1K A) (T2K_down A) (T1K_down A) 6
    (fun m i hm => by simp [T2K, hm]) _ _ _ QZ QZ
    QZ_down ?_ (fun _ => none) (fun _ en _ _ hq' _ hTk => by cases hTk)
    (fun k ls v ρ hv => erwp_idV hΦ (T1K_down A) hv) ?_
  · intro i en hT _
    rcases T2K_cases hT with ⟨-, rfl, rfl⟩ | ⟨h6, -, -⟩
    · exact Stage1.capTag_one .lin
    · exact absurd h6.symm Stage1.divEff_ne6
  · intro i en hT
    rcases T2K_cases hT with ⟨-, rfl, rfl⟩ | ⟨h6, -, -⟩
    · refine ⟨Stage1.clStore, Stage1.clauseAt_pair0 _ _, fun _ k ls v κ ρ hsep => ?_,
        fun h => by cases h⟩
      obtain ⟨ρa, ρk, hc, ⟨-, rfl⟩, -, hK⟩ := hsep
      obtain rfl : ρ = ρk := eq_of_compS_empty_left hc
      refine erwp_clStore hΦ (T1K_down A) QZ_down fun k' hk' => ?_
      exact (hK ls (extK_of_same (fun _ => Iff.rfl) ρ) k' hk').1 Val.unit PMap.empty ρ
        ⟨rfl, rfl⟩ (ResU.comp_empty_right ρ)
    · exact absurd h6.symm Stage1.divEff_ne6

theorem erwp_rtHK {Φ : LocFam} (hΦ : Φ.Down) (A : Life) :
    ∀ n ls e ρ, erwp (ℍ := ℍ) Φ (opTableN (T1K A)) QZ n ls e ρ →
      erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) QZ n ls (hndE DivRuntime.rtH e) ρ := by
  refine erwp_handle hΦ (T1K A) OpTabN.empty (T1K_down A) empty_down divEff
    (fun m i hm => by simp [T1K, hm, OpTabN.empty]) _ _ _ QZ QZ QZ_down ?_ (fun _ => none)
    (fun _ en _ _ hq' _ hTk => by cases hTk)
    (fun k ls v ρ hv => erwp_idV hΦ empty_down hv) ?_
  · intro i en hT _
    obtain ⟨-, rfl, rfl⟩ := T1K_cases hT
    exact Stage1.capTag_one .lin
  · intro i en hT
    obtain ⟨-, rfl, rfl⟩ := T1K_cases hT
    refine ⟨DivRuntime.rtC, Stage1.clauseAt_pair0 _ _, fun _ k ls v κ ρ hsep => ?_,
      fun h => by cases h⟩
    obtain ⟨ρa, ρk, hc, ⟨-, rfl⟩, -, hK⟩ := hsep
    obtain rfl : ρ = ρk := eq_of_compS_empty_left hc
    rw [Stage1.rtC_eq]
    refine erwp_resumeCl hΦ empty_down QZ_down nextV_closed fun k' hk' => ?_
    exact (hK ls (extK_of_same (fun _ => Iff.rfl) ρ) k' hk').1 nextV PMap.empty ρ ⟨rfl, rfl⟩
      (ResU.comp_empty_right ρ)

/-! ### The turn -/

/-- The borrowed computation `y (); ℓ := 5` (`lend_ok` at `T2K A`). -/
theorem lend_okK {Φ : LocFam} (hΦ : Φ.Down) (l : Loc) (A : Life) (u : Val) (k : Nat)
    (ls : List SRec) (BM : WRes)
    (hBM : ResU.CompS PMap.empty (ResU.single l (CellU.mutOf A u PMap.empty (inStratum_empty A)
      (famF A k) rfl)) BM) :
    erwp (ℍ := ℍ) (Φ.set l A (famF A)) (opTableN (T2K A)) (MFPost l A (famF A) (Qlend l)) k ls
      (lendE l) BM := by
  have hΦ' := LocFam.set_down (l := l) hΦ (famF_down A)
  have hFl : Φ.set l A (famF A) l = some ⟨A, famF A⟩ := by simp [LocFam.set]
  obtain rfl := eq_of_compS_empty_left hBM
  refine erwp_perform (T := T2K A) (en := yEntK A) (K := .seq .hole (wrL l))
    (by simp [Kont.HasHnd]) (by simp [T2K]) rfl rfl
    (compS_empty_left _) ⟨rfl, rfl⟩ (fun ls' _ k' hk' w σB XB hB hXB => ?_)
  obtain ⟨rfl, rfl⟩ := hB
  obtain rfl := ResU.CompS.functional hXB (ResU.comp_empty_right _)
  cases k' with
  | zero => exact erwp_zero
  | succ k₀ =>
  refine erwp_step (opTableN_local (T2K A)) (fun μ => step1Only_plug (Head.seq μ _) rfl .hole) ?_
  refine erwp_of_rwp (rwp_dump (rwp_M_antiFrame hΦ' hFl (ResU.comp_empty_right _) ?_))
  intro W X hW hX
  obtain rfl := eq_of_compS_empty_left hW
  obtain rfl := eq_of_compS_empty_left hX
  refine rwp_store ls' l u (Val.i32 5) _ ⟨_, PMap.empty, ResU.comp_empty_right _, rfl, ?_⟩
  intro ρ₁ ρ₂ h₁ hc
  subst h₁
  obtain rfl := eq_of_compS_empty_left hc
  refine ⟨Val.i32 5, PMap.empty, inStratum_empty A, rfl, PMap.empty, PMap.empty,
    ResU.comp_empty_right _, ResU.comp_empty_right _, fun X hX => ?_⟩
  obtain rfl := eq_of_compS_empty_left hX
  refine ⟨noOwn_single_mut l, inStratum_empty A, fun w Y hY σ ⟨hσ, hF⟩ Z hZ => ?_⟩
  have hσ0 : σ = PMap.empty := hF
  subst hσ0
  obtain rfl := eq_of_compS_empty_left hY
  obtain rfl := ResU.CompS.functional hZ (ResU.comp_empty_right _)
  exact ⟨rfl, w, rfl⟩

/-- **A turn**, the lend by `erwp_M_frameK`. -/
theorem turn_okK {Φ : LocFam} (hΦ : Φ.Down) (A : Life) (k : Nat) (s : Val) (ls : List SRec)
    (ρ : WRes) (hI : IL s ρ) :
    erwp (ℍ := ℍ) Φ (opTableN (T2K A)) (turnPostN IL QZ) k ls
      (.app (.app (.val fT) (.val s)) (.val nextV)) ρ := by
  obtain ⟨l, u, rfl, rfl⟩ := hI
  have hD := opTableN_down (T2K_down A)
  have hTP : (turnPostN IL QZ).Down := fun _ _ _ _ h => by
    rcases h with ⟨x, hx, hq⟩ | h
    · exact .inl ⟨x, hx, hq⟩
    · exact .inr h
  refine erwp_det hΦ hD hTP
    (fun μ => step1Only_plug (Head.beta μ _ (Val.loc l)) rfl (.appL .hole nextV)) ?_
  have e₁ : (Kont.appL .hole nextV).plug (Expr.subst 0 (Val.loc l)
      (.lam (.case (.var 0) (.seq (.seq Stage1.yE wrE) (.inj₂ (.var 2))) (.val .unit)))) =
      Kont.hole.plug (.app (.val (Val.lam (.case (.var 0)
        (.seq (.seq Stage1.yE (wrL l)) (.inj₂ (.val (Val.loc l)))) (.val .unit)))) (.val nextV)) := by
    simp [Expr.subst, Expr.shift, Kont.plug, Stage1.yE, wrE, wrL, performE, opPayload, Val.pair,
      Val.i32, Val.unit, Val.lam, Val.loc, Val.storeV, Expr.val, Val.prim, Val.shift]
  rw [e₁]
  refine erwp_det hΦ hD hTP (fun μ => step1Only_plug (Head.beta μ _ nextV) rfl .hole) ?_
  have e₂ : Kont.hole.plug (Expr.subst 0 nextV (.case (.var 0)
        (.seq (.seq Stage1.yE (wrL l)) (.inj₂ (.val (Val.loc l)))) (.val .unit))) =
      Kont.hole.plug (.case (.val (Val.inj₁ Val.unit))
        (.seq (.seq Stage1.yE (wrL l)) (.inj₂ (.val (Val.loc l)))) (.val .unit)) := by
    simp [Expr.subst, Kont.plug, Stage1.yE, wrL, performE, opPayload, Val.pair, Val.i32,
      Val.unit, nextV, Val.inj₁, Val.loc, Val.storeV, Expr.val, Val.prim]
  rw [e₂]
  refine erwp_det hΦ hD hTP (fun μ => step1Only_plug (Head.case₁ μ Val.unit _ _) rfl .hole) ?_
  have e₃ : Kont.hole.plug (Expr.subst 0 Val.unit
        (.seq (.seq Stage1.yE (wrL l)) (.inj₂ (.val (Val.loc l))))) =
      (Kont.seq .hole (.inj₂ (.val (Val.loc l)))).plug (lendE l) := by
    simp [Expr.subst, Kont.plug, Stage1.yE, wrL, lendE, performE, opPayload, Val.pair, Val.i32,
      Val.unit, Val.loc, Val.storeV, Expr.val, Val.prim]
  rw [e₃]
  refine erwp_bind_le (Q' := Qlend l) hΦ _ (fun m => by simp [Kont.HasHnd])
    (fun m => by simp [Kont.Catches]) (OpTabN.ctxClosed_of_fin (T2K_fin A) _) k ?_ k le_rfl ls _ _ ?_
  · rintro k' ls' v σ - ⟨rfl, w, rfl⟩
    refine erwp_det hΦ hD hTP (fun μ => step1Only_plug (Head.seq μ _) rfl .hole) ?_
    exact erwp_val (v := Val.inj₂ (Val.loc l)) (.inr ⟨Val.loc l, rfl, l, w, rfl, rfl⟩)
  · exact erwp_M_frameK (famF_down A) (T2K_lendOKK A) k k le_rfl ls (lendE l) u PMap.empty _
      PMap.empty _ (inStratum_empty A) (inStratum_empty _) (famF A k) (fun _ _ h => h) rfl
      (ResU.comp_empty_right _) (ResU.comp_empty_right _) (lend_okK hΦ l A u k ls)

/-! ### The program -/

theorem body_okK (A : Life) (n : Nat) :
    erwp (ℍ := ℍ) Φ₀ (opTableN (T2K A)) QZ n [] LendProg.bodyL (PMap.empty : WRes) := by
  have hD := opTableN_down (T2K_down A)
  refine erwp_alloc Φ₀_down (opTableN_local (T2K A)) (.appR (.val (Val.lam
    (.app (.val (.prim .iterate)) (.pair (.val fT) (.var 0))))) .hole) (Val.i32 1)
    (fun l σ₁ σ₂ hcell hc => ?_)
  obtain rfl := eq_of_compS_empty_left hc
  refine erwp_det Φ₀_down hD QZ_down (fun μ => step1Only_plug (Head.beta μ _ _) rfl .hole) ?_
  have e : Kont.hole.plug (Expr.subst 0 (Val.loc l)
      (.app (.val (.prim .iterate)) (.pair (.val fT) (.var 0)))) = iterateE fT (Val.loc l) := by
    simp [Expr.subst, Kont.plug, iterateE, Val.pair, Val.loc, Expr.val, Val.prim,
      subst_closedAt _ _ (show closedAt 0 fT.1 = true from rfl) (Nat.zero_le _)]
  rw [e]
  exact erwp_iterate Φ₀_down (T2K_down A) (OpTabN.ctxClosed_of_fin (T2K_fin A) _) QZ_down rfl
    (I := IL) (en := tickEntK A)
    (by simp [T2K, T1K, Stage1.divEff_ne6]) rfl rfl
    (fun _ _ => ⟨rfl, rfl⟩) (fun _ _ _ _ h => h) IL_closed
    (fun k s ls ρ hI => turn_okK Φ₀_down A k s ls ρ hI) _ _ _ _ ⟨l, Val.i32 1, rfl, hcell⟩

theorem progLendK_ok (A : Life) (n : Nat) :
    erwp (ℍ := ℍ) Φ₀ (opTableN OpTabN.empty) QZ n [] LendProg.progLend (PMap.empty : WRes) :=
  erwp_rtHK Φ₀_down A n [] _ _ (erwp_yHK Φ₀_down A n [] _ _ (body_okK A n))

/-- **The forest test.** `progLend`, the lend across `y` taken with its continuations resumed
at `ExtK A` (no `sameW`): every configuration a run reaches is a value or steps, a value only at
the empty memory, and every `free` finds its cell. No fuel. -/
theorem progLendK_orDiverges : LoopAwait.OrDiverges (ℍ := ℍ) LendProg.progLend :=
  erwp_adequacy (Φ := Φ₀) (fun _ _ _ _ h => h) (progLendK_ok (OrderDual.toDual 3))

end BoCa.Fig16.LogRel.Core.DtorUnwind.SI.ForestLendProg

end
