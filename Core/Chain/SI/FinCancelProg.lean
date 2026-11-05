import Core.Chain.SI.FinCancelN
import Core.Chain.SI.AntiStopN
import Core.Chain.SI.LendCancelProg
import Core.Chain.SI.RaiseFinProg

/-!
# The test: a finaliser that performs, on the cancel path

    progCancelC = hnd_Div rtH (hnd_C cH (hnd_Y yCancel (
                    (λc. ubind (dC c, dC c) (iterate (fT, c))) (alloc 1))))

    dC c = (λ_. (λ_. ()) (free c)) (close ())        cH: close ↦ λ(v, κ). κ ()

`LendCancelProg`'s program with `RaiseFinProg`'s finaliser: each turn lends the cell `mut` across
a cancellable `y`; the scheduler stores the first `κ` and cancels it; the cancel run unwinds
through the lend (its cancel run ends carrying the lend's claim) to the finaliser frame, where
`cfin cancel (dC c ())` runs: the finaliser performs `close`, which the handler outside the
scheduler resumes, frees the cell, and the cancel goes on (`erwp_ubindClaimF`). `y`'s cancel
row records `close` (`cancelOblN Φ₀ TCl`).
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core.Chain.SI.FinCancelProg
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel.Core.Chain.SI.LendProg
open BoCa.Fig16.LogRel.Core.Chain.SI.RaiseLendProg
open BoCa.BoLo (Heap Step1 Steps Head Kont performE raiseE cancelVal opPayload freeE hndE hndVal
  clauseAt capTag ubindE)

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

/-! ### The tables -/

/-- The cancel run's table: `close`. -/
def TCl : OpTabN := fun m i => if m = 8 ∧ i = 0 then some cEnt else none

/-- `y : 1 ↠^cancel 1`, its cancel run at `TCl`. -/
def yCC : OpEntN := ⟨.cancel, false, unitP, unitP, some (cancelOblN (ℍ := ℍ) Φ₀ TCl), extF⟩

/-- Under `cH`: `close` and the tick. -/
def T1C : OpTabN := fun m i => if m = 8 ∧ i = 0 then some cEnt else T1 m i

/-- Under the scheduler: `y`, `close` and the tick. -/
def T2CC : OpTabN := fun m i => if m = 6 ∧ i = 0 then some (yCC (ℍ := ℍ)) else T1C m i

theorem TCl_ent {m i : UInt32} {en : OpEntN} (h : TCl m i = some en) :
    m = 8 ∧ i = 0 ∧ en = cEnt := by
  unfold TCl at h
  split_ifs at h with h₁
  · exact ⟨h₁.1, h₁.2, (Option.some.inj h).symm⟩

theorem T1C_cases {m i : UInt32} {en : OpEntN} (h : T1C m i = some en) :
    (m = 8 ∧ i = 0 ∧ en = cEnt) ∨ (m = divEff ∧ i = 0 ∧ en = tickEnt) := by
  unfold T1C at h
  split_ifs at h with h₁
  · exact .inl ⟨h₁.1, h₁.2, (Option.some.inj h).symm⟩
  · exact .inr (T1_cases h)

theorem T2CC_cases {m i : UInt32} {en : OpEntN} (h : T2CC (ℍ := ℍ) m i = some en) :
    (m = 6 ∧ i = 0 ∧ en = yCC (ℍ := ℍ)) ∨ (m = 8 ∧ i = 0 ∧ en = cEnt) ∨
      (m = divEff ∧ i = 0 ∧ en = tickEnt) := by
  unfold T2CC at h
  split_ifs at h with h₁
  · exact .inl ⟨h₁.1, h₁.2, (Option.some.inj h).symm⟩
  · exact .inr (T1C_cases h)

theorem T2CC_ent {m i : UInt32} {en : OpEntN} (h : T2CC (ℍ := ℍ) m i = some en) :
    en = yCC (ℍ := ℍ) ∨ en = cEnt ∨ en = tickEnt := by
  rcases T2CC_cases h with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩
  · exact .inl rfl
  · exact .inr (.inl rfl)
  · exact .inr (.inr rfl)

theorem T1C_ent {m i : UInt32} {en : OpEntN} (h : T1C m i = some en) :
    en = cEnt ∨ en = tickEnt := by
  rcases T1C_cases h with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩
  · exact .inl rfl
  · exact .inr rfl

theorem TCl_down : TCl.Down where
  pa := fun _ _ en h _ _ _ _ hA => by obtain ⟨-, -, rfl⟩ := TCl_ent h; exact hA
  fin := fun _ _ en P h hP => by rw [(TCl_ent h).2.2] at hP; cases hP
  wcl := fun _ _ en h => by rw [(TCl_ent h).2.2]; exact extF_left

theorem T1C_down : T1C.Down where
  pa := fun _ _ en h _ _ _ _ hA => by rcases T1C_ent h with rfl | rfl <;> exact hA
  fin := fun _ _ en P h hP => by rcases T1C_ent h with rfl | rfl <;> cases hP
  wcl := fun _ _ en h => by rcases T1C_ent h with rfl | rfl <;> exact extF_left

theorem T2CC_down : (T2CC (ℍ := ℍ)).Down where
  pa := fun _ _ en h _ _ _ _ hA => by
    rcases T2CC_ent h with rfl | rfl | rfl <;> exact hA
  fin := fun _ _ en P h hP => by
    rcases T2CC_ent h with rfl | rfl | rfl
    · cases hP; exact cancelOblN_down Φ₀_down TCl_down
    · cases hP
    · cases hP
  wcl := fun _ _ en h => by rcases T2CC_ent h with rfl | rfl | rfl <;> exact extF_left

theorem TCl_lin : ∀ m i en, TCl m i = some en → en.abort = false ∧ en.q = .lin :=
  fun _ _ en h => by rw [(TCl_ent h).2.2]; exact ⟨rfl, rfl⟩

theorem TCl_lendOK (A : Life) : TCl.LendOK A where
  entry := fun _ _ en h => by rw [(TCl_ent h).2.2]; exact ⟨rfl, rfl, rfl⟩
  pa := fun _ _ en h _ _ _ ρ hA => by
    rw [(TCl_ent h).2.2] at hA; obtain ⟨-, rfl⟩ := hA; exact inStratum_empty A
  pb := fun _ _ en h _ _ _ ρ hB => by
    rw [(TCl_ent h).2.2] at hB; obtain ⟨-, rfl⟩ := hB; exact inStratum_empty _

theorem T2CC_lendOKC (A : Life) : (T2CC (ℍ := ℍ)).LendOKC A where
  entry := fun _ _ en h => by
    rcases T2CC_ent h with rfl | rfl | rfl <;> exact ⟨rfl, by simp [yCC, cEnt, tickEnt], rfl⟩
  pa := fun _ _ en h _ _ _ ρ hA => by
    rcases T2CC_ent h with rfl | rfl | rfl <;>
    · obtain ⟨-, rfl⟩ := hA
      exact inStratum_empty A
  pb := fun _ _ en h _ _ _ ρ hB => by
    rcases T2CC_ent h with rfl | rfl | rfl <;>
    · obtain ⟨-, rfl⟩ := hB
      exact inStratum_empty _

theorem T2CC_fin : ∀ m i en, T2CC (ℍ := ℍ) m i = some en → en.q = .cancel →
    en.fin = some (cancelOblN (ℍ := ℍ) Φ₀ TCl) := fun _ _ en h hq => by
  rcases T2CC_ent h with rfl | rfl | rfl
  · rfl
  · cases hq
  · cases hq

theorem T2CC_finNone : ∀ m i en, T2CC (ℍ := ℍ) m i = some en → en.q ≠ .cancel →
    en.fin = none := fun _ _ en h hq => by
  rcases T2CC_ent h with rfl | rfl | rfl
  · exact absurd rfl hq
  · rfl
  · rfl

theorem T2CC_e : ∀ m i en, T2CC (ℍ := ℍ) m i = some en → en.abort = false ∧ en.q ≠ .unr :=
  fun _ _ en h => by
    rcases T2CC_ent h with rfl | rfl | rfl <;> exact ⟨rfl, by simp [yCC, cEnt, tickEnt]⟩

theorem TCl_sub : TCl.Sub T1C := fun m i en h => by
  obtain ⟨rfl, rfl, rfl⟩ := TCl_ent h
  simp [T1C]

/-- The body's table: `T2CC` with the lend's claim at `ℓ`. -/
abbrev T2LC (A : Life) (l : Loc) : OpTabN :=
  @OpTabN.claimT ℍ _ (T2CC (ℍ := ℍ)) Φ₀ TCl (claimR l A (famF A))

theorem T2LC_down (A : Life) (l : Loc) : (T2LC (ℍ := ℍ) A l).Down where
  pa := fun _ _ en' h _ _ _ _ hA => by
    obtain ⟨en, hT, rfl⟩ := claimT_some h
    by_cases hq : en.q = .cancel
    · rw [if_pos hq] at hA ⊢; exact T2CC_down.pa _ _ en hT _ _ _ _ hA
    · rw [if_neg hq] at hA ⊢; exact T2CC_down.pa _ _ en hT _ _ _ _ hA
  fin := fun _ _ en' P h hP => by
    obtain ⟨en, hT, rfl⟩ := claimT_some h
    by_cases hq : en.q = .cancel
    · rw [if_pos hq] at hP
      cases hP
      exact fun k ls e ρ hk => erwp_le Φ₀_down (cancelTabR_local _ _)
        (cancelTabR_down TCl_down (claimR_down (famF_down A))) falsePost_down
        (Nat.le_succ _) hk
    · rw [if_neg hq] at hP; exact T2CC_down.fin _ _ en _ hT hP
  wcl := fun _ _ en' h => by
    obtain ⟨en, hT, rfl⟩ := claimT_some h
    by_cases hq : en.q = .cancel
    · rw [if_pos hq]; exact T2CC_down.wcl _ _ en hT
    · rw [if_neg hq]; exact T2CC_down.wcl _ _ en hT

theorem T2LC_ctxClosed (A : Life) (l : Loc) (K : Kont) (hH : ∀ m, K.HasHnd m = false)
    (hC : ∀ m, K.Catches m = false) : (T2LC (ℍ := ℍ) A l).CtxClosed K :=
  claimT_ctxClosed Φ₀_down K hH hC T2CC_finNone
    (OpTabN.ctxClosed_of_fin (fun _ _ en h => by rw [(TCl_ent h).2.2]; rfl) K)

/-! ### The lend, the turn -/

/-- **The borrowed computation, `y` cancellable at `TCl`**: `lend_okC` at `T2CC`. -/
theorem lend_okCC (l : Loc) (A : Life) (u : Val) (k : Nat) (ls : List SRec) (BM : WRes)
    (hBM : ResU.CompS PMap.empty (ResU.single l (CellU.mutOf A u PMap.empty (inStratum_empty A)
      (famF A k) rfl)) BM) :
    erwp (ℍ := ℍ) (Φ₀.set l A (famF A)) (opTableN (T2CC (ℍ := ℍ)))
      (MFPost l A (famF A) (Qlend l)) k ls (lendE l) BM := by
  have hΦ' := LocFam.set_down (l := l) Φ₀_down (famF_down A)
  have hFl : Φ₀.set l A (famF A) l = some ⟨A, famF A⟩ := by simp [LocFam.set]
  obtain rfl := eq_of_compS_empty_left hBM
  have hKH : ∀ m, (Kont.seq .hole (wrL l)).HasHnd m = false := fun m => by simp [Kont.HasHnd]
  have hKC : ∀ m, (Kont.seq .hole (wrL l)).Catches m = false := fun m => by simp [Kont.Catches]
  refine erwp_performG (T := T2CC) (en := yCC) (K := .seq .hole (wrL l)) (hKH 6)
    (by simp [T2CC]) rfl (compS_empty_left _) ⟨rfl, rfl⟩ (fun h => by cases h)
    (fun ls' _ k' hk' w σB XB hB hXB => ?_) (fun ls' _ _ P hP => ?_)
  · obtain ⟨rfl, rfl⟩ := hB
    obtain rfl := ResU.CompS.functional hXB (ResU.comp_empty_right _)
    cases k' with
    | zero => exact erwp_zero
    | succ k₀ =>
    refine erwp_step (opTableN_local _) (fun μ => step1Only_plug (Head.seq μ _) rfl .hole) ?_
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
  · cases hP
    show erwp (ℍ := ℍ) Φ₀ (cancelTabN TCl) (fun _ _ _ _ => False) k ls' _ _
    rw [dead_plain _ hKH (hKC 0), erwp_eq]
    exact rwpG_here (final_opPlug (r := true) (payloadName_cancelVal none) (hKC 0))
      (Or.inr (Or.inl ⟨_, none, pure_sep_mk ⟨rfl, hKC 0⟩
        ⟨PMap.empty, _, compS_empty_left _, emp_empty, noOwn_single_mut l⟩⟩))

/-- **A turn**: the lend by `erwp_M_frameC` at `T2CC`, its cancel runs ending at the claim. -/
theorem turn_okCC (A : Life) (l : Loc) (k : Nat) (s : Val) (ls : List SRec) (ρ : WRes)
    (hI : ILl l s ρ) :
    erwp (ℍ := ℍ) Φ₀ (opTableN (T2LC (ℍ := ℍ) A l)) (turnPostN (ILl l) QF) k ls
      (.app (.app (.val fT) (.val s)) (.val nextV)) ρ := by
  obtain ⟨u, rfl, rfl⟩ := hI
  have hD := opTableN_down (T2LC_down (ℍ := ℍ) A l)
  have hTP : (turnPostN (ILl l) QF).Down := fun _ _ _ _ h => by
    rcases h with ⟨x, hx, hq⟩ | h
    · exact .inl ⟨x, hx, hq⟩
    · exact .inr h
  refine erwp_det Φ₀_down hD hTP
    (fun μ => step1Only_plug (Head.beta μ _ (Val.loc l)) rfl (.appL .hole nextV)) ?_
  have e₁ : (Kont.appL .hole nextV).plug (Expr.subst 0 (Val.loc l)
      (.lam (.case (.var 0) (.seq (.seq Stage1.yE wrE) (.inj₂ (.var 2))) (.val .unit)))) =
      Kont.hole.plug (.app (.val (Val.lam (.case (.var 0)
        (.seq (.seq Stage1.yE (wrL l)) (.inj₂ (.val (Val.loc l)))) (.val .unit)))) (.val nextV)) := by
    simp [Expr.subst, Expr.shift, Kont.plug, Stage1.yE, wrE, wrL, performE, opPayload, Val.pair,
      Val.i32, Val.unit, Val.lam, Val.loc, Val.storeV, Expr.val, Val.prim, Val.shift]
  rw [e₁]
  refine erwp_det Φ₀_down hD hTP (fun μ => step1Only_plug (Head.beta μ _ nextV) rfl .hole) ?_
  have e₂ : Kont.hole.plug (Expr.subst 0 nextV (.case (.var 0)
        (.seq (.seq Stage1.yE (wrL l)) (.inj₂ (.val (Val.loc l)))) (.val .unit))) =
      Kont.hole.plug (.case (.val (Val.inj₁ Val.unit))
        (.seq (.seq Stage1.yE (wrL l)) (.inj₂ (.val (Val.loc l)))) (.val .unit)) := by
    simp [Expr.subst, Kont.plug, Stage1.yE, wrL, performE, opPayload, Val.pair, Val.i32,
      Val.unit, nextV, Val.inj₁, Val.loc, Val.storeV, Expr.val, Val.prim]
  rw [e₂]
  refine erwp_det Φ₀_down hD hTP (fun μ => step1Only_plug (Head.case₁ μ Val.unit _ _) rfl .hole) ?_
  have e₃ : Kont.hole.plug (Expr.subst 0 Val.unit
        (.seq (.seq Stage1.yE (wrL l)) (.inj₂ (.val (Val.loc l))))) =
      (Kont.seq .hole (.inj₂ (.val (Val.loc l)))).plug (lendE l) := by
    simp [Expr.subst, Kont.plug, Stage1.yE, wrL, lendE, performE, opPayload, Val.pair, Val.i32,
      Val.unit, Val.loc, Val.storeV, Expr.val, Val.prim]
  rw [e₃]
  refine erwp_bind_le (Q' := Qlend l) Φ₀_down _ (fun m => by simp [Kont.HasHnd])
    (fun m => by simp [Kont.Catches])
    (T2LC_ctxClosed A l _ (fun m => by simp [Kont.HasHnd]) (fun m => by simp [Kont.Catches]))
    k ?_ k le_rfl ls _ _ ?_
  · rintro k' ls' v σ - ⟨rfl, w, rfl⟩
    refine erwp_det Φ₀_down hD hTP (fun μ => step1Only_plug (Head.seq μ _) rfl .hole) ?_
    exact erwp_val (v := Val.inj₂ (Val.loc l)) (.inr ⟨Val.loc l, rfl, w, rfl, rfl⟩)
  · exact erwp_M_frameC (Φ := Φ₀) rfl (famF_down A) (T2CC_lendOKC A) (TCl_lendOK A) T2CC_fin
      k k le_rfl ls (lendE l) u PMap.empty _ PMap.empty _ (inStratum_empty A) (inStratum_empty _)
      (famF A k) (fun _ _ h => h) rfl (ResU.comp_empty_right _) (ResU.comp_empty_right _)
      (lend_okCC l A u k ls)

/-! ### The finaliser, the body -/

/-- **The finaliser at the cancel run's table**: `dC_ok` at `TCl`. -/
theorem dC_okCl (A : Life) (l : Loc) (k : Nat) (ls : List SRec) (ρ : WRes)
    (h : claimR l A (famF A) k ρ) :
    erwp (ℍ := ℍ) Φ₀ (opTableN TCl) (fun _ _ v ρ' => v = Val.unit ∧ ρ' = PMap.empty) k ls
      (.app (.val (dC l)) (.val .unit)) ρ := by
  have hQ : PostN.Down (fun _ _ v ρ' => v = Val.unit ∧ ρ' = PMap.empty) := fun _ _ _ _ h => h
  refine erwp_det Φ₀_down (opTableN_down TCl_down) hQ
    (fun μ => step1Only_plug (Head.beta μ _ Val.unit) rfl .hole) ?_
  have e : Kont.hole.plug (Expr.subst 0 Val.unit (.app (.val (dU l)) closeE)) =
      (Kont.appR (.val (dU l)) .hole).plug (performE (.val (opPayload 8 0 Val.unit))) := by
    simp [Expr.subst, Kont.plug, dU, closeE, freeE, Val.loc, Expr.val, Val.prim, Val.lam,
      Val.unit, performE, opPayload, Val.pair, Val.i32]
  rw [e]
  obtain ⟨w, σ, hσ, hF, hc⟩ := h
  refine erwp_perform (T := TCl) (en := cEnt) (K := .appR (.val (dU l)) .hole)
    rfl (by simp [TCl]) rfl rfl (compS_empty_left _) ⟨rfl, rfl⟩
    (fun ls' _ k' hk' w' σB XB hB hXB => ?_)
  obtain ⟨rfl, rfl⟩ := hB
  obtain rfl := ResU.CompS.functional hXB (ResU.comp_empty_right _)
  exact erwp_of_rwp (dU_ok A l k' ls' _ ⟨w, σ, hσ, hF, hc⟩)

/-- `λc. ubind (dC c, dC c) (iterate (fT, c))`, its body. -/
def bodyCCF : Expr :=
  .app (.app (.val (.prim .ubind))
    (.pair (.val (Val.lam (.app (.val (Val.lam (.app (.val (Val.lam (.val .unit)))
        (freeE (.var 2))))) closeE)))
      (.val (Val.lam (.app (.val (Val.lam (.app (.val (Val.lam (.val .unit)))
        (freeE (.var 2))))) closeE)))))
    (.app (.val (.prim .iterate)) (.pair (.val fT) (.var 0)))

/-- `(λc. ubind (dC c, dC c) (iterate (fT, c))) (alloc 1)`. -/
def bodyCC : Expr :=
  .app (.val (Val.lam bodyCCF)) (.app (.val (.prim .alloc)) (.val (Val.i32 1)))

theorem bodyCCF_subst (l : Loc) :
    Expr.subst 0 (Val.loc l) bodyCCF = ubindE (Val.pair (dC l) (dC l)) (iterateE fT (Val.loc l)) := by
  simp [bodyCCF, dC, dU, closeE, ubindE, Expr.subst, Val.pair, Val.lam, Val.loc, freeE,
    Expr.val, Expr.shift, Val.prim, iterateE, performE, opPayload, Val.i32, Val.unit,
    subst_closedAt _ _ (show closedAt 0 fT.1 = true from rfl) (Nat.zero_le _)]

theorem bodyCC_ok (A : Life) (n : Nat) :
    erwp (ℍ := ℍ) Φ₀ (opTableN (T2CC (ℍ := ℍ))) QZ n [] bodyCC (PMap.empty : WRes) := by
  have hD := opTableN_down (T2CC_down (ℍ := ℍ))
  refine erwp_alloc Φ₀_down (opTableN_local _) (.appR (.val (Val.lam bodyCCF)) .hole) (Val.i32 1)
    (fun l σ₁ σ₂ hcell hc => ?_)
  obtain rfl := eq_of_compS_empty_left hc
  refine erwp_det Φ₀_down hD QZ_down (fun μ => step1Only_plug (Head.beta μ _ _) rfl .hole) ?_
  rw [Kont.plug_hole, bodyCCF_subst]
  refine erwp_ubindClaimF Φ₀_down T2CC_down TCl_down TCl_lin T2CC_e T2CC_fin
    (dC l) (dC l) (dC_okCl A l) QZ_down (Qin := QF) (fun _ _ _ _ h => h.elim) _ _ _ _ ?_
  refine erwp_iterate Φ₀_down (T2LC_down A l)
    (T2LC_ctxClosed A l _ (fun m => by simp [iterK, Kont.HasHnd])
      (fun m => by simp [iterK, Kont.Catches])) QF_down rfl (I := ILl l) (en := tickEnt)
    (by simp [OpTabN.claimT, T2CC, T1C, T1, tickEnt, Stage1.divEff_ne6,
      show divEff ≠ (8 : UInt32) by decide]) rfl rfl
    (fun _ _ => ⟨rfl, rfl⟩) (fun _ _ _ _ h => h) (fun s ρ ⟨_, hs, _⟩ => by subst hs; rfl)
    (fun k s ls ρ hI => turn_okCC A l k s ls ρ hI) _ _ _ _ ⟨Val.i32 1, rfl, hcell⟩

/-! ### The handlers, the program -/

/-- **The scheduler's clause at a table holding the cancel run's**: `erwp_clDrop`, `κ`'s cancel
read at the outer table. -/
theorem erwp_clDropT {Φ : LocFam} (hΦ : Φ.Down) {T : OpTabN} (hTD : T.Down) {k : Nat}
    {ls : List SRec} {v κ : Val} {ρ : WRes}
    (h : ∀ k', k' < k → erwp (ℍ := ℍ) Φ (opTableN T) unitPost k' ls
      (.app κ.1 (.val (Val.inj₂ .unit))) ρ) :
    erwp (ℍ := ℍ) Φ (opTableN T) QZ k ls (.app (.val Stage1.clCancel) (.pair (.val v) κ.1)) ρ := by
  have hL := opTableN_local T
  cases k with
  | zero => exact erwp_zero
  | succ k₀ =>
  refine erwp_storeCl hΦ hTD QZ_down rfl (fun ℓ' σ₁ σ₂ hcell hc => ?_)
  have e : Expr.subst 0 (Val.loc ℓ') (.app (freeE (.var 0)) (.val (Val.inj₂ .unit))) =
      (Kont.appL .hole (Val.inj₂ .unit)).plug (freeE (.val (Val.loc ℓ'))) := by
    simp [Expr.subst, Kont.plug, freeE, Val.inj₂, Val.unit, Val.loc]
  rw [e]
  refine erwp_free hΦ hL _ ℓ' κ ⟨σ₁, ρ, ResU.CompS.comm hc, hcell, ?_⟩
  exact erwp_mono (Q := unitPost) (Q' := QZ) (fun _ _ _ _ h => h.1)
    (fun k ls t Ψ Ψ' ρ hΨ h => hL k ls t Ψ Ψ' ρ hΨ h) _ ls _ ρ (h _ (by omega))

theorem erwp_yHCC :
    ∀ n ls e ρ, erwp (ℍ := ℍ) Φ₀ (opTableN (T2CC (ℍ := ℍ))) QZ n ls e ρ →
      erwp (ℍ := ℍ) Φ₀ (opTableN T1C) QZ n ls (hndE yHC e) ρ := by
  refine erwp_handle Φ₀_down T2CC T1C T2CC_down T1C_down 6 (fun m i hm => by simp [T2CC, hm])
    _ _ _ QZ QZ QZ_down ?_ (fun _ => some T1C) ?_
    (fun k ls v ρ hv => erwp_idV Φ₀_down T1C_down hv) ?_
  · intro i en hT _
    rcases T2CC_cases hT with ⟨-, rfl, rfl⟩ | ⟨h8, -, -⟩ | ⟨h6, -, -⟩
    · exact Stage1.capTag_one .cancel
    · exact absurd h8 (by decide)
    · exact absurd h6.symm Stage1.divEff_ne6
  · intro i en hT _ _ Tk hTk
    cases hTk
    rcases T2CC_cases hT with ⟨-, rfl, rfl⟩ | ⟨h8, -, -⟩ | ⟨h6, -, -⟩
    · exact ⟨TCl, rfl, TCl_sub, T1C_down⟩
    · exact absurd h8 (by decide)
    · exact absurd h6.symm Stage1.divEff_ne6
  · intro i en hT
    rcases T2CC_cases hT with ⟨-, rfl, rfl⟩ | ⟨h8, -, -⟩ | ⟨h6, -, -⟩
    · refine ⟨Stage1.clCancel, Stage1.clauseAt_pair0 _ _, fun _ k ls v κ ρ hsep => ?_,
        fun h => by cases h⟩
      obtain ⟨ρa, ρk, hc, ⟨-, rfl⟩, -, hK⟩ := hsep
      obtain rfl : ρ = ρk := eq_of_compS_empty_left hc
      refine erwp_clDropT Φ₀_down T1C_down fun k' hk' => ?_
      exact (hK ls (extF_refl ls _) k' hk').2 (by simp [yCC]) _ rfl
    · exact absurd h8 (by decide)
    · exact absurd h6.symm Stage1.divEff_ne6

theorem erwp_cHT :
    ∀ n ls e ρ, erwp (ℍ := ℍ) Φ₀ (opTableN T1C) QZ n ls e ρ →
      erwp (ℍ := ℍ) Φ₀ (opTableN T1) QZ n ls (hndE cH e) ρ := by
  refine erwp_handle Φ₀_down T1C T1 T1C_down T1_down 8
    (fun m i hm => by simp [T1C, hm]) _ _ _ QZ QZ QZ_down ?_ (fun _ => none)
    (fun _ en hT _ hq' _ hTk => by cases hTk)
    (fun k ls v ρ hv => erwp_idV Φ₀_down T1_down hv) ?_
  · intro i en hT _
    rcases T1C_cases hT with ⟨-, rfl, rfl⟩ | ⟨h8, -, -⟩
    · exact Stage1.capTag_one .lin
    · exact absurd h8.symm (by simp [divEff])
  · intro i en hT
    rcases T1C_cases hT with ⟨-, rfl, rfl⟩ | ⟨h8, -, -⟩
    · refine ⟨Stage1.resumeCl Val.unit, Stage1.clauseAt_pair0 _ _, fun _ k ls v κ ρ hsep => ?_,
        fun h => (by cases h)⟩
      obtain ⟨ρa, ρk, hc, ⟨-, rfl⟩, -, hK⟩ := hsep
      obtain rfl : ρ = ρk := eq_of_compS_empty_left hc
      refine erwp_resumeCl Φ₀_down T1_down QZ_down rfl fun k' hk' => ?_
      exact (hK ls (extF_refl ls _) k' hk').1 Val.unit PMap.empty ρ ⟨rfl, rfl⟩
        (ResU.comp_empty_right ρ)
    · exact absurd h8.symm (by simp [divEff])

/-- `hnd_Div rtH (hnd_C cH (hnd_Y yCancel bodyCC))`. -/
def progCancelC : Expr := hndE DivRuntime.rtH (hndE cH (hndE yHC bodyCC))

theorem progCancelC_ok (n : Nat) :
    erwp (ℍ := ℍ) Φ₀ (opTableN OpTabN.empty) QZ n [] progCancelC (PMap.empty : WRes) :=
  erwp_rtH Φ₀_down n [] _ _ (erwp_cHT n [] _ _ (erwp_yHCC n [] _ _ (bodyCC_ok 0 n)))

/-- **The performing finaliser on the cancel path.** A cell lent `mut` across a cancellable
`y` on a loop with no bound; the scheduler stores `κ` and cancels it; the cancel unwinds through
the lend to the finaliser frame, whose finaliser performs `close` (resumed by a handler outside
the scheduler) and frees the cell. Every configuration a run reaches is a value or steps, a
value only at the empty memory, and every `free` finds its cell. No fuel. -/
theorem progCancelC_orDiverges : OrDiverges (ℍ := ℍ) progCancelC :=
  erwp_adequacy (Φ := Φ₀) (fun _ _ _ _ h => h) progCancelC_ok

end BoCa.Fig16.LogRel.Core.Chain.SI.FinCancelProg

end
