import Core.Chain.SI.AntiCancelN
import Core.Chain.SI.AntiLendProg
import Core.Chain.SI.LendCancelProg

/-!
# The cancel case: a field of a `mut`-borrowed value borrowed `mut` across a `yield` whose `κ` the
scheduler cancels

    progAntiCancel = hnd_Div rtH (hnd_Y yCancel (
                     (λd. (λc. ubind (Dc, Dc) (iterate (fA, c))) (alloc d)) (alloc 1)))

    Dc = λ_. free (free c)

The turn is `AntiLendProg`'s: `c` lent `mut` to a method that opens the borrow, lends the field
`d` `mut` and holds that borrow across `y`, here cancellable. The scheduler stores the first
`y`'s `κ` and cancels it. The cancel run unwinds through the field's lend (its cancel run ends
carrying the field's claim), the frame `c ↦ own(d)` rides along (`erwpG_frameT`), the anti-frame
seals the cell with the field as its content (`erwp_M_antiFrameC`), the outer lend's cancel run
ends carrying `c`'s claim, `c ↦ own(d) ● d ↦ own(w)`, and the finaliser frees
both cells. `progAntiCancel_orDiverges`.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core.Chain.SI.AntiCancelProg
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel.Core.Chain.SI.LendProg
open BoCa.Fig16.LogRel.Core.Chain.SI.AntiLendProg
open BoCa.BoLo (Heap Step1 Steps Head Kont performE raiseE cancelVal opPayload freeE hndE hndVal
  clauseAt capTag ubindE)

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

/-! ### The tables, at a location typing -/

/-- `y : 1 ↠^cancel 1`, its cancel run at `Φ`. -/
def yCEntΦ (Φ : LocFam) : OpEntN :=
  ⟨.cancel, false, unitP, unitP, some (cancelOblN (ℍ := ℍ) Φ OpTabN.empty), extF⟩

/-- `T2C` with `y`'s cancel run at `Φ`. -/
def T2CΦ (Φ : LocFam) : OpTabN :=
  fun m i => if m = 6 ∧ i = 0 then some (yCEntΦ (ℍ := ℍ) Φ) else T1 m i

theorem T2CΦ_ent {Φ : LocFam} {m i : UInt32} {en : OpEntN} (h : T2CΦ (ℍ := ℍ) Φ m i = some en) :
    en = yCEntΦ (ℍ := ℍ) Φ ∨ en = tickEnt := by
  unfold T2CΦ at h
  split_ifs at h
  · exact .inl (Option.some.inj h).symm
  · exact .inr (T1_cases h).2.2

theorem T2CΦ_lendOKC (Φ : LocFam) (A : Life) : (T2CΦ (ℍ := ℍ) Φ).LendOKC A where
  entry := fun _ _ en h => by
    rcases T2CΦ_ent h with rfl | rfl <;> exact ⟨rfl, by simp [yCEntΦ, tickEnt], rfl⟩
  pa := fun _ _ en h _ _ _ ρ hA => by
    rcases T2CΦ_ent h with rfl | rfl <;>
    · obtain ⟨-, rfl⟩ := hA
      exact inStratum_empty A
  pb := fun _ _ en h _ _ _ ρ hB => by
    rcases T2CΦ_ent h with rfl | rfl <;>
    · obtain ⟨-, rfl⟩ := hB
      exact inStratum_empty _

theorem T2CΦ_e (Φ : LocFam) : ∀ m i en, T2CΦ (ℍ := ℍ) Φ m i = some en → en.abort = false →
    en.q ≠ .unr ∧ en.wc = extF := fun _ _ en h _ => by
  rcases T2CΦ_ent h with rfl | rfl <;> exact ⟨by simp [yCEntΦ, tickEnt], rfl⟩

theorem T2CΦ_fin (Φ : LocFam) : ∀ m i en, T2CΦ (ℍ := ℍ) Φ m i = some en → en.q = .cancel →
    en.fin = some (cancelOblN (ℍ := ℍ) Φ OpTabN.empty) := fun _ _ en h hq => by
  rcases T2CΦ_ent h with rfl | rfl
  · rfl
  · cases hq

/-- `claimT` reads only the cancel obligation's place: the cancel runs of `T2CΦ` at any `Φ′`
give the same claim table. -/
theorem claimT_T2CΦ (Φ Φ' : LocFam) (Φc : LocFam) (R : Nat → WProp) :
    @OpTabN.claimT ℍ _ (T2CΦ (ℍ := ℍ) Φ) Φc OpTabN.empty R =
      @OpTabN.claimT ℍ _ (T2CΦ (ℍ := ℍ) Φ') Φc OpTabN.empty R := by
  funext m i
  unfold OpTabN.claimT T2CΦ
  split_ifs <;> simp [yCEntΦ]

/-- Two claim tables over twins, the claim weakened, are twins with weaker cancel
obligations. -/
theorem claimT_twinC {T T' : OpTabN} {Φc : LocFam} {R R' : Nat → WProp}
    (hTT : ∀ m i en, T m i = some en → ∃ en', T' m i = some en' ∧ en'.q = en.q ∧
      en'.abort = en.abort ∧ en'.PA = en.PA ∧ en'.PB = en.PB ∧ en'.wc = en.wc ∧
      (en.q ≠ .cancel → en'.fin = en.fin))
    (hR : ∀ k ρ, R k ρ → R' k ρ) :
    (@OpTabN.claimT ℍ _ T Φc OpTabN.empty R).TwinC (@OpTabN.claimT ℍ _ T' Φc OpTabN.empty R') := by
  intro m i en₁ h
  obtain ⟨en, hT, rfl⟩ := claimT_some h
  obtain ⟨en', hT', hq, hab, hPA, hPB, hwc, hfin⟩ := hTT m i en hT
  by_cases hc : en.q = .cancel
  · refine ⟨OpEntN.mk en'.q en'.abort en'.PA en'.PB
      (some (@cancelOblRN ℍ _ Φc OpTabN.empty R')) en'.wc, ?_, ?_⟩
    · simp [OpTabN.claimT, hT', hq, hc]
    simp only [hc, if_true]
    refine ⟨hq.trans hc, hab, hPA, hPB, hwc, fun k ls K ρ h P hP => ?_⟩
    cases hP
    exact erwp_cancelRun_mono hR _ _ _ _ (h _ rfl)
  · refine ⟨en', by simp [OpTabN.claimT, hT', hq, hc], ?_⟩
    simp only [hc, if_false]
    refine ⟨hq, hab, hPA, hPB, hwc, fun k ls K ρ h P hP => h P ((hfin hc).symm.trans hP)⟩

/-- `T2CΦ` at two location typings: twins up to the cancel entry's obligation. -/
theorem T2CΦ_twin (Φ Φ' : LocFam) : ∀ m i en, T2CΦ (ℍ := ℍ) Φ m i = some en →
    ∃ en', T2CΦ (ℍ := ℍ) Φ' m i = some en' ∧ en'.q = en.q ∧ en'.abort = en.abort ∧
      en'.PA = en.PA ∧ en'.PB = en.PB ∧ en'.wc = en.wc ∧ (en.q ≠ .cancel → en'.fin = en.fin) := by
  intro m i en h
  unfold T2CΦ at h ⊢
  split_ifs at h ⊢
  · cases h; exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, fun hq => absurd rfl hq⟩
  · exact ⟨en, h, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩

/-! ### The field's lend, `y` cancellable -/

/-- **The borrowed computation, `y` cancellable, at any location typing**: `lend_okC`. -/
theorem lend_okCΦ {Φ : LocFam} (hΦ : Φ.Down) (l : Loc) (A : Life) (u : Val) (k : Nat)
    (ls : List SRec) (BM : WRes)
    (hBM : ResU.CompS PMap.empty (ResU.single l (CellU.mutOf A u PMap.empty (inStratum_empty A)
      (famF A k) rfl)) BM) :
    erwp (ℍ := ℍ) (Φ.set l A (famF A)) (opTableN (T2CΦ (ℍ := ℍ) (Φ.set l A (famF A))))
      (MFPost l A (famF A) (Qlend l)) k ls (lendE l) BM := by
  have hΦ' := LocFam.set_down (l := l) hΦ (famF_down A)
  have hFl : Φ.set l A (famF A) l = some ⟨A, famF A⟩ := by simp [LocFam.set]
  obtain rfl := eq_of_compS_empty_left hBM
  have hKH : ∀ m, (Kont.seq .hole (wrL l)).HasHnd m = false := fun m => by simp [Kont.HasHnd]
  have hKC : ∀ m, (Kont.seq .hole (wrL l)).Catches m = false := fun m => by simp [Kont.Catches]
  refine erwp_performG (T := T2CΦ (Φ.set l A (famF A))) (en := yCEntΦ (Φ.set l A (famF A)))
    (K := .seq .hole (wrL l)) (hKH 6) (by simp [T2CΦ]) rfl (compS_empty_left _) ⟨rfl, rfl⟩
    (fun h => by cases h) (fun ls' _ k' hk' w σB XB hB hXB => ?_) (fun ls' _ _ P hP => ?_)
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
    show erwp (ℍ := ℍ) (Φ.set l A (famF A)) (cancelTabN OpTabN.empty) (fun _ _ _ _ => False) k
      ls' _ _
    rw [dead_plain _ hKH (hKC 0), erwp_eq]
    exact rwpG_here (final_opPlug (r := true) (payloadName_cancelVal none) (hKC 0))
      (Or.inr (Or.inl ⟨_, none, pure_sep_mk ⟨rfl, hKC 0⟩
        ⟨PMap.empty, _, compS_empty_left _, emp_empty, noOwn_single_mut l⟩⟩))

/-! ### The method, `y` cancellable -/

/-- The callback's table: `T2C` at `Φ` with the opened cell's claim. -/
abbrev Tcb (Φ : LocFam) (c : Loc) (A : Life) : OpTabN :=
  @OpTabN.claimT ℍ _ (T2CΦ (ℍ := ℍ) Φ) Φ OpTabN.empty (claimR c A (boxF A))

/-- **The opened borrow, `y` cancellable**: `open_ok` with the field's lend at `claimT`
(`erwp_M_frameTF`), the opened cell framed across cancellable stops (`erwpG_frameT`), and the
field's claim beside the frame read as the opened cell's claim. -/
theorem openC_ok {Φ : LocFam} (hΦ : Φ.Down) (c d : Loc) (u : Val) (A : Life) (k : Nat)
    (ls : List SRec) (X : WRes)
    (hX : ResU.CompS (ResU.single d (CellU.ownOf u)) (ResU.single c (CellU.ownOf (.loc d))) X) :
    erwp (ℍ := ℍ) Φ (opTableG (Tcb (ℍ := ℍ) Φ c A) (CellFold c A (boxF A)))
      (AFPost c A (boxF A) (AntiLendProg.QD c A)) k ls (fieldE c) X := by
  set Φ₂ := Φ.set d A (famF A) with hΦ₂
  set T' := @OpTabN.claimT ℍ _ (T2CΦ (ℍ := ℍ) Φ₂) Φ OpTabN.empty (claimR d A (famF A))
  set R₂ : WProp := ptoOwn c (.loc d)
  set T'' := @OpTabN.claimT ℍ _ (T2CΦ (ℍ := ℍ) Φ₂) Φ OpTabN.empty
    (fun k => claimR d A (famF A) k ⋆ R₂)
  have hL := opTableG_local (Tcb (ℍ := ℍ) Φ c A) (CellFold c A (boxF A))
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
      (.seq Stage1.yE (.app (.app (.val (.prim .store)) (.var 0)) (.val (Val.i32 5))))) =
      lendE d := by
    simp [Expr.subst, Kont.plug, Stage1.yE, lendE, wrL, performE, opPayload, Val.pair,
      Val.i32, Val.unit, Val.loc, Expr.val, Val.prim, Val.storeV]
  rw [e₁]
  have hTfield : erwp (ℍ := ℍ) Φ (opTableG T' (CellFold d A (famF A))) (Qlend d) k₀ ls (lendE d)
      (ResU.single d (CellU.ownOf u)) :=
    erwp_M_frameTF (famF_down A) (T2CΦ_lendOKC Φ₂ A) (claimT_twin _ _ _ _)
      (claimT_canS (famF_down A) (empty_lendOK A) (T2CΦ_fin Φ₂)
        (fun m i en h => (T2CΦ_e Φ₂ m i en h (by rcases T2CΦ_ent h with rfl | rfl <;> rfl)).1))
      k₀ k₀ le_rfl ls (lendE d) u PMap.empty _ PMap.empty _ (inStratum_empty A)
      (inStratum_empty _) (famF A k₀) (fun _ _ h => h) rfl (ResU.comp_empty_right _)
      (ResU.comp_empty_right _) (lend_okCΦ hΦ d A u k₀ ls)
  have hT'e : ∀ m i en, T' m i = some en → en.abort = false → en.q ≠ .unr ∧ en.wc = extF := by
    intro m i en h ha
    obtain ⟨en₀, h₀, rfl⟩ := claimT_some h
    by_cases hq : en₀.q = .cancel
    · simp only [hq, if_true] at ha ⊢
      exact ⟨by simp, (T2CΦ_e Φ₂ m i en₀ h₀ ha).2⟩
    · simp only [hq, if_false] at ha ⊢; exact T2CΦ_e Φ₂ m i en₀ h₀ ha
  have hT'T'' : T'.Twin T'' := by
    intro m i en h
    obtain ⟨en₀, h₀, rfl⟩ := claimT_some h
    by_cases hq : en₀.q = .cancel
    · refine ⟨OpEntN.mk en₀.q en₀.abort en₀.PA en₀.PB
        (some (@cancelOblRN ℍ _ Φ OpTabN.empty (fun k => claimR d A (famF A) k ⋆ R₂))) en₀.wc,
        by simp [T'', OpTabN.claimT, h₀, hq], ?_⟩
      simp [hq]
    · refine ⟨en₀, by simp [T'', OpTabN.claimT, h₀, hq], ?_⟩
      simp [hq]
  have hfr := erwpG_frameT hT'e hT'T'' R₂ (fun m i en en' h h' hql k ls' K ρk σ₂ ρk₂ hk hR hcan => by
      obtain ⟨en₀, h₀, rfl⟩ := claimT_some h
      obtain ⟨en₁, h₁, rfl⟩ := claimT_some h'
      rw [h₀] at h₁; cases h₁
      have hqc : en₀.q = .cancel := by
        rcases T2CΦ_ent h₀ with rfl | rfl
        · rfl
        · exfalso; simp [tickEnt] at hql
      simp only [hqc, if_true] at hcan ⊢
      intro P hP
      cases hP
      exact erwp_frame_cancelRun R₂ k ls' _ ρk σ₂ ρk₂ hk hR (hcan _ rfl))
    k₀ ls (lendE d) _ _ _ hc rfl hTfield
  have hR : ∀ k ρ, (claimR d A (famF A) k ⋆ R₂) ρ → claimR c A (boxF A) k ρ := by
    rintro k ρ ⟨ρ₁, ρ₂', hc₁, ⟨w, σ, hσ, hF, hcw⟩, rfl⟩
    have hσ0 : σ = PMap.empty := hF
    subst hσ0
    obtain rfl := ResU.CompS.functional hcw (ResU.comp_empty_right _)
    exact ⟨Val.loc d, ResU.single d (CellU.ownOf w), inStratum_own A d w, ⟨d, w, rfl, rfl⟩,
      ResU.CompS.comm hc₁⟩
  refine erwp_mono (fun k ls' v ρ h => ?_)
    (opTableG_twinC (claimT_twinC (T2CΦ_twin Φ₂ Φ) hR) fun k ls' ρ h => ?_) _ _ _ _ hfr
  · obtain ⟨ρ₁, ρ₂, hc₁, ⟨rfl, w, rfl⟩, rfl⟩ := h
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
  · obtain ⟨ρ₁, ρ₂, hc₁, ⟨w, χ, hχ, hw, R, rest, hr1, hr2⟩, rfl⟩ := h
    have hχ0 : χ = PMap.empty := hw
    subst hχ0
    obtain rfl := eq_of_compS_empty_left hr2
    exact ⟨Val.loc d, ResU.single d (CellU.ownOf w), inStratum_own A d w, ⟨d, w, rfl, rfl⟩, _,
      ρ₁, ResU.CompS.comm hc₁, hr1⟩

/-- **The method, `y` cancellable**: the anti-frame across cancellable stops
(`erwp_M_antiFrameC`) around the opened borrow; the borrow released at the end. -/
theorem methodC_ok {Φ : LocFam} (hΦ : Φ.Down) (c d : Loc) (u : Val) (A : Life) (k : Nat)
    (ls : List SRec) (BM : WRes)
    (hBM : ResU.CompS PMap.empty (ResU.single c (CellU.mutOf A (.loc d)
      (ResU.single d (CellU.ownOf u)) (inStratum_own A d u) (boxF A k) ⟨d, u, rfl, rfl⟩)) BM) :
    erwp (ℍ := ℍ) (Φ.set c A (boxF A)) (opTableN (T2CΦ (ℍ := ℍ) (Φ.set c A (boxF A))))
      (MFPost c A (boxF A) (QA c)) k ls (fieldE c) BM := by
  have hΦ' := LocFam.set_down (l := c) hΦ (boxF_down A)
  have hFl : Φ.set c A (boxF A) c = some ⟨A, boxF A⟩ := by simp [LocFam.set]
  obtain rfl := eq_of_compS_empty_left hBM
  refine erwp_dump (opTableN_local _) k ls _ _ (erwp_M_antiFrameC hΦ' hFl (T2CΦ_e _)
    (T2CΦ_fin _) k ls (fieldE c) (.loc d) _ (inStratum_own A d u) k ⟨d, u, rfl, rfl⟩ PMap.empty _
    (ResU.comp_empty_right _) fun W X hW hX => ?_)
  obtain rfl := eq_of_compS_empty_left hX
  exact openC_ok hΦ' c d u A k ls _ hW

/-! ### The turn, the body, the program -/

theorem T2CΦ_Φ₀ : T2CΦ (ℍ := ℍ) Φ₀ = T2C (ℍ := ℍ) := rfl

/-- The body's table: `T2C` with `c`'s claim. -/
abbrev TL (A : Life) (c : Loc) : OpTabN :=
  @OpTabN.claimT ℍ _ (T2C (ℍ := ℍ)) Φ₀ OpTabN.empty (claimR c A (boxF A))

theorem claimR_downB {c : Loc} {A : Life} :
    ∀ k (ρ : WRes), claimR c A (boxF A) (k + 1) ρ → claimR c A (boxF A) k ρ :=
  fun _ _ ⟨w, σ, hσ, hw, hc⟩ => ⟨w, σ, hσ, hw, hc⟩

theorem TL_down (A : Life) (c : Loc) : (TL (ℍ := ℍ) A c).Down where
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
        (cancelTabR_down empty_down claimR_downB) falsePost_down (Nat.le_succ _) hk
    · rw [if_neg hq] at hP; exact T2C_down.fin _ _ en _ hT hP
  wcl := fun _ _ en' h => by
    obtain ⟨en, hT, rfl⟩ := claimT_some h
    by_cases hq : en.q = .cancel
    · rw [if_pos hq]; exact T2C_down.wcl _ _ en hT
    · rw [if_neg hq]; exact T2C_down.wcl _ _ en hT

theorem TL_ctxClosed (A : Life) (c : Loc) (K : Kont) (hH : ∀ m, K.HasHnd m = false)
    (hC : ∀ m, K.Catches m = false) : (TL (ℍ := ℍ) A c).CtxClosed K :=
  claimT_ctxClosed Φ₀_down K hH hC T2C_finNone (empty_ctxClosed K)

/-- The loop's invariant over a fixed cell `c`. -/
def ILc (c : Loc) : Val → WProp := fun s ρ => ∃ (d : Loc) (u : Val), s = Val.loc c ∧
  ResU.CompS (ResU.single c (CellU.ownOf (.loc d))) (ResU.single d (CellU.ownOf u)) ρ

/-- **A turn, `y` cancellable**: the outer lend at `claimT` (`erwp_M_frameT`), its cancel runs
ending at `c`'s claim. -/
theorem turnC_ok (A : Life) (c : Loc) (k : Nat) (s : Val) (ls : List SRec) (ρ : WRes)
    (hI : ILc c s ρ) :
    erwp (ℍ := ℍ) Φ₀ (opTableN (TL (ℍ := ℍ) A c)) (turnPostN (ILc c) QF) k ls
      (.app (.app (.val fA) (.val s)) (.val nextV)) ρ := by
  obtain ⟨d, u, rfl, hρ⟩ := hI
  have hD := opTableN_down (TL_down (ℍ := ℍ) A c)
  have hTP : (turnPostN (ILc c) QF).Down := fun _ _ _ _ h => by
    rcases h with ⟨x, hx, hq⟩ | h
    · exact .inl ⟨x, hx, hq⟩
    · exact .inr h
  refine erwp_det Φ₀_down hD hTP
    (fun μ => step1Only_plug (Head.beta μ _ (Val.loc c)) rfl (.appL .hole nextV)) ?_
  have e₁ : (Kont.appL .hole nextV).plug (Expr.subst 0 (Val.loc c)
      (.lam (.case (.var 0) (.seq (.app (.val lamW) (.app (.val (.prim .load)) (.var 2)))
        (.inj₂ (.var 2))) (.val .unit)))) =
      Kont.hole.plug (.app (.val (Val.lam (.case (.var 0)
        (.seq (fieldE c) (.inj₂ (.val (Val.loc c)))) (.val .unit)))) (.val nextV)) := by
    simp [Expr.subst, Expr.shift, Kont.plug, lamW, fieldE, ldA, Stage1.yE, performE, opPayload,
      Val.pair, Val.i32, Val.unit, Val.lam, Val.loc, Expr.val, Val.prim, Val.shift]
  rw [e₁]
  refine erwp_det Φ₀_down hD hTP (fun μ => step1Only_plug (Head.beta μ _ nextV) rfl .hole) ?_
  have e₂ : Kont.hole.plug (Expr.subst 0 nextV (.case (.var 0)
        (.seq (fieldE c) (.inj₂ (.val (Val.loc c)))) (.val .unit))) =
      Kont.hole.plug (.case (.val (Val.inj₁ Val.unit))
        (.seq (fieldE c) (.inj₂ (.val (Val.loc c)))) (.val .unit)) := by
    simp [Expr.subst, Kont.plug, lamW, fieldE, ldA, Stage1.yE, performE, opPayload, Val.pair,
      Val.i32, Val.unit, nextV, Val.inj₁, Val.loc, Expr.val, Val.prim, Val.lam]
  rw [e₂]
  refine erwp_det Φ₀_down hD hTP
    (fun μ => step1Only_plug (Head.case₁ μ Val.unit _ _) rfl .hole) ?_
  have e₃ : Kont.hole.plug (Expr.subst 0 Val.unit
        (.seq (fieldE c) (.inj₂ (.val (Val.loc c))))) =
      (Kont.seq .hole (.inj₂ (.val (Val.loc c)))).plug (fieldE c) := by
    simp [Expr.subst, Kont.plug, lamW, fieldE, ldA, Stage1.yE, performE, opPayload, Val.pair,
      Val.i32, Val.unit, Val.loc, Expr.val, Val.prim, Val.lam]
  rw [e₃]
  refine erwp_bind_le (Q' := QA c) Φ₀_down _ (fun m => by simp [Kont.HasHnd])
    (fun m => by simp [Kont.Catches])
    (TL_ctxClosed A c _ (fun m => by simp [Kont.HasHnd]) (fun m => by simp [Kont.Catches]))
    k ?_ k le_rfl ls _ _ ?_
  · rintro k' ls' v σ - ⟨rfl, d', u', hσ⟩
    refine erwp_det Φ₀_down hD hTP (fun μ => step1Only_plug (Head.seq μ _) rfl .hole) ?_
    exact erwp_val (v := Val.inj₂ (Val.loc c)) (.inr ⟨Val.loc c, rfl, d', u', rfl, hσ⟩)
  · have h := erwp_M_frameT (Φ := Φ₀) (boxF_down A)
      (T2CΦ_lendOKC (Φ₀.set c A (boxF A)) A)
      (claimT_twin (T2CΦ (Φ₀.set c A (boxF A))) Φ₀ OpTabN.empty (claimR c A (boxF A)))
      (claimT_canS (boxF_down A) (empty_lendOK A) (T2CΦ_fin _)
        (fun m i en h => (T2CΦ_e _ m i en h
          (by rcases T2CΦ_ent h with rfl | rfl <;> rfl)).1))
      k k le_rfl ls (fieldE c) (.loc d) (ResU.single d (CellU.ownOf u)) ρ PMap.empty ρ
      (inStratum_own A d u) (inStratum_empty _) (boxF A k) (fun _ _ h => h) ⟨d, u, rfl, rfl⟩ hρ
      (ResU.comp_empty_right _) (methodC_ok Φ₀_down c d u A k ls)
    rwa [claimT_T2CΦ (Φ₀.set c A (boxF A)) Φ₀, T2CΦ_Φ₀] at h

/-- `λ_. free (free c)`: frees `c`, then the field `free c` returns. -/
def Dc (c : Loc) : Val := Val.lam (freeE (freeE (.val (Val.loc c))))

/-- **The finaliser consumes `c`'s claim**: both cells freed. -/
theorem Dc_ok (A : Life) (c : Loc) (k : Nat) (ls : List SRec) (ρ : WRes)
    (h : claimR c A (boxF A) k ρ) :
    rwp (ℍ := ℍ) Φ₀ (fun _ _ _ ρ' => ρ' = PMap.empty) k ls (.app (.val (Dc c)) (.val .unit)) ρ := by
  obtain ⟨w, σ, hσ, ⟨d, u, rfl, hσ'⟩, hc⟩ := h
  have : σ = ResU.single d (CellU.ownOf u) := hσ'
  subst this
  rw [rwp_iff_rwpG]
  refine rwpG_det Φ₀_down (fun _ _ _ _ ⟨v, hv, hq⟩ => ⟨v, hv, hq⟩)
    (fun μ => step1Only_plug (Head.beta μ _ Val.unit) rfl .hole) ?_
  have e : Kont.hole.plug (Expr.subst 0 Val.unit (freeE (freeE (.val (Val.loc c))))) =
      (Kont.appR (.val (.prim .free)) .hole).plug
        (.app (.val (.prim .free)) (.val (.loc c)) : Expr) := by
    simp [Expr.subst, Kont.plug, freeE, Val.loc, Expr.val, Val.prim]
  rw [e, ← rwp_iff_rwpG]
  refine rwp_bind Φ₀_down _ (rwp_free ls c (.loc d) _ ⟨_, _, hc, rfl, ?_⟩)
  exact rwp_free ls d u _ ⟨_, PMap.empty, ResU.comp_empty_right _, rfl, rfl⟩

/-- `λc. ubind (Dc, Dc) (iterate (fA, c))`, its body. -/
def bodyCDF : Expr :=
  .app (.app (.val (.prim .ubind))
    (.pair (.val (Val.lam (freeE (freeE (.var 1))))) (.val (Val.lam (freeE (freeE (.var 1)))))))
    (.app (.val (.prim .iterate)) (.pair (.val fA) (.var 0)))

theorem bodyCDF_subst (c : Loc) :
    Expr.subst 0 (Val.loc c) bodyCDF = ubindE (Val.pair (Dc c) (Dc c)) (iterateE fA (Val.loc c)) := by
  simp [bodyCDF, Dc, ubindE, Expr.subst, iterateE, Val.pair, Val.lam, Val.loc, freeE, Expr.val,
    Expr.shift, Val.prim, subst_closedAt _ _ (show closedAt 0 fA.1 = true from rfl) (Nat.zero_le _)]

/-- `λd. (λc. bodyCDF) (alloc d)`. -/
def lamDD : Val :=
  Val.lam (.app (.val (Val.lam bodyCDF)) (.app (.val (.prim .alloc)) (.var 0)))

/-- `lamDD (alloc 1)`. -/
def bodyCD : Expr := .app (.val lamDD) (.app (.val (.prim .alloc)) (.val (Val.i32 1)))

theorem bodyCD_ok (A : Life) (n : Nat) :
    erwp (ℍ := ℍ) Φ₀ (opTableN (T2C (ℍ := ℍ))) QZ n [] bodyCD (PMap.empty : WRes) := by
  have hD := opTableN_down (T2C_down (ℍ := ℍ))
  have hL := opTableN_local (T2C (ℍ := ℍ))
  refine erwp_alloc Φ₀_down hL (.appR (.val lamDD) .hole) (Val.i32 1)
    (fun d τ₁ τ₂ hcd hcd' => ?_)
  obtain rfl := eq_of_compS_empty_left hcd'
  refine erwp_det Φ₀_down hD QZ_down (fun μ => step1Only_plug (Head.beta μ _ _) rfl .hole) ?_
  have h₂ : Kont.hole.plug (Expr.subst 0 (Val.loc d)
      (.app (.val (Val.lam bodyCDF)) (.app (.val (.prim .alloc)) (.var 0)))) =
      (Kont.appR (.val (Val.lam bodyCDF)) .hole).plug
        (.app (.val (.prim .alloc)) (.val (Val.loc d))) := by
    simp [Expr.subst, Kont.plug, bodyCDF, fA, lamW, Stage1.yE, performE, opPayload, freeE,
      Val.pair, Val.i32, Val.unit, Val.loc, Expr.val, Val.prim, Val.lam]
  rw [h₂]
  refine erwp_alloc Φ₀_down hL (.appR (.val (Val.lam bodyCDF)) .hole) (Val.loc d)
    (fun c υ₁ υ₂ hcc hcc' => ?_)
  refine erwp_det Φ₀_down hD QZ_down (fun μ => step1Only_plug (Head.beta μ _ _) rfl .hole) ?_
  rw [Kont.plug_hole, bodyCDF_subst]
  subst hcd hcc
  refine erwp_ubindClaim Φ₀_down T2C_down empty_down (fun _ _ _ h => by cases h) T2C_e T2C_fin
    (Dc c) (Dc c) (Dc_ok A c) QZ_down (Qin := QF) (fun _ _ _ _ h => h.elim) _ _ _ _ ?_
  exact erwp_iterate Φ₀_down (TL_down A c)
    (TL_ctxClosed A c _ (fun m => by simp [iterK, Kont.HasHnd])
      (fun m => by simp [iterK, Kont.Catches])) QF_down rfl (I := ILc c) (en := tickEnt)
    (by simp [OpTabN.claimT, T2C, T1, tickEnt, Stage1.divEff_ne6]) rfl rfl
    (fun _ _ => ⟨rfl, rfl⟩) (fun _ _ _ _ h => h) (fun s ρ ⟨_, _, hs, _⟩ => by subst hs; rfl)
    (fun k s ls ρ hI => turnC_ok A c k s ls ρ hI) _ _ _ _
    ⟨d, Val.i32 1, rfl, ResU.CompS.comm hcc'⟩

/-- `hnd_Div rtH (hnd_Y yCancel bodyCD)`. -/
def progAntiCancel : Expr := hndE DivRuntime.rtH (hndE yHC bodyCD)

theorem progAntiCancel_ok (n : Nat) :
    erwp (ℍ := ℍ) Φ₀ (opTableN OpTabN.empty) QZ n [] progAntiCancel (PMap.empty : WRes) :=
  erwp_rtH Φ₀_down n [] _ _ (erwp_yHC n [] _ _ (bodyCD_ok 0 n))

/-- **The cancel case.** A value with a boxed field lent `mut` to a method that opens the borrow,
lends the field `mut` and holds that borrow across a cancellable `y`; the scheduler stores `κ`
and cancels it; the cancel unwinds through the field's lend, the anti-frame and the outer lend to
the finaliser frame, whose finaliser frees the value and its field. Every configuration a run
reaches is a value or steps, a value only at the empty memory, and every `free` finds its cell.
No fuel. -/
theorem progAntiCancel_orDiverges : OrDiverges (ℍ := ℍ) progAntiCancel :=
  erwp_adequacy (Φ := Φ₀) (fun _ _ _ _ h => h) progAntiCancel_ok

end BoCa.Fig16.LogRel.Core.Chain.SI.AntiCancelProg

end
