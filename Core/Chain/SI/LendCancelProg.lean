import Core.Chain.SI.UbindN

/-!
# Unknown 1, the cancel case, the test: a `mut` lend live across a `yield` whose `κ` the
scheduler cancels

    progLendCancel = hnd_Div rtH (
                     hnd_Y yCancel (                        -- y : 1 ↠^cancel 1; κ stored, cancelled
                       (λc. ubind (λ_. free c, λ_. free c) (iterate (fT, c))) (alloc 1)))

Each turn lends the cell `mut` to `y (); s := 5` (`erwp_M_frameC`). The scheduler stores the
first `y`'s `κ` in a cell, takes it back and cancels it: the cancel run unwinds through the lend
(the lender's cancel run ends carrying the lend's claim, `claimR`) to the finaliser frame, whose
`D = λ_. free c` consumes the claim (`erwp_ubindClaim`); the run ends at `()` at the empty
memory. `progLendCancel_orDiverges`.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core.Chain.SI.LendProg
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.BoLo (Heap Step1 Steps Head Kont performE raiseE cancelVal opPayload freeE hndE hndVal
  clauseAt capTag ubindE)

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

/-! ### Stops, cancel runs and contexts -/

/-- A stop at a non-abortive operation of any qualifier, its continuation's share and cancel run
given. -/
theorem erwp_performG {Φ : LocFam} {T : OpTabN} {Q : PostN} (K : Kont) {m i : UInt32} {v : Val}
    {en : OpEntN} (hK : K.HasHnd m = false) (hT : T m i = some en) (ha : en.abort = false)
    {n : Nat} {ls : List SRec} {ρa ρk ρ : WRes} (hc : ResU.CompS ρa ρk ρ)
    (hA : en.PA n ls v ρa) (hu : en.q = .unr → ρk = PMap.empty)
    (hk : ∀ ls', en.wc ls ls' ρk → ∀ k', k' < n → ∀ w : Val,
      (en.PB k' ls' w ─⋆ erwp (ℍ := ℍ) Φ (opTableN T) Q k' ls' (K.plug (.val w))) ρk)
    (hcan : ∀ ls', en.wc ls ls' ρk → en.q ≠ .lin → cancelOKN en n ls' K ρk) :
    erwp (ℍ := ℍ) Φ (opTableN T) Q n ls (K.plug (performE (.val (opPayload m i v)))) ρ := by
  rw [erwp_eq]
  refine rwpG_here (final_opPlug (r := false) (payloadName_opPayload m i v) hK) (Or.inr (Or.inl
    ⟨K, m, i, v, en, pure_sep_mk ⟨rfl, hK, hT, ha⟩ ⟨ρa, ρk, hc, hA, hu,
      fun ls' he => ⟨fun k' hk' w τ₁ τ₂ hB hcτ => ?_, hcan ls' he⟩⟩⟩))
  simp only [erwpC, hk', if_true]
  exact hk ls' he k' hk' w τ₁ τ₂ hB hcτ

/-- **A cancel run passes a context with no handler and no catcher.** -/
theorem erwp_cancelTabR_ctx {Φ : LocFam} (hΦ : Φ.Down) {T : OpTabN} {R : Nat → WProp}
    (K : Kont) (hH : ∀ m, K.HasHnd m = false) (hC : ∀ m, K.Catches m = false)
    (hK : T.CtxClosed K) :
    ∀ n ls x ρ, erwp (ℍ := ℍ) Φ (cancelTabR T R) (fun _ _ _ _ => False) n ls x ρ →
      erwp (ℍ := ℍ) Φ (cancelTabR T R) (fun _ _ _ _ => False) n ls (K.plug x) ρ := by
  have hL := cancelTabR_local T R
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ls x ρ h
  rw [erwp_eq]
  refine rwpG_bind hΦ K ?_
  refine rwpG_mono_le (fun k hk ls' t σ ht => ?_) (erwp_unfold_at hL le_rfl h)
  rcases ht with ⟨_, _, hf⟩ | ⟨K', err, hp⟩ | ⟨K₁, m, i, v, en, hp⟩
  · exact hf.elim
  · obtain ⟨⟨rfl, hK'⟩, hrest⟩ := pure_sep_iff.mp hp
    have hKo : (K.comp K').Catches 0 = false := by simp [catches_comp, hC, hK']
    have ht' : K.plug (K'.plug (raiseE (.val (cancelVal err)))) =
        (K.comp K').plug (opE true (cancelVal err)) := by
      rw [Kont.plug_comp]; rfl
    rw [ht']
    exact rwpG_here (final_opPlug (payloadName_cancelVal err) hKo) (Or.inr (Or.inl
      ⟨K.comp K', err, pure_sep_mk ⟨rfl, hKo⟩ hrest⟩))
  · obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρk, hcak, hA, hu, hcont'⟩ := pure_sep_iff.mp hp
    have hKo : (K.comp K₁).HasHnd m = false := by simp [hasHnd_comp, hH, hK₁]
    have ht' : K.plug (K₁.plug (performE (.val (opPayload m i v)))) =
        (K.comp K₁).plug (opE false (opPayload m i v)) := by
      rw [Kont.plug_comp]; rfl
    rw [ht']
    refine rwpG_here (final_opPlug (payloadName_opPayload m i v) hKo) (Or.inr (Or.inr
      ⟨K.comp K₁, m, i, v, en, pure_sep_mk ⟨rfl, hKo, hT, ha⟩
        ⟨ρa, ρk, hcak, hA, hu, fun ls'' he => ⟨fun k' hk' w τ₁ τ₂ hB hcτ => ?_,
          fun hq' P hP => ?_⟩⟩⟩))
    · rw [Kont.plug_comp]
      have hc := (hcont' ls'' he).1 k' hk' w τ₁ τ₂ hB hcτ
      simp only [erwpC, show k' < n by omega, if_true] at hc ⊢
      exact ih k' (by omega) _ _ _ hc
    · exact hK m i en P hT hP _ _ _ _ _ ((hcont' ls'' he).2 hq' P hP)

/-- `claimT`'s cancel obligations pass a context with no handler and no catcher. -/
theorem claimT_ctxClosed {Φ : LocFam} (hΦ : Φ.Down) {T T₁ : OpTabN} {R : Nat → WProp}
    (K : Kont) (hH : ∀ m, K.HasHnd m = false) (hC : ∀ m, K.Catches m = false)
    (hT : ∀ m i en, T m i = some en → en.q ≠ .cancel → en.fin = none)
    (hT₁ : T₁.CtxClosed K) : (@OpTabN.claimT ℍ _ T Φ T₁ R).CtxClosed K := by
  intro m i en' P h hP k ls K' x ρ hx
  obtain ⟨en, hT', rfl⟩ := claimT_some h
  by_cases hq : en.q = .cancel
  · rw [if_pos hq] at hP
    cases hP
    have hd : (K.comp K').dead = K.comp K'.dead := by
      rw [dead_comp, dead_plain K hH (hC 0)]
    show erwp (ℍ := ℍ) Φ (cancelTabR T₁ R) (fun _ _ _ _ => False) k ls _ ρ
    rw [hd, Kont.plug_comp]
    exact erwp_cancelTabR_ctx hΦ K hH hC hT₁ k ls _ ρ hx
  · rw [if_neg hq, hT m i en hT' hq] at hP
    cases hP

/-- A computation at the empty table is at every table. -/
theorem erwp_of_empty {Φ : LocFam} {T : OpTabN} {Q : PostN} {n : Nat} {ls : List SRec}
    {e : Expr} {ρ : WRes} (h : erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) Q n ls e ρ) :
    erwp (ℍ := ℍ) Φ (opTableN T) Q n ls e ρ := by
  rw [erwp_eq] at h ⊢
  refine rwpG_mono (fun k ls' t σ ht => ?_) h
  rcases ht with ht | ⟨_, _, _, _, _, h'⟩ | ⟨_, _, _, _, _, h'⟩
  · exact Or.inl ht
  · exact absurd (pure_sep_iff.mp h').1.2.2.1 (by simp [OpTabN.empty])
  · exact absurd (pure_sep_iff.mp h').1.2.2.1 (by simp [OpTabN.empty])

/-! ### The tables -/

/-- `y : 1 ↠^cancel 1`, its cancel run releasing every cell of the cancelled region, no
finaliser performing anything. -/
def yCEnt : OpEntN :=
  ⟨.cancel, false, unitP, unitP, some (cancelOblN (ℍ := ℍ) Φ₀ OpTabN.empty), extF⟩

/-- Under both handlers: the cancellable `y` and the tick. -/
def T2C : OpTabN := fun m i => if m = 6 ∧ i = 0 then some (yCEnt (ℍ := ℍ)) else T1 m i

theorem T2C_cases {m i : UInt32} {en : OpEntN} (h : T2C (ℍ := ℍ) m i = some en) :
    (m = 6 ∧ i = 0 ∧ en = yCEnt (ℍ := ℍ)) ∨ (m = divEff ∧ i = 0 ∧ en = tickEnt) := by
  unfold T2C at h
  split_ifs at h with h₁
  · exact .inl ⟨h₁.1, h₁.2, (Option.some.inj h).symm⟩
  · exact .inr (T1_cases h)

theorem T2C_ent {m i : UInt32} {en : OpEntN} (h : T2C (ℍ := ℍ) m i = some en) :
    en = yCEnt (ℍ := ℍ) ∨ en = tickEnt := by
  rcases T2C_cases h with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩
  · exact .inl rfl
  · exact .inr rfl

theorem cancelOblN_down {Φ : LocFam} {T : OpTabN} (hΦ : Φ.Down) (hT : T.Down) :
    ∀ k ls e (ρ : WRes), cancelOblN (ℍ := ℍ) Φ T (k + 1) ls e ρ → cancelOblN (ℍ := ℍ) Φ T k ls e ρ :=
  fun _ _ _ _ h => erwp_le hΦ (cancelTabN_local T) (cancelTabN_down hT) falsePost_down
    (Nat.le_succ _) h

theorem T2C_down : (T2C (ℍ := ℍ)).Down where
  pa := fun _ _ en h _ _ _ _ hA => by rcases T2C_ent h with he | he <;> subst he <;> exact hA
  fin := fun _ _ en P h hP => by
    rcases T2C_ent h with rfl | rfl
    · cases hP; exact cancelOblN_down Φ₀_down empty_down
    · cases hP
  wcl := fun _ _ en h => by rcases T2C_ent h with rfl | rfl <;> exact extF_left

theorem T2C_lendOKC (A : Life) : (T2C (ℍ := ℍ)).LendOKC A where
  entry := fun _ _ en h => by
    rcases T2C_ent h with rfl | rfl <;> exact ⟨rfl, by simp [yCEnt, tickEnt], rfl⟩
  pa := fun _ _ en h _ _ _ ρ hA => by
    rcases T2C_ent h with rfl | rfl <;>
    · obtain ⟨-, rfl⟩ := hA
      exact inStratum_empty A
  pb := fun _ _ en h _ _ _ ρ hB => by
    rcases T2C_ent h with rfl | rfl <;>
    · obtain ⟨-, rfl⟩ := hB
      exact inStratum_empty _

theorem T2C_fin : ∀ m i en, T2C (ℍ := ℍ) m i = some en → en.q = .cancel →
    en.fin = some (cancelOblN (ℍ := ℍ) Φ₀ OpTabN.empty) := fun _ _ en h hq => by
  rcases T2C_ent h with rfl | rfl
  · rfl
  · cases hq

theorem T2C_finNone : ∀ m i en, T2C (ℍ := ℍ) m i = some en → en.q ≠ .cancel → en.fin = none :=
  fun _ _ en h hq => by
    rcases T2C_ent h with rfl | rfl
    · exact absurd rfl hq
    · rfl

theorem empty_lendOK (A : Life) : OpTabN.empty.LendOK A where
  entry := fun _ _ _ h => by cases h
  pa := fun _ _ _ h => by cases h
  pb := fun _ _ _ h => by cases h

theorem empty_ctxClosed (K : Kont) : OpTabN.empty.CtxClosed K := fun _ _ _ _ h => by cases h

/-- The body's table: `T2C` with the lend's claim at `ℓ`. -/
abbrev T2L (A : Life) (l : Loc) : OpTabN :=
  @OpTabN.claimT ℍ _ (T2C (ℍ := ℍ)) Φ₀ OpTabN.empty (claimR l A (famF A))

theorem cancelTabR_down {T : OpTabN} (hT : T.Down) {R : Nat → WProp}
    (hR : ∀ k ρ, R (k + 1) ρ → R k ρ) : (cancelTabR T R).Down := by
  intro k ls t Ψ ρ h
  rcases h with ⟨K, err, hp⟩ | ⟨K, n, i, v, en, h⟩
  · obtain ⟨hc, y1, y2, hy, ⟨τa, τb, hcab, he, hnb⟩, hRk⟩ := pure_sep_iff.mp hp
    refine Or.inl ⟨K, err, pure_sep_mk hc ⟨y1, y2, hy, ⟨τa, τb, hcab, ?_, hnb⟩, hR _ _ hRk⟩⟩
    cases err with
    | none => exact he
    | some E =>
        obtain ⟨m, j, w, en, he⟩ := he
        obtain ⟨hh, hPA, hn⟩ := pure_sep_iff.mp he
        exact ⟨m, j, w, en, pure_sep_mk hh ⟨hT.pa _ _ _ hh.2.1 _ _ _ _ hPA, hn⟩⟩
  · obtain ⟨⟨h₁, h₂, h₃, h₄⟩, ρa, ρk, hc, hA, hu, hcont⟩ := pure_sep_iff.mp h
    exact Or.inr ⟨K, n, i, v, en, pure_sep_mk ⟨h₁, h₂, h₃, h₄⟩ ⟨ρa, ρk, hc,
      hT.pa _ _ _ h₃ _ _ _ _ hA, hu, fun ls' he =>
      ⟨fun k' hk => (hcont ls' he).1 k' (by omega), fun hq P hP =>
        hT.fin _ _ _ _ h₃ hP _ _ _ _ ((hcont ls' he).2 hq P hP)⟩⟩⟩

theorem claimR_down {l : Loc} {A : Life} {F : Nat → Val → SPropS Loc Val A} (hF : DownFam A F) :
    ∀ k (ρ : WRes), claimR l A F (k + 1) ρ → claimR l A F k ρ :=
  fun _ _ ⟨w, σ, hσ, hw, hc⟩ => ⟨w, σ, hσ, hF _ _ _ hw, hc⟩

theorem T2L_down (A : Life) (l : Loc) : (T2L (ℍ := ℍ) A l).Down where
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
        (cancelTabR_down empty_down (claimR_down (famF_down A))) falsePost_down
        (Nat.le_succ _) hk
    · rw [if_neg hq] at hP; exact T2C_down.fin _ _ en _ hT hP
  wcl := fun _ _ en' h => by
    obtain ⟨en, hT, rfl⟩ := claimT_some h
    by_cases hq : en.q = .cancel
    · rw [if_pos hq]; exact T2C_down.wcl _ _ en hT
    · rw [if_neg hq]; exact T2C_down.wcl _ _ en hT

/-! ### The lent computation, the turn, the loop -/

/-- **The borrowed computation, `y` cancellable**: its cancel run is the `raise` at once, the
borrow garbage. -/
theorem lend_okC (l : Loc) (A : Life) (u : Val) (k : Nat) (ls : List SRec) (BM : WRes)
    (hBM : ResU.CompS PMap.empty (ResU.single l (CellU.mutOf A u PMap.empty (inStratum_empty A)
      (famF A k) rfl)) BM) :
    erwp (ℍ := ℍ) (Φ₀.set l A (famF A)) (opTableN (T2C (ℍ := ℍ))) (MFPost l A (famF A) (Qlend l))
      k ls (lendE l) BM := by
  have hΦ' := LocFam.set_down (l := l) Φ₀_down (famF_down A)
  have hFl : Φ₀.set l A (famF A) l = some ⟨A, famF A⟩ := by simp [LocFam.set]
  obtain rfl := eq_of_compS_empty_left hBM
  have hKH : ∀ m, (Kont.seq .hole (wrL l)).HasHnd m = false := fun m => by simp [Kont.HasHnd]
  have hKC : ∀ m, (Kont.seq .hole (wrL l)).Catches m = false := fun m => by simp [Kont.Catches]
  refine erwp_performG (T := T2C) (en := yCEnt) (K := .seq .hole (wrL l)) (hKH 6)
    (by simp [T2C]) rfl (compS_empty_left _) ⟨rfl, rfl⟩ (fun h => by cases h)
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
  · -- the cancel run: `raise cancel` under the plain context, the borrow garbage
    cases hP
    show erwp (ℍ := ℍ) Φ₀ (cancelTabN OpTabN.empty) (fun _ _ _ _ => False) k ls' _ _
    rw [dead_plain _ hKH (hKC 0), erwp_eq]
    exact rwpG_here (final_opPlug (r := true) (payloadName_cancelVal none) (hKC 0))
      (Or.inr (Or.inl ⟨_, none, pure_sep_mk ⟨rfl, hKC 0⟩
        ⟨PMap.empty, _, compS_empty_left _, emp_empty, noOwn_single_mut l⟩⟩))

/-- The loop's invariant over a fixed cell. -/
def ILl (l : Loc) : Val → WProp := fun s ρ => ∃ u, s = Val.loc l ∧ ptoOwn l u ρ

/-- The loop's normal exit: never. -/
def QF : PostN := fun _ _ _ _ => False

theorem QF_down : QF.Down := fun _ _ _ _ h => h

theorem T2L_ctxClosed (A : Life) (l : Loc) (K : Kont) (hH : ∀ m, K.HasHnd m = false)
    (hC : ∀ m, K.Catches m = false) : (T2L (ℍ := ℍ) A l).CtxClosed K :=
  claimT_ctxClosed Φ₀_down K hH hC T2C_finNone (empty_ctxClosed K)

/-- **A turn, `y` cancellable**: the lend by `erwp_M_frameC`. -/
theorem turn_okC (A : Life) (l : Loc) (k : Nat) (s : Val) (ls : List SRec) (ρ : WRes)
    (hI : ILl l s ρ) :
    erwp (ℍ := ℍ) Φ₀ (opTableN (T2L (ℍ := ℍ) A l)) (turnPostN (ILl l) QF) k ls
      (.app (.app (.val fT) (.val s)) (.val nextV)) ρ := by
  obtain ⟨u, rfl, rfl⟩ := hI
  have hD := opTableN_down (T2L_down (ℍ := ℍ) A l)
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
    (T2L_ctxClosed A l _ (fun m => by simp [Kont.HasHnd]) (fun m => by simp [Kont.Catches]))
    k ?_ k le_rfl ls _ _ ?_
  · rintro k' ls' v σ - ⟨rfl, w, rfl⟩
    refine erwp_det Φ₀_down hD hTP (fun μ => step1Only_plug (Head.seq μ _) rfl .hole) ?_
    exact erwp_val (v := Val.inj₂ (Val.loc l)) (.inr ⟨Val.loc l, rfl, w, rfl, rfl⟩)
  · exact erwp_M_frameC (Φ := Φ₀) rfl (famF_down A) (T2C_lendOKC A) (empty_lendOK A) T2C_fin
      k k le_rfl ls (lendE l) u PMap.empty _ PMap.empty _ (inStratum_empty A) (inStratum_empty _)
      (famF A k) (fun _ _ h => h) rfl (ResU.comp_empty_right _) (ResU.comp_empty_right _)
      (lend_okC l A u k ls)

/-! ### The body: the cell, its finaliser, the loop -/

/-- `λ_. free ℓ`. -/
def dF (l : Loc) : Val := Val.lam (freeE (.val (Val.loc l)))

/-- `λc. ubind (λ_. free c, λ_. free c) (iterate (fT, c))`, its body. -/
def bodyCF : Expr :=
  .app (.app (.val (.prim .ubind)) (.pair (.val (Val.lam (freeE (.var 1))))
    (.val (Val.lam (freeE (.var 1)))))) (.app (.val (.prim .iterate)) (.pair (.val fT) (.var 0)))

/-- `(λc. ubind (λ_. free c, λ_. free c) (iterate (fT, c))) (alloc 1)`. -/
def bodyC : Expr := .app (.val (Val.lam bodyCF)) (.app (.val (.prim .alloc)) (.val (Val.i32 1)))

theorem bodyCF_subst (l : Loc) :
    Expr.subst 0 (Val.loc l) bodyCF = ubindE (Val.pair (dF l) (dF l)) (iterateE fT (Val.loc l)) := by
  simp [bodyCF, dF, ubindE, Expr.subst, iterateE, Val.pair, Val.lam, Val.loc, freeE, Expr.val,
    Expr.shift, Val.prim, subst_closedAt _ _ (show closedAt 0 fT.1 = true from rfl) (Nat.zero_le _)]

/-- **The finaliser consumes the claim.** -/
theorem dF_ok (A : Life) (l : Loc) (k : Nat) (ls : List SRec) (ρ : WRes)
    (h : claimR l A (famF A) k ρ) :
    rwp (ℍ := ℍ) Φ₀ (fun _ _ _ ρ' => ρ' = PMap.empty) k ls (.app (.val (dF l)) (.val .unit)) ρ := by
  obtain ⟨w, σ, hσ, hF, hc⟩ := h
  have hσ0 : σ = PMap.empty := hF
  subst hσ0
  obtain rfl := ResU.CompS.functional hc (ResU.comp_empty_right _)
  rw [rwp_iff_rwpG]
  refine rwpG_det Φ₀_down (fun _ _ _ _ ⟨v, hv, hq⟩ => ⟨v, hv, hq⟩)
    (fun μ => step1Only_plug (Head.beta μ _ Val.unit) rfl .hole) ?_
  have e : Kont.hole.plug (Expr.subst 0 Val.unit (freeE (.val (Val.loc l)))) =
      (.app (.val (.prim .free)) (.val (.loc l)) : Expr) := by
    simp [Expr.subst, Kont.plug, freeE, Val.loc, Expr.val, Val.prim]
  rw [e, ← rwp_iff_rwpG]
  exact rwp_free ls l w _ ⟨_, PMap.empty, ResU.comp_empty_right _, rfl, rfl⟩

theorem T2C_e : ∀ m i en, T2C (ℍ := ℍ) m i = some en → en.abort = false ∧ en.q ≠ .unr :=
  fun _ _ en h => by rcases T2C_ent h with rfl | rfl <;> exact ⟨rfl, by simp [yCEnt, tickEnt]⟩

theorem body_okC (A : Life) (n : Nat) :
    erwp (ℍ := ℍ) Φ₀ (opTableN (T2C (ℍ := ℍ))) QZ n [] bodyC (PMap.empty : WRes) := by
  have hD := opTableN_down (T2C_down (ℍ := ℍ))
  refine erwp_alloc Φ₀_down (opTableN_local _) (.appR (.val (Val.lam bodyCF)) .hole) (Val.i32 1)
    (fun l σ₁ σ₂ hcell hc => ?_)
  obtain rfl := eq_of_compS_empty_left hc
  refine erwp_det Φ₀_down hD QZ_down (fun μ => step1Only_plug (Head.beta μ _ _) rfl .hole) ?_
  rw [Kont.plug_hole, bodyCF_subst]
  refine erwp_ubindClaim Φ₀_down T2C_down empty_down (fun _ _ _ h => by cases h) T2C_e T2C_fin
    (dF l) (dF l) (dF_ok A l) QZ_down (Qin := QF) (fun _ _ _ _ h => h.elim) _ _ _ _ ?_
  refine erwp_iterate Φ₀_down (T2L_down A l)
    (T2L_ctxClosed A l _ (fun m => by simp [iterK, Kont.HasHnd])
      (fun m => by simp [iterK, Kont.Catches])) QF_down rfl (I := ILl l) (en := tickEnt)
    (by simp [OpTabN.claimT, T2C, T1, tickEnt, Stage1.divEff_ne6]) rfl rfl
    (fun _ _ => ⟨rfl, rfl⟩) (fun _ _ _ _ h => h) (fun s ρ ⟨_, hs, _⟩ => by subst hs; rfl)
    (fun k s ls ρ hI => turn_okC A l k s ls ρ hI) _ _ _ _ ⟨Val.i32 1, rfl, hcell⟩

/-! ### The scheduler that cancels `κ`, and the program -/

/-- A computation at the empty table at a postcondition, at every table and every weaker
postcondition. -/
theorem erwp_of_empty_post {Φ : LocFam} {T : OpTabN} {Q Q' : PostN}
    (hQ : ∀ k ls v ρ, Q k ls v ρ → Q' k ls v ρ) {n : Nat} {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) Q n ls e ρ) :
    erwp (ℍ := ℍ) Φ (opTableN T) Q' n ls e ρ := by
  rw [erwp_eq] at h ⊢
  refine rwpG_mono (fun k ls' t σ ht => ?_) h
  rcases ht with ⟨v, hv, hq⟩ | ⟨_, _, _, _, _, h'⟩ | ⟨_, _, _, _, _, h'⟩
  · exact Or.inl ⟨v, hv, hQ _ _ _ _ hq⟩
  · exact absurd (pure_sep_iff.mp h').1.2.2.1 (by simp [OpTabN.empty])
  · exact absurd (pure_sep_iff.mp h').1.2.2.1 (by simp [OpTabN.empty])

/-- **The scheduler's clause** `λ(v, κ). (λc. (free c).2) (alloc κ)`: `κ` stored, taken back and
cancelled. -/
theorem erwp_clDrop {Φ : LocFam} (hΦ : Φ.Down) {T : OpTabN} (hTD : T.Down) {k : Nat}
    {ls : List SRec} {v κ : Val} {ρ : WRes}
    (h : ∀ k', k' < k → erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) unitPost k' ls
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
  exact erwp_of_empty_post (fun _ _ _ _ h => h.1) (h _ (by omega))

/-- `hnd_Y yCancel`: the scheduler, `y` cancellable. -/
def yHC : Val := hndVal 6 (qualsVal [.cancel]) Stage1.idV (Val.pair Stage1.clCancel .unit)

theorem erwp_yHC :
    ∀ n ls e ρ, erwp (ℍ := ℍ) Φ₀ (opTableN (T2C (ℍ := ℍ))) QZ n ls e ρ →
      erwp (ℍ := ℍ) Φ₀ (opTableN T1) QZ n ls (hndE yHC e) ρ := by
  refine erwp_handle Φ₀_down T2C T1 T2C_down T1_down 6 (fun m i hm => by simp [T2C, hm]) _ _ _
    QZ QZ QZ_down ?_ (fun _ => some OpTabN.empty) ?_
    (fun k ls v ρ hv => erwp_idV Φ₀_down T1_down hv) ?_
  · intro i en hT _
    rcases T2C_cases hT with ⟨-, rfl, rfl⟩ | ⟨h6, -, -⟩
    · exact Stage1.capTag_one .cancel
    · exact absurd h6.symm Stage1.divEff_ne6
  · intro i en hT _ _ Tk hTk
    cases hTk
    rcases T2C_cases hT with ⟨-, rfl, rfl⟩ | ⟨h6, -, -⟩
    · exact ⟨OpTabN.empty, rfl, fun _ _ _ h => h, empty_down⟩
    · exact absurd h6.symm Stage1.divEff_ne6
  · intro i en hT
    rcases T2C_cases hT with ⟨-, rfl, rfl⟩ | ⟨h6, -, -⟩
    · refine ⟨Stage1.clCancel, Stage1.clauseAt_pair0 _ _, fun _ k ls v κ ρ hsep => ?_,
        fun h => by cases h⟩
      obtain ⟨ρa, ρk, hc, ⟨-, rfl⟩, -, hK⟩ := hsep
      obtain rfl : ρ = ρk := eq_of_compS_empty_left hc
      refine erwp_clDrop Φ₀_down T1_down fun k' hk' => ?_
      exact (hK ls (extF_refl ls _) k' hk').2 (by simp [yCEnt]) _ rfl
    · exact absurd h6.symm Stage1.divEff_ne6

/-- `hnd_Div rtH (hnd_Y yCancel bodyC)`. -/
def progLendCancel : Expr := hndE DivRuntime.rtH (hndE yHC bodyC)

theorem progLendCancel_ok (n : Nat) :
    erwp (ℍ := ℍ) Φ₀ (opTableN OpTabN.empty) QZ n [] progLendCancel (PMap.empty : WRes) :=
  erwp_rtH Φ₀_down n [] _ _ (erwp_yHC n [] _ _ (body_okC 0 n))

/-- **Unknown 1, the cancel case, the test.** A cell lent `mut` across a cancellable `y` on a
loop with no bound; the scheduler stores `κ` and cancels it; the cancel unwinds through the lend
to the finaliser frame, whose finaliser takes the lend's claim and releases the cell. Every
configuration a run reaches is a value or steps, a value only at the empty memory, and every
`free` finds its cell. No fuel. -/
theorem progLendCancel_orDiverges : OrDiverges (ℍ := ℍ) progLendCancel :=
  erwp_adequacy (Φ := Φ₀) (fun _ _ _ _ h => h) progLendCancel_ok

end BoCa.Fig16.LogRel.Core.Chain.SI.LendProg

end
