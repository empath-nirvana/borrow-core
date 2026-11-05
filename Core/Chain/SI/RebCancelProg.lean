import Core.Chain.SI.RebProg
import Core.Chain.SI.RebCancelC
import Core.Chain.SI.ILendCancelProg

/-!
# The test, the cancel case: a reborrow of a borrowed field live across a `yield` whose `κ` the
scheduler cancels

    progRebCancel = hnd_Div rtH (hnd_Y yCancel (
                    (λe. (λd. (λc. ubind (D, D) (iterate (fR, c))) (alloc d)) (alloc u₀)) (alloc ())))

    D = λ_. (λ_. (λ_. free c) (free d)) (free e)

As `progReb`, with `y` cancellable. The scheduler stores the first `y`'s `κ`, takes it back and
cancels it: the cancel run unwinds through the reborrow (`erwp_reborrowT`: the reborrow folded at
the stop and re-entered at the canonical image, its cancel run owning nothing) and the `imm` lend
(`erwp_I_frameC`: the lender's cancel run carrying the claim `c ↦ own(d) ● d ↦ own(u₀) ● e ↦ own(())`)
to the finaliser frame, whose finaliser frees the three cells.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core.Chain.SI.RebProg
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel.Core.Chain.SI.LendProg
open BoCa.Fig16.LogRel.Core.Chain.SI.ILendProg
open BoCa.BoLo (Heap Step1 Steps Head Kont performE raiseE cancelVal opPayload freeE hndE hndVal
  clauseAt capTag ubindE)
open BoCa.Lifetime (LSub LifeVar)

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

theorem T2C_rebOKC (β : Life) : (T2C (ℍ := ℍ)).RebOKC β where
  entry := (T2C_lendOKC β).entry
  pa := fun _ _ en h _ _ _ ρ hA => by
    rcases T2C_ent h with rfl | rfl <;>
    · obtain ⟨-, rfl⟩ := hA
      exact inStratum_empty β
  pb := fun _ _ en h _ _ _ ρ hB => by
    rcases T2C_ent h with rfl | rfl <;>
    · obtain ⟨-, rfl⟩ := hB
      exact inStratum_empty β

theorem empty_rebOK (β : Life) : OpTabN.empty.RebOK β where
  entry := fun _ _ _ h => by cases h
  pa := fun _ _ _ h => by cases h
  pb := fun _ _ _ h => by cases h

/-- **The reborrowed computation, `y` cancellable**: as `rebBody_ok`; its cancel run is the
`raise` at once, the image garbage. -/
theorem rebBodyC_ok (c d : Loc) (R₀ : WRes) (A β : Life) (k : Nat)
    (ls : List SRec) (Bχ : WRes) (P : Val → WProp)
    (hpto : ptoImm d β P Bχ) :
    erwp (ℍ := ℍ) Φ₀ (opTableN (T2C (ℍ := ℍ)))
      (RebPost β (IFPost c (.loc d) (PR d R₀) A (Qt c d R₀))) k ls
      (.seq Stage1.yE (useR d)) Bχ := by
  have hKH : ∀ m, (Kont.seq .hole (useR d)).HasHnd m = false := fun m => by simp [Kont.HasHnd]
  have hKC : ∀ m, (Kont.seq .hole (useR d)).Catches m = false := fun m => by simp [Kont.Catches]
  have hnoχ : NoOwn Bχ := by
    obtain ⟨s, u', σ, hs, rfl, -, -⟩ := hpto
    exact noOwn_single_imm d _ _ _ _
  refine erwp_performG (T := T2C) (en := yCEnt) (K := .seq .hole (useR d)) (hKH 6)
    (by simp [T2C]) rfl (compS_empty_left _) ⟨rfl, rfl⟩ (fun h => by cases h)
    (fun ls' _ k' hk' w σB XB hB hXB => ?_) (fun ls' _ _ P' hP => ?_)
  · obtain ⟨rfl, rfl⟩ := hB
    obtain rfl := ResU.CompS.functional hXB (ResU.comp_empty_right _)
    cases k' with
    | zero => exact erwp_zero
    | succ k₀ =>
    refine erwp_step (opTableN_local _) (fun μ => step1Only_plug (Head.seq μ _) rfl .hole) ?_
    have hplug : useR d = (Kont.appR (.val discardV) .hole).plug (ldR d) := rfl
    rw [hplug]
    refine erwp_bindR Φ₀_down (opTableN_local _) (Kont.appR (.val discardV) .hole)
      (rwp_load_I ls' d β P _ ⟨_, PMap.empty, ResU.comp_empty_right _, hpto,
        fun v ρc X hc hX => ?_⟩)
    obtain rfl := eq_of_compS_empty_left hX
    obtain ⟨s, u', σ, hs, rfl, -, -⟩ := hc
    generalize k₀ - 1 = k₁
    cases k₁ with
    | zero => exact erwp_zero
    | succ k₂ =>
    refine erwp_step (opTableN_local _) (fun μ => step1Only_plug (Head.beta μ _ v) rfl .hole) ?_
    have e₁ : Kont.hole.plug (Expr.subst 0 v (.val Val.unit)) = (Val.unit).1 := by
      simp [Expr.subst, Kont.plug, Val.unit, Expr.val]
    rw [e₁]
    refine erwp_garbage (compS_empty_left _) (noOwn_single_imm d _ _ _ _) (erwp_val ?_)
    refine ⟨⟨fun ρl Y hl hY ρv Z hv hZ => ?_, inStratum_empty A⟩, inStratum_empty β⟩
    obtain ⟨-, rfl⟩ := hv
    subst hl
    obtain rfl := eq_of_compS_empty_left hY
    exact ⟨rfl, hZ⟩
  · -- the cancel run: `raise cancel` under the plain context, the image garbage
    cases hP
    show erwp (ℍ := ℍ) Φ₀ (cancelTabN OpTabN.empty) (fun _ _ _ _ => False) k ls' _ _
    rw [dead_plain _ hKH (hKC 0), erwp_eq]
    exact rwpG_here (final_opPlug (r := true) (payloadName_cancelVal none) (hKC 0))
      (Or.inr (Or.inl ⟨_, none, pure_sep_mk ⟨rfl, hKC 0⟩
        ⟨PMap.empty, _, compS_empty_left _, emp_empty, hnoχ⟩⟩))

/-- **The lent computation, `y` cancellable**: `lendRG_ok`'s steps, with `erwp_reborrowT`. -/
theorem lendRC_ok (c d e : Loc) (R₀ : WRes)
    (hR₀ : ResU.CompS (ResU.single d (CellU.ownOf u₀)) (ResU.single e (CellU.ownOf .unit)) R₀)
    (A : Life) (houtP : R₀.InStratum A) (k : Nat) (ls : List SRec)
    (ds : List FrameRec) (BI : WRes)
    (hBI : ResU.CompS PMap.empty
      (ResU.single c (CellU.immOf (LSet.singleton A) (.loc d) R₀ houtP)) BI) :
    erwp (ℍ := ℍ) Φ₀ (opTableN (T2C (ℍ := ℍ))) (IFPost c (.loc d) (PR d R₀) A (Qt c d R₀)) k
      (frameList (recR c d R₀) ds A ls) (lendRE c) BI := by
  obtain rfl := eq_of_compS_empty_left hBI
  set lsF := frameList (recR c d R₀) ds A ls with hlsF
  have hplug : lendRE c = (Kont.appR (.val lamX) .hole).plug (ldR c) := rfl
  rw [hplug]
  refine erwp_bindR Φ₀_down (opTableN_local _) _ (rwp_load_I lsF c A
    (fun v σ => v = .loc d ∧ σ = R₀) _ ⟨_, PMap.empty, ResU.comp_empty_right _,
      ⟨LSet.singleton A, .loc d, R₀, houtP, rfl, ⟨rfl, rfl⟩, le_refl _⟩,
      fun v ρc X hc hX => ?_⟩)
  obtain rfl := eq_of_compS_empty_left hX
  obtain ⟨s, v', σ, hs, rfl, hsep, hAs⟩ := hc
  obtain ⟨rfl, ⟨rfl, hσ⟩⟩ := pure_sep_iff.mp hsep
  subst σ
  generalize k - 1 = k'
  cases k' with
  | zero => exact erwp_zero
  | succ k₀ =>
  refine erwp_step (opTableN_local _)
    (fun μ => step1Only_plug (Head.beta μ _ (Val.loc d)) rfl .hole) ?_
  have e₁ : Kont.hole.plug (Expr.subst 0 (Val.loc d)
      (.seq Stage1.yE (.app (.val discardV) (.app (.val (.prim .load)) (.var 0))))) =
      .seq Stage1.yE (useR d) := by
    simp [Expr.subst, Kont.plug, Stage1.yE, useR, discardV, ldR, performE, opPayload, Val.pair,
      Val.i32, Val.unit, Val.loc, Expr.val, Val.prim, Val.lam]
  rw [e₁]
  have hS := recR_tmpl (c := c) hR₀
  have hRβ := R₀_inStratum (↓A) hR₀
  have hshape := canon_ref (r := recR c d R₀) (S := .thunk .top) rfl
    (x := 0) (by simp [VFree, CFree]) hS hRβ
    (fun ℓ h => ⟨u₀, by rw [show ℓ = d from (BoCa.Val.loc_inj.mp h).symm]; exact pair_get_left hR₀⟩)
  have hr : recR c d R₀ ∈ rsOf lsF := by rw [hlsF, rsOf_frameList]; exact List.mem_cons_self
  refine erwp_reborrowT (recR c d R₀) 0 (rT_free 0) hS hRβ hshape (T2C_rebOKC (↓A))
    (empty_rebOK (↓A)) T2C_fin (down_le_of_meet hAs) k₀ lsF _ PMap.empty _
    (ResU.comp_empty_right _) (inStratum_empty _) hr (fun Bχ hBχ => ?_)
  obtain rfl := eq_of_compS_empty_left hBχ
  obtain ⟨β', hint, ℓ, hk⟩ := hshape
  obtain ⟨hv, hpto⟩ := pure_sep_iff.mp hk
  have hℓ : ℓ = d := (BoCa.Val.loc_inj.mp hv).symm
  subst ℓ
  have hβ' : β' = ↓A := by
    simp [BoCa.Lifetime.Life.interp, find?_extend_self] at hint
    exact (Option.some.inj hint).symm
  subst hβ'
  exact rebBodyC_ok c d R₀ A _ k₀ lsF _ _ hpto

/-! ### The turn -/

/-- The body's table: `T2C` with the `imm` lend's claim at `c`. -/
abbrev T2R (c d : Loc) (R₀ : WRes) : OpTabN :=
  @OpTabN.claimT ℍ _ (T2C (ℍ := ℍ)) Φ₀ OpTabN.empty (claimI c (.loc d) R₀)

theorem T2R_down (c d : Loc) (R₀ : WRes) : (T2R (ℍ := ℍ) c d R₀).Down where
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

theorem T2R_ctxClosed (c d : Loc) (R₀ : WRes) (K : Kont) (hH : ∀ m, K.HasHnd m = false)
    (hC : ∀ m, K.Catches m = false) : (T2R (ℍ := ℍ) c d R₀).CtxClosed K :=
  claimT_ctxClosed Φ₀_down K hH hC T2C_finNone (empty_ctxClosed K)

/-- The loop's invariant over the fixed cells. -/
def IRf (c d : Loc) (R₀ : WRes) : Val → WProp := fun s ρ =>
  s = Val.loc c ∧ ResU.CompS (ResU.single c (CellU.ownOf (.loc d))) R₀ ρ

/-- **A turn, `y` cancellable**: the lend by `erwp_I_frameC`, the reborrow inside it by
`erwp_reborrowT`. -/
theorem turnRC_ok (c d e : Loc) (R₀ : WRes)
    (hR₀ : ResU.CompS (ResU.single d (CellU.ownOf u₀)) (ResU.single e (CellU.ownOf .unit)) R₀)
    (k : Nat) (s : Val) (ls : List SRec) (ρ : WRes) (hI : IRf c d R₀ s ρ) :
    erwp (ℍ := ℍ) Φ₀ (opTableN (T2R (ℍ := ℍ) c d R₀)) (turnPostN (IRf c d R₀) QF) k ls
      (.app (.app (.val fR) (.val s)) (.val nextV)) ρ := by
  obtain ⟨rfl, hρ⟩ := hI
  have hD := opTableN_down (T2R_down (ℍ := ℍ) c d R₀)
  have hTP : (turnPostN (IRf c d R₀) QF).Down := fun _ _ _ _ h => by
    rcases h with ⟨x, hx, hq⟩ | h
    · exact .inl ⟨x, hx, hq⟩
    · exact .inr h
  refine erwp_det Φ₀_down hD hTP
    (fun μ => step1Only_plug (Head.beta μ _ (Val.loc c)) rfl (.appL .hole nextV)) ?_
  have e₁ : (Kont.appL .hole nextV).plug (Expr.subst 0 (Val.loc c)
      (.lam (.case (.var 0) (.seq (.app (.val lamX) (.app (.val (.prim .load)) (.var 2)))
        (.inj₂ (.var 2))) (.val .unit)))) =
      Kont.hole.plug (.app (.val (Val.lam (.case (.var 0)
        (.seq (lendRE c) (.inj₂ (.val (Val.loc c)))) (.val .unit)))) (.val nextV)) := by
    simp [Expr.subst, Expr.shift, Kont.plug, lamX, discardV, lendRE, ldR, Stage1.yE, performE,
      opPayload, Val.pair, Val.i32, Val.unit, Val.lam, Val.loc, Expr.val, Val.prim, Val.shift]
  rw [e₁]
  refine erwp_det Φ₀_down hD hTP (fun μ => step1Only_plug (Head.beta μ _ nextV) rfl .hole) ?_
  have e₂ : Kont.hole.plug (Expr.subst 0 nextV (.case (.var 0)
        (.seq (lendRE c) (.inj₂ (.val (Val.loc c)))) (.val .unit))) =
      Kont.hole.plug (.case (.val (Val.inj₁ Val.unit))
        (.seq (lendRE c) (.inj₂ (.val (Val.loc c)))) (.val .unit)) := by
    simp [Expr.subst, Kont.plug, lamX, discardV, lendRE, ldR, Stage1.yE, performE, opPayload,
      Val.pair, Val.i32, Val.unit, nextV, Val.inj₁, Val.loc, Expr.val, Val.prim, Val.lam]
  rw [e₂]
  refine erwp_det Φ₀_down hD hTP
    (fun μ => step1Only_plug (Head.case₁ μ Val.unit _ _) rfl .hole) ?_
  have e₃ : Kont.hole.plug (Expr.subst 0 Val.unit
        (.seq (lendRE c) (.inj₂ (.val (Val.loc c))))) =
      (Kont.seq .hole (.inj₂ (.val (Val.loc c)))).plug (lendRE c) := by
    simp [Expr.subst, Kont.plug, lamX, discardV, lendRE, ldR, Stage1.yE, performE, opPayload,
      Val.pair, Val.i32, Val.unit, Val.loc, Expr.val, Val.prim, Val.lam]
  rw [e₃]
  refine erwp_bind_le (Q' := Qt c d R₀) Φ₀_down _ (fun m => by simp [Kont.HasHnd])
    (fun m => by simp [Kont.Catches])
    (T2R_ctxClosed c d R₀ _ (fun m => by simp [Kont.HasHnd]) (fun m => by simp [Kont.Catches]))
    k ?_ k le_rfl ls _ _ ?_
  · rintro k' ls' v σ - ⟨hv, hσ⟩
    obtain rfl : v = Val.unit := hv
    refine erwp_det Φ₀_down hD hTP (fun μ => step1Only_plug (Head.seq μ _) rfl .hole) ?_
    exact erwp_val (v := Val.inj₂ (Val.loc c)) (.inr ⟨Val.loc c, rfl, rfl, hσ⟩)
  · obtain ⟨A, -⟩ := exists_fresh ls
    have hshape : vShape rT δ₀ (.loc d) R₀ :=
      ⟨d, u₀, pure_sep_mk rfl ⟨_, _, hR₀, rfl, trivial⟩⟩
    have hadm : AdmWf rT δ₀ := fun y hy => by simp [rT, VFree, CFree] at hy
    have hex : ExS R₀ R₀ := (ExS.split hR₀).mpr ⟨_, _, ExW.single_own d u₀,
      ExW.single_own e Val.unit, hR₀⟩
    obtain ⟨ds, hds⟩ := lineage_list (r := recR c d R₀) hshape hadm hex
    have houtP : R₀.InStratum A := R₀_inStratum A hR₀
    exact erwp_I_frameC (Φ := Φ₀) c rT δ₀ hadm (.loc d) (PR d R₀)
      (fun _ ρ' h => by obtain ⟨-, rfl⟩ := h; exact hshape)
      (fun _ _ _ _ h => h) (T2C_ilendOKC A) (empty_ilendOK A) T2C_fin houtP hshape hρ hds
      (fun _ _ _ _ _ _ h => h) k ls (lendRE c) PMap.empty ρ (inStratum_empty A) ⟨rfl, rfl⟩
      (ResU.comp_empty_right _) (lendRC_ok c d e R₀ hR₀ A houtP k ls ds)

/-! ### The finaliser -/

/-- `λ_. (λ_. (λ_. free c) (free d)) (free e)`. -/
def D3v (c d e : Loc) : Val :=
  Val.lam (.app (.val (Val.lam (.app (.val (Val.lam (freeE (.val (Val.loc c)))))
    (freeE (.val (Val.loc d)))))) (freeE (.val (Val.loc e))))

/-- `(λ_. M) (free x)`, `M` closed: the cell freed, then `M`. -/
theorem rwp_lam_free (M : Expr) (hM : ∀ v, Expr.subst 0 v M = M) (x : Loc) (v : Val)
    {ls : List SRec} {ρ' ρ : WRes} (hc : ResU.CompS (ResU.single x (CellU.ownOf v)) ρ' ρ)
    (h : ∀ k, rwp (ℍ := ℍ) Φ₀ (fun _ _ _ ρ'' => ρ'' = PMap.empty) k ls M ρ') (n : Nat) :
    rwp (ℍ := ℍ) Φ₀ (fun _ _ _ ρ'' => ρ'' = PMap.empty) n ls
      (.app (.val (Val.lam M)) (freeE (.val (Val.loc x)))) ρ := by
  have hplug : (Expr.app (.val (Val.lam M)) (freeE (.val (Val.loc x)))) =
      (Kont.appR (.val (Val.lam M)) .hole).plug (freeE (.val (Val.loc x))) := rfl
  rw [hplug]
  refine rwp_bind Φ₀_down _ (rwp_free ls x v _ ⟨_, ρ', hc, rfl, ?_⟩)
  rw [rwp_iff_rwpG]
  refine rwpG_det Φ₀_down (fun _ _ _ _ ⟨w, hw, hq⟩ => ⟨w, hw, hq⟩)
    (fun μ => step1Only_plug (Head.beta μ _ v) rfl .hole) ?_
  rw [Kont.plug_hole, hM, ← rwp_iff_rwpG]
  exact h _

/-- **The finaliser frees the lend's claim**: `c ↦ own(d) ● d ↦ own(u₀) ● e ↦ own(())`. -/
theorem D3_ok (c d e : Loc) (R₀ : WRes)
    (hR₀ : ResU.CompS (ResU.single d (CellU.ownOf u₀)) (ResU.single e (CellU.ownOf .unit)) R₀)
    (k : Nat) (ls : List SRec) (ρ : WRes) (h : claimI c (.loc d) R₀ k ρ) :
    rwp (ℍ := ℍ) Φ₀ (fun _ _ _ ρ' => ρ' = PMap.empty) k ls
      (.app (.val (D3v c d e)) (.val .unit)) ρ := by
  obtain ⟨cd, hcd, hcde⟩ := compS_reassoc' hR₀ h
  rw [rwp_iff_rwpG]
  refine rwpG_det Φ₀_down (fun _ _ _ _ ⟨v, hv, hq⟩ => ⟨v, hv, hq⟩)
    (fun μ => step1Only_plug (Head.beta μ _ Val.unit) rfl .hole) ?_
  have e₀ : Kont.hole.plug (Expr.subst 0 Val.unit (.app (.val (Val.lam (.app (.val (Val.lam
      (freeE (.val (Val.loc c))))) (freeE (.val (Val.loc d)))))) (freeE (.val (Val.loc e))))) =
      .app (.val (Val.lam (.app (.val (Val.lam (freeE (.val (Val.loc c)))))
        (freeE (.val (Val.loc d)))))) (freeE (.val (Val.loc e))) := by
    simp [Expr.subst, Kont.plug, freeE, Val.loc, Expr.val, Val.prim, Val.lam]
  rw [e₀, ← rwp_iff_rwpG]
  refine rwp_lam_free _ (fun v => by simp [Expr.subst, freeE, Val.loc, Expr.val, Val.prim,
    Val.lam]) e Val.unit (ResU.CompS.comm hcde) (fun k₁ => ?_) k
  refine rwp_lam_free _ (fun v => by simp [Expr.subst, freeE, Val.loc, Expr.val, Val.prim])
    d u₀ (ResU.CompS.comm hcd) (fun k₂ => ?_) k₁
  exact rwp_free ls c (.loc d) _ ⟨_, PMap.empty, ResU.comp_empty_right _, rfl, rfl⟩

/-! ### The program -/

/-- The finaliser frame and the loop over `c`, given the finaliser. -/
def bodyCF (D : Val) : Expr :=
  .app (.app (.val (.prim .ubind)) (.pair (.val D) (.val D)))
    (.app (.val (.prim .iterate)) (.pair (.val fR) (.var 0)))

/-- The finaliser under `λe. λd. λc`. -/
def D3var : Val :=
  Val.lam (.app (.val (Val.lam (.app (.val (Val.lam (freeE (.var 3)))) (freeE (.var 3)))))
    (freeE (.var 3)))

/-- …once `e` is known. -/
def D3e (e : Loc) : Val :=
  Val.lam (.app (.val (Val.lam (.app (.val (Val.lam (freeE (.var 3)))) (freeE (.var 3)))))
    (freeE (.val (Val.loc e))))

/-- …once `d` and `e` are known. -/
def D3de (d e : Loc) : Val :=
  Val.lam (.app (.val (Val.lam (.app (.val (Val.lam (freeE (.var 3))))
    (freeE (.val (Val.loc d)))))) (freeE (.val (Val.loc e))))

/-- `λd. (λc. bodyCF D) (alloc d)`. -/
def lamDC (D : Val) : Val := Val.lam (.app (.val (Val.lam (bodyCF D))) (.app (.val (.prim .alloc)) (.var 0)))

/-- `(λe. lamDC D3var (alloc u₀)) (alloc ())`. -/
def bodyRC : Expr :=
  .app (.val (Val.lam (.app (.val (lamDC D3var)) (.app (.val (.prim .alloc)) (.val u₀)))))
    (.app (.val (.prim .alloc)) (.val Val.unit))

/-- `hnd_Div rtH (hnd_Y yCancel bodyRC)`. -/
def progRebCancel : Expr := hndE DivRuntime.rtH (hndE yHC bodyRC)

theorem bodyRC_ok (n : Nat) :
    erwp (ℍ := ℍ) Φ₀ (opTableN (T2C (ℍ := ℍ))) QZ n [] bodyRC (PMap.empty : WRes) := by
  have hD := opTableN_down (T2C_down (ℍ := ℍ))
  have hL := opTableN_local (T2C (ℍ := ℍ))
  refine erwp_alloc Φ₀_down hL (.appR (.val (Val.lam (.app (.val (lamDC D3var))
    (.app (.val (.prim .alloc)) (.val u₀))))) .hole) Val.unit (fun e σ₁ σ₂ hcell hc => ?_)
  obtain rfl := eq_of_compS_empty_left hc
  refine erwp_det Φ₀_down hD QZ_down (fun μ => step1Only_plug (Head.beta μ _ _) rfl .hole) ?_
  have h₁ : Kont.hole.plug (Expr.subst 0 (Val.loc e)
      (.app (.val (lamDC D3var)) (.app (.val (.prim .alloc)) (.val u₀)))) =
      (Kont.appR (.val (lamDC (D3e e))) .hole).plug (.app (.val (.prim .alloc)) (.val u₀)) := by
    simp [Expr.subst, Expr.shift, Kont.plug, lamDC, bodyCF, D3var, D3e, fR, lamX, discardV, u₀, Stage1.idV,
      Stage1.yE, performE, opPayload, freeE, Val.pair, Val.i32, Val.unit, Val.loc, Expr.val,
      Val.prim, Val.lam]
  rw [h₁]
  refine erwp_alloc Φ₀_down hL (.appR (.val (lamDC (D3e e))) .hole) u₀
    (fun d τ₁ τ₂ hcd hcd' => ?_)
  refine erwp_det Φ₀_down hD QZ_down (fun μ => step1Only_plug (Head.beta μ _ _) rfl .hole) ?_
  have h₂ : Kont.hole.plug (Expr.subst 0 (Val.loc d)
      (.app (.val (Val.lam (bodyCF (D3e e)))) (.app (.val (.prim .alloc)) (.var 0)))) =
      (Kont.appR (.val (Val.lam (bodyCF (D3de d e)))) .hole).plug
        (.app (.val (.prim .alloc)) (.val (Val.loc d))) := by
    simp [Expr.subst, Expr.shift, Kont.plug, bodyCF, D3e, D3de, fR, lamX, discardV, Stage1.yE, performE,
      opPayload, freeE, Val.pair, Val.i32, Val.unit, Val.loc, Expr.val, Val.prim, Val.lam]
  rw [h₂]
  refine erwp_alloc Φ₀_down hL (.appR (.val (Val.lam (bodyCF (D3de d e)))) .hole) (Val.loc d)
    (fun c υ₁ υ₂ hcc hcc' => ?_)
  refine erwp_det Φ₀_down hD QZ_down (fun μ => step1Only_plug (Head.beta μ _ _) rfl .hole) ?_
  have h₃ : Kont.hole.plug (Expr.subst 0 (Val.loc c) (bodyCF (D3de d e))) =
      ubindE (Val.pair (D3v c d e) (D3v c d e)) (iterateE fR (Val.loc c)) := by
    simp [Expr.subst, Kont.plug, bodyCF, D3de, D3v, ubindE, iterateE, freeE, Val.pair, Val.lam,
      Val.loc, Expr.val, Val.prim, Expr.shift,
      subst_closedAt _ _ (show closedAt 0 fR.1 = true from rfl) (Nat.zero_le _)]
  rw [h₃]
  subst hcell hcd hcc
  have hR₀ := ResU.CompS.comm hcd'
  refine erwp_ubindClaim Φ₀_down T2C_down empty_down (fun _ _ _ h => by cases h) T2C_e T2C_fin
    (D3v c d e) (D3v c d e) (D3_ok c d e _ hR₀) QZ_down (Qin := QF) (fun _ _ _ _ h => h.elim)
    _ _ _ _ ?_
  refine erwp_iterate Φ₀_down (T2R_down c d _)
    (T2R_ctxClosed c d _ _ (fun m => by simp [iterK, Kont.HasHnd])
      (fun m => by simp [iterK, Kont.Catches])) QF_down rfl (I := IRf c d _) (en := tickEnt)
    (by simp [OpTabN.claimT, T2C, T1, tickEnt, Stage1.divEff_ne6]) rfl rfl
    (fun _ _ => ⟨rfl, rfl⟩) (fun _ _ _ _ h => h) (fun s ρ ⟨hs, _⟩ => by subst hs; rfl)
    (fun k s ls ρ hI => turnRC_ok c d e _ hR₀ k s ls ρ hI) _ _ _ _
    ⟨rfl, ResU.CompS.comm hcc'⟩

theorem progRebCancel_ok (n : Nat) :
    erwp (ℍ := ℍ) Φ₀ (opTableN OpTabN.empty) QZ n [] progRebCancel (PMap.empty : WRes) :=
  erwp_rtH Φ₀_down n [] _ _ (erwp_yHC n [] _ _ (bodyRC_ok n))

/-- **The reborrow cancel test.** As `progReb_orDiverges`, with `y` cancellable and the scheduler
cancelling the stored `κ`: the cancel unwinds through the live reborrow and the `imm` lend to the
finaliser frame, whose finaliser frees the three cells. Every configuration a run reaches is a
value or steps, a value only at the empty memory, and every `free` finds its cell. No fuel. -/
theorem progRebCancel_orDiverges : OrDiverges (ℍ := ℍ) progRebCancel :=
  erwp_adequacy (Φ := Φ₀) (fun _ _ _ _ h => h) progRebCancel_ok

end BoCa.Fig16.LogRel.Core.Chain.SI.RebProg

end
