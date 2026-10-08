import ProbeD1.NxGuardPair

/-!
# ProbeD1 — step 3.0 after the edits (`NEXT.md` §3.1, §1.3's item 1a′)

* **`MuAdjVRLME1`** (`muAdjVRLME1`): after (E1), `GAP.md` §4's adjacency closure `Λ. return ℓ₀` is
  a `vRLM` value at W's own `μX. U(∀'0 ⊏ ⊤. F (Mut '0 1))` over the view `0 ↦ mut(1, (), ∅)` at the
  stack `[muEnt]`. `vRLM`'s `U` clause hands the view back at every instantiation of the stack; the
  `∀` clause's first conjunct then reads one instance, the view's own lifetime, the only value in
  scope; and at every own push (named `'0`, new to the stack, which names `'1`) the closure's answer
  is a `Mut '0 1` view at the pushed instance, the cell at the outer lifetime above it. So
  `muAdjNotVRLM` (proved of `vRLM` at commit `5210cf1`) is false of the edited relation.
* **Item 1a′ at the pair** (`withloadUPairGapNilE1`, `not_withloadPairGapNilInstE1`): the gate's
  world at the empty stack (`ArisesI.nil`), at the reading `'0 ↦ 1`. After (E1) no instance in
  scope is below `⊓Δ`, so the callback's first conjunct reads nothing there, and every single own
  push fails the guard at the reborrowed pair. The relation also reads block pushes; the block
  gate at the empty stack (`LoadGateNilB` at `pairTy`, `loadGateNilB_pairTy`, `GroundBlock.lean`)
  gives, under its hypotheses, a push at which the reborrowed pair meets the guard. At
  `withload`'s thunked type the answer's `U` clause instantiates the push's lifetime below the
  reborrowed cells, where they meet the table.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace ProbeD1
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open GhostEnd (LEnt LStack LKind extS vwE vwS vis stratS ReLend TabAtS jdgCty innerView)

/-! ### `MuAdjVRLME1` -/

/-- `ptoMutS` at an instance at or below the cell's lifetime. -/
theorem ptoMutS_le {l : BoCa.Loc} {α α' : Life} {ls : List SRec}
    {P : List SRec → Val → WProp} {ρ : WRes} (h : ptoMutS l α ls P ρ) (hle : α' ≤ α) :
    ptoMutS l α' ls P ρ := by
  obtain ⟨b, u, σ, hσ, Q, hw, ls₀, hαb, rest⟩ := h
  exact ⟨b, u, σ, hσ, Q, hw, ls₀, le_trans hle hαb, rest⟩

/-- `muEnt`'s view, handed at the stack `[muEnt]` at `α₁`: a `mut` cell exactly at `α₁` storing
`𝒱⟦1⟧`. -/
theorem muEnt_view_of {s : LSub} {α₁ : Life} {ls : List SRec} {ρv : WRes}
    (hv : vwSL s [muEnt] [true] [α₁] ls ρv) :
    ptoMutS 0 α₁ ls (fun ls₀ => vC true .unit ls₀ s) ρv ∧
      ∀ ψ, ρv.get 0 = some ψ → ψ.at = α₁ := by
  obtain ⟨⟨ρ₁, ρ₂, hc, ⟨hvw, hat⟩, hemp⟩, -⟩ := hv
  obtain ⟨rfl, -⟩ := hemp
  rw [ResU.CompS.functional hc (ResU.comp_empty_right ρ₁)]
  exact ⟨hvw, fun ψ hψ => (hat ψ hψ).1⟩

/-- **The view at `Mut '0 1`** at a stack whose innermost entry lending `0` is `muEnt` at `α₁`, at a
reading sending `'0` at or below `α₁`: Core's `Mut` clause (`ptoMutS_le`), `CohS` at `muEnt`, and
`RetainedPay` vacuous at the lent place. -/
theorem muEnt_view_vRLM {σ : LStack} {αs : List Life} {s s' : LSub} {α₁ α : Life}
    {ls : List SRec} {ρv : WRes} (hin : innerAt σ αs 0 = some (muEnt, α₁))
    (hs : (extS s σ αs).find? 0 = some (OrderDual.ofDual α)) (hle : α ≤ α₁)
    (hpt : ptoMutS 0 α₁ ls (fun ls₀ => vC true .unit ls₀ s') ρv)
    (hat : ∀ ψ, ρv.get 0 = some ψ → ψ.at = α₁) :
    vRLM (ℍ := ℍ) .binder0 none σ s (.mut (.var 0) .unit) αs ls (.loc 0) ρv := by
  rw [vRLM_mut_eq, vRLJ_mut_eq]
  refine ⟨⟨OrderDual.ofDual α, hs, 0, pure_sep_iff.mpr ⟨rfl, ptoMutS_le hpt hle⟩⟩,
    fun l e α' hl hi => ?_, fun l hl hi => ?_⟩
  · cases hl
    rw [hin] at hi
    obtain ⟨rfl, rfl⟩ : muEnt = e ∧ α₁ = α' := by simpa using hi
    exact ⟨⟨trivial, TyEq.refl _ _⟩, hat⟩
  · cases hl
    rw [hin] at hi
    cases hi

theorem muAdjTy_noMut : VTy.NoMut 0 (.thunk adjC) := trivial

theorem muAdjTy_cl : (wClose none (VTy.mu (.thunk adjC))).Cl 0 := trivial

/-- **`MuAdjVRLME1`**: after (E1), the adjacency closure is a `vRLM` value at W's own `μ`. -/
theorem muAdjVRLME1 : MuAdjVRLME1 (ℍ := ℍ) := by
  intro h
  apply h
  have hU : vRLM (ℍ := ℍ) .binder0 none [muEnt] adjδ (.thunk adjC) [lifeN 1] []
      (Val.lam (.val (Val.loc 0))) (innerView 0 (lifeN 1)) := by
    rw [vRLM_thunk0]
    intro _ _
    refine ⟨[true], PMap.empty, innerView 0 (lifeN 1), ResU.comp_empty_left _,
      vwSL_innerView _ _ _, fun a _ => ResU.inStratum_empty a,
      fun ι _ ls' _ _ _ _ ρv τ hv hc => ?_⟩
    rw [← ResU.CompS.functional (ResU.comp_empty_left ρv) hc]
    have hsub : ι.sub adjδ = adjδ := by
      cases ι with
      | none => rfl
      | some p => rfl
    rw [hsub] at hv ⊢
    have hlife : ι.life [lifeN 1] = [ι.life1 (lifeN 1)] := rfl
    rw [hlife] at hv ⊢
    generalize ι.life1 (lifeN 1) = α₁ at hv ⊢
    obtain ⟨hpt, hat⟩ := muEnt_view_of hv
    have hin₀ : innerAt [muEnt] [α₁] 0 = some (muEnt, α₁) := by simp [innerAt]
    show cRLM .binder0 [muEnt] adjδ adjC [α₁] ls' (.val (Val.lam (.val (Val.loc 0)))) ρv
    intro ls'' σ' αs' hE hF _
    have hE' : ls'' = ls' := by simpa [ExtQ, Placement.bindFut] using hE
    have hF' : σ' = [muEnt] ∧ αs' = [α₁] := by simpa [FutQI, Placement.bindFut] using hF
    obtain ⟨rfl, rfl⟩ := hF'
    subst hE'
    refine ⟨fun α ρ₁ ρ₂ hp hc' ht hpv => ?_, fun _ en α' hpush _ _ ht hpv => ?_,
      fun _ τ α hpush _ _ => ?_⟩
    · obtain ⟨rfl, -, ⟨q, hq, hqα⟩⟩ := hp
      rw [ResU.CompS.functional hc' (ResU.comp_empty_right ρv)]
      simp only [extS, LSub.extend, List.mem_singleton] at hq
      subst hq
      have hα : α = α₁ := hqα.symm
      subst hα
      refine wpTS_lolli _ _ _ _ _ ?_
      show wpTS _ (.val (Val.loc 0)) _ _
      refine wpTS_val _ _ _ _ ?_
      refine muEnt_view_vRLM hin₀ ?_ le_rfl hpt hat
      show ((LSub.extend adjδ 0 α).extend 1 α).find? 0 = _
      rw [find?_extend_ne _ _ (by decide : (1 : LifeVar) ≠ 0), find?_extend_self]; rfl
    · obtain ⟨⟨x, c, C', hall, hex, -, hoi, -, -⟩, -, -⟩ := hpush
      obtain ⟨rfl, -, rfl⟩ : 0 = x ∧ Lifetime.Life.top = c ∧
          CTy.ret (.mut (.var 0) .unit) = C' := by simpa using hall
      have hl : en.l ≠ 0 := fun h => hoi.place (by rw [h]; simp)
      have hlt : α' < α₁ := by
        have := hoi.chain
        simpa using this
      refine wpTS_lolli _ _ _ _ _ ?_
      show wpTS _ (.val (Val.loc 0)) _ _
      refine wpTS_val _ _ _ _ ?_
      refine muEnt_view_vRLM ?_ ?_ hlt.le hpt hat
      · rw [innerAt_cons, if_neg hl]; exact hin₀
      · show ((extS (LSub.extend adjδ 0 α') [muEnt] [α₁]).extend en.x α').find? 0 = _
        rw [hex, find?_extend_self]; rfl
    · obtain ⟨x, c, C', A, hall, hcb, -⟩ := hpush
      obtain ⟨rfl, -, rfl⟩ : 0 = x ∧ Lifetime.Life.top = c ∧
          CTy.ret (.mut (.var 0) .unit) = C' := by simpa using hall
      rcases hcb with ⟨D, hD⟩ | ⟨D, hD⟩ <;> cases hD
  exact ⟨muAdjTy_noMut, muAdjTy_cl, fun P hP => hP _ _ (by
    rw [vRLM_thunk_env .binder0 _ none]; exact hU)⟩

/-! ### Item 1a re-checked against the edited relation -/

/-- **The gate's configuration after (E1)–(E4)** (`NEXT.md` §1.2, "Which relation"): the witness push
meets `OwnPushM` (its payload type is closed), the index meets `StackJM` (the entry is `pairΔ`'s),
and after (E1) the callback's first conjunct reads no instance at `pc`'s index at any
instantiation: the instantiated reading has one value, the instantiated lend, and every instance
below the bound is below it (`pairBoundBelow`). -/
theorem pairGate_afterEdits :
    OwnPushM ⟨[]⟩ (pairCbUC 1 .unit) PMap.empty ([pE], [pα]) pEn pβ ∧
    StackJM [pE] [pα] ⟨[]⟩ pairΔ pairΓ (.ret .unit) ∧
    ∀ ι : Inst, InstAt [pα] ι → ∀ β, LtLife (extS (ι.sub ⟨[]⟩) [pE] (ι.life [pα]))
      pairΔ.meetOfDom β → ¬ InScope (extS (ι.sub ⟨[]⟩) [pE] (ι.life [pα])) β := by
  refine ⟨⟨pOwnPush _ (empty_not_deepAt 3) (ResU.inStratum_empty _),
    fun y hy => absurd hy (by simp [pEn, VFree]), by simp [pEn, VFree]⟩,
    ⟨⟨by simp [pE], fun e he y hy => ?_, fun e he => ?_⟩, fun e he hΔ _ _ => ?_⟩,
    fun ι _ β hlt hin => ?_⟩
  · rw [List.mem_singleton] at he; subst he
    exact absurd hy (pairTy_closed y)
  · rw [List.mem_singleton] at he; subst he
    exact Or.inl ⟨.top, rfl⟩
  · rw [List.mem_singleton] at he; subst he
    exact absurd hΔ (by simp [pE, LifeCtx.find?, LifeCtx.extend, Lifetime.assocFind])
  · have hsub : ι.sub ⟨[]⟩ = ⟨[]⟩ := by
      cases ι with
      | none => rfl
      | some p => rfl
    rw [hsub] at hlt hin
    have hβ : β < ι.life1 pα := pairBoundBelow ⟨[]⟩ pE (ι.life1 pα) β rfl hlt
    obtain ⟨q, hq, hqβ⟩ := hin
    simp only [Inst.life, List.map_cons, List.map_nil, extS, LSub.extend, pE,
      List.mem_singleton] at hq
    subst hq
    rw [← hqβ] at hβ
    exact lt_irrefl _ hβ

/-! ### Item 1a′ at the pair -/

/-- The gate's world at the empty stack: the frame open, its cell the local part. -/
def pcN : Cfg := ⟨pW₁, PMap.empty, pW₁, [pRec], pls, [], []⟩

/-- The reading whose only value is the frame's lifetime: `'0 ↦ 1`. -/
abbrev δN : LSub := ⟨[(0, 1)]⟩

theorem pcN_arises : ArisesI (ℍ := ℍ) pcN :=
  ArisesI.nil pW₁_tw pW₁_tagged hash_empty_pW₁ (ResU.comp_empty_left _)

/-- `⊓Δ` at `δN` is the frame's lifetime. -/
theorem meetOfDom_δN : (pairΔ.meetOfDom).interp δN = some 1 := rfl

/-- **`SemSM`'s index at the empty stack**, at the frame's cell. -/
theorem pSemIdxN : SemIdxM pairΔ pairΓ (.ret .unit) δN [] [] pls pW₁ := by
  refine ⟨⟨fun x hx => absurd hx (by simp [CTy.binders, VTy.binders]), fun s hs _ x hx => ?_⟩,
    ⟨fun y hy => absurd hy (by simp [CFree, VFree]), fun s hs _ y hy => ?_⟩,
    stackOKB_of_ok _ _ ⟨rfl, List.isChain_nil, List.nodup_nil⟩, fun o ho => absurd ho (by simp),
    ⟨fun e he => absurd he List.not_mem_nil, fun e he => absurd he List.not_mem_nil⟩,
    fun y hy => ?_, ?_,
    fun a ha => absurd ha List.not_mem_nil, fun e a he => absurd he (by simp),
    ⟨fun a ha => absurd ha (by simp), fun a ha => absurd ha (by simp)⟩, pvlNil _ _ _⟩
  · rw [List.mem_singleton] at hs; subst hs
    simp [VTy.binders] at hx
  · rw [List.mem_singleton] at hs; subst hs
    rcases hy with h | h
    · have : y = 0 := by simpa [Lifetime.Life.mentions] using h
      subst this
      exact ⟨.top, rfl⟩
    · exact absurd h (pairTy_closed y)
  · have : y = 0 := by
      by_contra hne
      exact hy (by simp [LSub.find?, Lifetime.assocFind, Ne.symm hne])
    subst this
    exact ⟨.top, rfl⟩
  · intro x u hu
    simp [LifeCtx.find?, LifeCtx.extend, LifeCtx.empty, Lifetime.assocFind] at hu
    obtain ⟨rfl, rfl⟩ := hu
    exact ⟨1, 0, rfl, rfl, show (0 : ℕ) < 1 from Nat.zero_lt_one⟩

/-- **The frame's cell is a `vRLM` value at `Imm '0 (Ref 1 ⊗ Ref 1)` at the empty stack.** -/
theorem pView_vRLM_nil :
    vRLM (ℍ := ℍ) .binder0 none [] δN (.imm (.var 0) pairTy) [] pls (.loc 0) pW₁ := by
  rw [vRLM_imm_eq, vRLJ_imm_eq]
  refine ⟨⟨1, rfl, 0, pure_sep_iff.mpr ⟨⟨rfl, pairTy, δN, TyEq.refl _ _,
    Or.inl ⟨pRec, List.mem_singleton_self _, rfl, rfl, fun y hy => absurd hy (pairTy_closed y)⟩⟩,
    pψ_ptoImmS false δN⟩⟩, fun l e α _ hin => absurd hin (by simp [innerAt]),
    retainedPay_of_closed pairTy_closed⟩

theorem pairNilCfg : PairNilCfg (ℍ := ℍ) pcN pψ pRec 1 2 δN .unit :=
  ⟨pcN_arises, rfl, rfl, ResU.single_get_self _ _, List.mem_singleton_self _,
    List.mem_singleton_self _, rfl, rfl, pψ_wit, pR_1, pR_2, by decide, pSemIdxN,
    pure_sep_iff.mpr ⟨trivial, pW₁, PMap.empty, ResU.comp_empty_right _, pView_vRLM_nil, rfl,
      trivial⟩⟩

/-- The own push at the empty stack, at either callback type of the pair. -/
theorem pOwnPushN {C' : CTy} (hC' : ∀ A D, C' = .arr A D → ViewAt 1 pEn A)
    (hb : 1 ∉ CTy.binders C') (hfreeC : ∀ y, VFree y pEn.T → CFree y (.all 1 pairΔ.meetOfDom C')) :
    OwnPushM δN (.all 1 pairΔ.meetOfDom C') PMap.empty ([], []) pEn pβ :=
  ⟨⟨1, pairΔ.meetOfDom, C', rfl, rfl, hb,
    ⟨⟨List.isChain_singleton _, ResU.inStratum_empty _, List.not_mem_nil, List.not_mem_nil,
      fun y hy => absurd hy (by simp [pEn, VFree])⟩, empty_not_deepAt _⟩,
    ⟨1, meetOfDom_δN, pβ_lt_pα⟩, hC'⟩, hfreeC, by simp [pEn, VFree]⟩

/-- **`WithloadUPairGapNilE1`**: after (E1), at the empty stack, the single own push is the
callback's only single-push route, and it fails the guard at the reborrowed pair. The block push of
the two places is not read by the statement. -/
theorem withloadUPairGapNilE1 : WithloadUPairGapNilE1 (ℍ := ℍ) := by
  refine ⟨pcN, pψ, pRec, 1, 2, δN, .unit, pCbE, 1, pEn, pβ, PMap.empty, pcb, pW₂, pairNilCfg,
    pairProgU_typed,
    pOwnPushN (fun A D h => by cases h; trivial) (by simp [CTy.binders, VTy.binders,
      pairTy_immReborrow]) (fun y hy => absurd hy (by simp [pEn, VFree])),
    pairTy_closed 1, pPairReb, pStratumLe, comp_pW₁_pcb, pW₂_tw, pW₂_tagged,
    fun β' hlt hin => ?_, fun ρk en' β' cb' ρ hpush hreb hc => ?_⟩
  · obtain ⟨q, hq, hqβ⟩ := hin
    rw [List.mem_singleton] at hq
    subst hq
    obtain ⟨γ, hγ, hlt'⟩ := hlt
    rw [meetOfDom_δN] at hγ
    cases hγ
    rw [← hqβ] at hlt'
    exact lt_irrefl _ hlt'
  · obtain ⟨hreb', hsh⟩ := hreb
    obtain ⟨⟨χ₁, k₁, e₁⟩, ⟨χ₂, k₂, e₂⟩⟩ := pairRebCells pR cb' β' 1 2 1 ⟨[]⟩ pR_1 pR_2 hreb' hsh
    exact (pairCallbackGuardFails [] [] β' cb' ρk ρ 1 2 (by decide) List.not_mem_nil
      List.not_mem_nil ⟨_, χ₁, k₁, e₁⟩ ⟨_, χ₂, k₂, e₂⟩ hc).2 en'
      ⟨rfl, List.isChain_singleton _, List.nodup_singleton _⟩

/-- A reborrowed cell at `Imm '1 1`, at a stack lending neither of the pair's places, at a reading
sending `'1` at or below the cell. -/
theorem pImm_vRLM_at {σ : LStack} {αs : List Life} {s : LSub} {m : ℕ} (l : BoCa.Loc)
    (hl : l = 1 ∨ l = 2) (hσ : innerAt σ αs l = none) (hs : (extS s σ αs).find? 1 = some m)
    (hm : (OrderDual.toDual m : Life) ≤ pβ) :
    vRLM (ℍ := ℍ) .binder0 none σ s (.imm (.var 1) .unit) αs pls (.loc l)
      (ResU.single l pImm) := by
  have hchain : ∃ p u, Chain pRec.R pRec.T pRec.v p l .unit u := by
    rcases hl with rfl | rfl
    · exact ⟨none, .unit, Chain.one (RefPos.tensorL (RefPos.ref .unit 1)) pR_1⟩
    · exact ⟨none, .unit, Chain.one (RefPos.tensorR (RefPos.ref .unit 2)) pR_2⟩
  obtain ⟨p, u, hch⟩ := hchain
  rw [vRLM_imm_eq, vRLJ_imm_eq]
  refine ⟨⟨m, hs, l, pure_sep_iff.mpr ⟨⟨rfl, .unit, _, TyEq.refl _ _,
    Or.inr ⟨pRec, List.mem_singleton_self _, p, u, hch, fun y hy => hy.elim⟩⟩,
    LSet.singleton pβ, .unit, PMap.empty, ResU.inStratum_empty _, pls, rfl, ⟨rfl, rfl⟩,
    hm, fun x => ?_⟩⟩, fun l' e α hl' hin => ?_, retainedPay_of_closed (fun y hy => hy)⟩
  · refine ⟨fun hx => ⟨hx, ?_⟩, fun h => h.1⟩
    simp only [pls, List.mem_singleton] at hx
    subst hx
    exact pβ_lt_pα
  · cases hl'
    rw [hσ] at hin
    cases hin

/-- **`¬ WithloadPairGapNilInstE1`**: at `withload`'s thunked type, the own push's answer's `U`
clause instantiates `[pβ]` by the shift of `2` below its cut `1`, which moves the push to `4`,
strictly below the reborrowed cells at `2`; there the reborrow is related at
`Imm '1 1 ⊗ Imm '1 1` and meets the table. A fact about the thunked form's guard: it is not shown
that a row can use that reading (`NEXT.md` §1.2). -/
theorem not_withloadPairGapNilInstE1 : ¬ WithloadPairGapNilInstE1 (ℍ := ℍ) := by
  intro h
  have hpush : OwnPushM δN (pairCbC 1 .unit) PMap.empty ([], []) pEn pβ :=
    pOwnPushN (fun A D h => by cases h)
      (by simp [CTy.binders, VTy.binders, pairTy_immReborrow])
      (fun y hy => absurd hy (by simp [pEn, VFree]))
  refine h pcN pψ pRec 1 2 δN .unit 1 pairNilCfg (pairTy_closed 1) PMap.empty pEn pβ pcb hpush
    pPairReb (Inst.ofEmb (Restrat.Emb.shift (lifeN 1) 2)) pls PMap.empty pcb
    (fun c θ h => ?_) ?_ (ResU.comp_empty_left _) ?_
  · obtain ⟨rfl, -⟩ := Sigma.mk.inj (Option.some.inj h)
    rfl
  · show vRLM .binder0 none [pEn] ⟨[(1, 4), (0, 1)]⟩ (pairTy.immReborrow (.var 1)) [lifeN 4] pls
      pV pcb
    rw [pairTy_immReborrow, vRLM]
    have hi : ∀ l, l = 1 ∨ l = 2 → innerAt [pEn] [lifeN 4] l = none := by
      rintro l (rfl | rfl) <;> simp [innerAt, pEn]
    exact ⟨.loc 1, .loc 2, pure_sep_iff.mpr ⟨rfl, _, _, comp_pcb,
      pImm_vRLM_at 1 (Or.inl rfl) (hi 1 (Or.inl rfl)) rfl (by decide),
      pImm_vRLM_at 2 (Or.inr rfl) (hi 2 (Or.inr rfl)) rfl (by decide)⟩⟩
  · show TabAtS [pEn] [lifeN 4] pcb
    refine ⟨fun a ha => ?_, fun a ha k ψ _ hψ => ?_⟩
    · cases ha
      intro k ψ hψ
      by_cases e1 : k = 1
      · subst e1; rw [pcb_1] at hψ; cases hψ
        exact show (↓(lifeN 4) : Life) < lifeN 2 by decide
      · by_cases e2 : k = 2
        · subst e2; rw [pcb_2] at hψ; cases hψ
          exact show (↓(lifeN 4) : Life) < lifeN 2 by decide
        · rw [pcb_ne e1 e2] at hψ; cases hψ
    · cases ha
      by_cases e1 : k = 1
      · subst e1; rw [pcb_1] at hψ; cases hψ
        exact show (lifeN 4 : Life) < lifeN 2 by decide
      · by_cases e2 : k = 2
        · subst e2; rw [pcb_2] at hψ; cases hψ
          exact show (lifeN 4 : Life) < lifeN 2 by decide
        · rw [pcb_ne e1 e2] at hψ; cases hψ

end ProbeD1

end
