import Core.Chain.PoolSpawnN
import Core.Chain.SI.AntiCancelProg
import Core.Chain.SI.UbindGN
import Core.TreeGoal791

/-!
# #791's hardest case over the chain relation  `[spec §62]`

`HardestCase791` and `HardestCase791C` (`Core/TreeGoal791.lean`) are `OrDiverges` for
`progOf rootMut` and `progOf rootMutC` under the scheduler `HS`. Here they are proved through
`poolSchedAdequacyN` at the chain table `TJN` (`Core/Chain/PoolSpawnN.lean`):

* **task A** (`taskA_ok`): `c ↦ own(loc k) ● k ↦ own(())`; `c` lent `mut` by `withborU dRec`
  (the Mut Frame across cancellable stops, `erwp_M_frameT` with `claimT_canS`, its cancel runs
  ending at `c`'s claim, which the finaliser frame `then … unwind dRec c` consumes,
  `erwp_ubindClaim`); inside, the borrow opened (`erwp_M_antiFrameC`), the boxed field `k` read out
  of it and lent `mut` by `withborF dFwd` to `cbField` (`erwp_M_frameTF`, the opened cell framed
  across cancellable stops by `erwpG_frameT`), which holds the field's borrow across `park`; the
  field's finaliser frame `then … unwind dFwd c` outside the anti-frame (`erwp_ubind`, its
  finaliser holding nothing); at the end both cells are freed by `dRec`;
* **the children** `thL` (`let a = alloc () in ubind (λ_. free a, λ_. free a) (park ())`) and
  `thC` (`park (); cancel ()`), at every indexed table;
* **the roots**: `spawn` of each child, then task A.

Task A's proof is the same in both programs: every entry of `TJN` is cancellable, so a stop of A's
is owed a cancel run whether or not the scheduler takes it. In `rootMutC`, `thC`'s `cancel` finds
A ready on the pool's top and cancels it while A holds the field's borrow.

The location family of the table's cancel obligations follows the lends (`tabOfN Φc PS` at
`Φc = Φ[c ↦ …][k ↦ …]` inside), the spawn payload `PS` staying the scheduler's.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Hardest791
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel.Core.Chain.SI.LendProg
open BoCa.Fig16.LogRel.Core.Chain.SI.AntiLendProg (boxF boxF_down inStratum_own ldA)
open BoCa.Fig16.LogRel.Core.Chain.SI.PoolSpawn
open BoCa.Fig16.Tree.Wp.SchedProgs.Park (nP)
open BoCa.BoLo (Heap Head Kont performE raiseE cancelVal opPayload freeE hndE hndVal clauseAt
  capTag ubindE)

/-! ### The tables -/

section Tables
variable {PS : Nat → List SRec → Val → WProp}

theorem tabOfN_lendOKC (Φc : LocFam) (A : Life) (hPS : ∀ k ls v ρ, PS k ls v ρ → ρ = PMap.empty) :
    (tabOfN (ℍ := ℍ) Φc PS).LendOKC A where
  entry := fun _ _ en h => by
    obtain ⟨ha, hq, -, hw, -⟩ := tabOfN_ent h
    exact ⟨ha, by rw [hq]; decide, hw⟩
  pa := fun _ _ en h k ls v ρ hA => by
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := tabOfN_some h
    · obtain ⟨-, rfl⟩ := hA; exact inStratum_empty A
    · obtain rfl := hPS k ls v ρ hA; exact inStratum_empty A
    · obtain ⟨-, rfl⟩ := hA; exact inStratum_empty A
  pb := fun _ _ en h k ls w ρ hB => by
    rw [(tabOfN_ent h).2.2.2.2] at hB
    obtain ⟨-, rfl⟩ := hB; exact inStratum_empty _

theorem tabOfN_e (Φc : LocFam) : ∀ m i en, tabOfN (ℍ := ℍ) Φc PS m i = some en →
    en.abort = false → en.q ≠ .unr ∧ en.wc = extF := fun _ _ en h _ => by
  obtain ⟨-, hq, -, hw, -⟩ := tabOfN_ent h
  exact ⟨by rw [hq]; decide, hw⟩

theorem tabOfN_fin (Φc : LocFam) : ∀ m i en, tabOfN (ℍ := ℍ) Φc PS m i = some en →
    en.q = .cancel → en.fin = some (cancelOblN (ℍ := ℍ) Φc OpTabN.empty) :=
  fun _ _ _ h _ => (tabOfN_ent h).2.2.1

theorem tabOfN_unr (Φc : LocFam) : ∀ m i en, tabOfN (ℍ := ℍ) Φc PS m i = some en → en.q ≠ .unr :=
  fun _ _ _ h => by rw [(tabOfN_ent h).2.1]; decide

/-- The tables at two location families: twins up to the cancel obligations. -/
theorem tabOfN_twin (Φc Φc' : LocFam) : ∀ m i en, tabOfN (ℍ := ℍ) Φc PS m i = some en →
    ∃ en', tabOfN (ℍ := ℍ) Φc' PS m i = some en' ∧ en'.q = en.q ∧ en'.abort = en.abort ∧
      en'.PA = en.PA ∧ en'.PB = en.PB ∧ en'.wc = en.wc ∧ (en.q ≠ .cancel → en'.fin = en.fin) := by
  intro m i en h
  obtain ⟨rfl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := tabOfN_some h
  · exact ⟨_, tabOfN_park _ _, rfl, rfl, rfl, rfl, rfl, fun hq => absurd rfl hq⟩
  · exact ⟨_, tabOfN_spawn _ _, rfl, rfl, rfl, rfl, rfl, fun hq => absurd rfl hq⟩
  · exact ⟨_, tabOfN_cancel _ _, rfl, rfl, rfl, rfl, rfl, fun hq => absurd rfl hq⟩

/-- `claimT` replaces every cancel obligation, so it does not read the table's own location
family. -/
theorem claimT_tabOfN (Φc Φc' Φ : LocFam) (T₁ : OpTabN) (R : Nat → WProp) :
    @OpTabN.claimT ℍ _ (tabOfN (ℍ := ℍ) Φc PS) Φ T₁ R =
      @OpTabN.claimT ℍ _ (tabOfN (ℍ := ℍ) Φc' PS) Φ T₁ R := by
  funext m i
  unfold OpTabN.claimT tabOfN
  split_ifs <;> simp [enParkN, enSpawnN]

theorem claimT_tabOfN_down {Φ : LocFam} (hΦ : Φ.Down) (Φc : LocFam) (hΦc : Φc.Down)
    (hPS : ∀ k ls v ρ, PS (k + 1) ls v ρ → PS k ls v ρ) {R : Nat → WProp}
    (hR : ∀ k ρ, R (k + 1) ρ → R k ρ) :
    (@OpTabN.claimT ℍ _ (tabOfN (ℍ := ℍ) Φc PS) Φ OpTabN.empty R).Down where
  pa := fun _ _ en' h _ _ _ _ hA => by
    obtain ⟨en, hT, rfl⟩ := claimT_some h
    have hq := (tabOfN_ent hT).2.1
    rw [if_pos hq] at hA ⊢
    exact (tabOfN_down hΦc hPS).pa _ _ en hT _ _ _ _ hA
  fin := fun _ _ en' P h hP => by
    obtain ⟨en, hT, rfl⟩ := claimT_some h
    rw [if_pos (tabOfN_ent hT).2.1] at hP
    cases hP
    exact fun k ls e ρ hk => erwp_le hΦ (cancelTabR_local _ _)
      (cancelTabR_down OpTabN.empty_down hR) falsePost_down (Nat.le_succ _) hk
  wcl := fun _ _ en' h => by
    obtain ⟨en, hT, rfl⟩ := claimT_some h
    rw [if_pos (tabOfN_ent hT).2.1]
    exact (tabOfN_down hΦc hPS).wcl _ _ en hT

theorem claimT_tabOfN_ctxClosed {Φ : LocFam} (hΦ : Φ.Down) (Φc : LocFam) {R : Nat → WProp}
    (K : Kont) (hH : ∀ m, K.HasHnd m = false) (hC : ∀ m, K.Catches m = false) :
    (@OpTabN.claimT ℍ _ (tabOfN (ℍ := ℍ) Φc PS) Φ OpTabN.empty R).CtxClosed K :=
  claimT_ctxClosed hΦ K hH hC (fun _ _ _ h hq => absurd (tabOfN_ent h).2.1 hq) (empty_ctxClosed K)

end Tables

/-- **A cancel run passes a context with no handler and no catcher** (`erwp_cancelTabR_ctx` at
`cancelTabN`). -/
theorem erwp_cancelTabN_ctx {Φ : LocFam} (hΦ : Φ.Down) {T : OpTabN} (K : Kont)
    (hH : ∀ m, K.HasHnd m = false) (hC : ∀ m, K.Catches m = false) (hK : T.CtxClosed K) :
    ∀ n ls x ρ, erwp (ℍ := ℍ) Φ (cancelTabN T) (fun _ _ _ _ => False) n ls x ρ →
      erwp (ℍ := ℍ) Φ (cancelTabN T) (fun _ _ _ _ => False) n ls (K.plug x) ρ := by
  have hL := cancelTabN_local T
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

/-- **`tabOfN`'s cancel obligations pass a context with no handler and no catcher.** -/
theorem tabOfN_ctxClosed {Φc : LocFam} (hΦ : Φc.Down) {PS : Nat → List SRec → Val → WProp}
    (K : Kont) (hH : ∀ m, K.HasHnd m = false) (hC : ∀ m, K.Catches m = false) :
    (tabOfN (ℍ := ℍ) Φc PS).CtxClosed K := by
  intro m i en P h hP k ls K' x ρ hx
  rw [(tabOfN_ent h).2.2.1] at hP
  cases hP
  have hd : (K.comp K').dead = K.comp K'.dead := by
    rw [dead_comp, dead_plain K hH (hC 0)]
  show erwp (ℍ := ℍ) Φc (cancelTabN OpTabN.empty) (fun _ _ _ _ => False) k ls _ ρ
  rw [hd, Kont.plug_comp]
  exact erwp_cancelTabN_ctx hΦ K hH hC (empty_ctxClosed K) k ls _ ρ hx

/-! ### The field's borrow, held across `park` -/

/-- The scheduler's spawn payload. -/
abbrev PS₀ (Φ : LocFam) : Nat → List SRec → Val → WProp := spawnPAN (ℍ := ℍ) Φ (tabAtN (ℍ := ℍ) Φ)

theorem PS₀_empty (Φ : LocFam) : ∀ k ls v ρ, PS₀ (ℍ := ℍ) Φ k ls v ρ → ρ = PMap.empty :=
  fun _ _ _ _ h => h.1

/-- `cbField`'s body at the field `d`: `park; forget d; ()`. -/
def fieldBody (d : Loc) : Expr :=
  .app (.lam (.app (.lam (.val .unit)) (.app forget (.val (Val.loc d))))) parkE
where parkE : Expr := performE (.val (opPayload nP 0 Val.unit))

/-- **The field's borrowed computation**: `park` with the field's `mut` borrow held, then the
borrow forgotten. Resumed, the cell is dumped and the field handed back; cancelled, the cancel's
`raise` owns only the borrow. -/
theorem fieldBody_ok {Φ : LocFam} (hΦ : Φ.Down) (Φs : LocFam) (l : Loc) (A : Life) (u : Val)
    (k : Nat) (ls : List SRec) (BM : WRes)
    (hBM : ResU.CompS PMap.empty (ResU.single l (CellU.mutOf A u PMap.empty (inStratum_empty A)
      (famF A k) rfl)) BM) :
    erwp (ℍ := ℍ) (Φ.set l A (famF A)) (opTableN (tabOfN (ℍ := ℍ) (Φ.set l A (famF A)) (PS₀ Φs)))
      (MFPost l A (famF A) (Qlend l)) k ls (fieldBody l) BM := by
  have hΦ' := LocFam.set_down (l := l) hΦ (famF_down A)
  obtain rfl := eq_of_compS_empty_left hBM
  set K₀ : Kont := .appR (.lam (.app (.lam (.val .unit)) (.app forget (.val (Val.loc l))))) .hole
  have hKH : ∀ m, K₀.HasHnd m = false := fun m => by simp [K₀, Kont.HasHnd]
  have hKC : ∀ m, K₀.Catches m = false := fun m => by simp [K₀, Kont.Catches]
  have hTD := opTableN_down (tabOfN_down (ℍ := ℍ) hΦ' (PS := PS₀ Φs) (spawnPAN_down _ _))
  have hQD : (MFPost l A (famF A) (Qlend l)).Down := fun _ _ _ _ ⟨h₁, h₂⟩ =>
    ⟨h₁, fun w Y hY σ ⟨hσ, hF⟩ Z hZ => h₂ w Y hY σ ⟨hσ, hF⟩ Z hZ⟩
  refine erwp_performG (K := K₀) (hKH nP) (tabOfN_park _ _) rfl (compS_empty_left _) ⟨rfl, rfl⟩
    (fun h => by cases h) (fun ls' _ k' hk' w σB XB hB hXB => ?_) (fun ls' _ _ P hP => ?_)
  · obtain ⟨rfl, rfl⟩ := hB
    obtain rfl := ResU.CompS.functional hXB (ResU.comp_empty_right _)
    refine erwp_dump (opTableN_local _) k' ls' _ _ ?_
    refine erwp_det hΦ' hTD (fun _ _ _ _ ⟨h₁, h₂⟩ => ⟨h₁, hQD _ _ _ _ h₂⟩)
      (fun μ => step1Only_plug (Head.beta μ _ Val.unit) rfl .hole) ?_
    refine erwp_det hΦ' hTD (fun _ _ _ _ ⟨h₁, h₂⟩ => ⟨h₁, hQD _ _ _ _ h₂⟩)
      (fun μ => step1Only_plug (Head.beta μ _ (Val.loc l)) rfl
        (.appR (.lam (.val .unit)) .hole)) ?_
    refine erwp_det hΦ' hTD (fun _ _ _ _ ⟨h₁, h₂⟩ => ⟨h₁, hQD _ _ _ _ h₂⟩)
      (fun μ => step1Only_plug (Head.beta μ _ Val.unit) rfl .hole) ?_
    refine erwp_val (v := Val.unit) ⟨noOwn_single_mut l, inStratum_empty A,
      fun w Y hY σ ⟨hσ, hF⟩ Z hZ => ?_⟩
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

/-! ### The opened borrow: the field read out and lent across `park` -/

open BoCa.Fig16.Tree.Wp.Goal791 (cbField cbRec dRec dFwd withborFV withborFE taskA rootMut
  rootMutC letE allocE)

/-- The callback's table inside the anti-frame: `tabOfN` with the opened cell's claim. -/
abbrev TcbN (Φ Φs : LocFam) (c : Loc) (A : Life) : OpTabN :=
  @OpTabN.claimT ℍ _ (tabOfN (ℍ := ℍ) Φ (PS₀ Φs)) Φ OpTabN.empty (claimR c A (boxF A))

/-- `withborF`'s callback run on the field read out of `c`: `cbField () (!c)`. -/
def fieldF (c : Loc) : Expr := .app (.app (.val cbField) (.val .unit)) (ldA c)

/-- The opened borrow's end: owning nothing. -/
def QF : PostN := fun _ _ _ X => NoOwn X

/-- **The opened borrow**: `!c` reads the field out of the opened cell, the field is lent `mut`
across `park` with the opened cell framed (`erwp_M_frameTF`, `erwpG_frameT`), and at the end the
cell is sealed with the field as its content. At a stop the field's fold and the frame give the
seal's guard. -/
theorem openF_ok {Φ : LocFam} (hΦ : Φ.Down) (Φs : LocFam) (c d : Loc) (u : Val) (A : Life)
    (k : Nat) (ls : List SRec) (X : WRes)
    (hX : ResU.CompS (ResU.single d (CellU.ownOf u)) (ResU.single c (CellU.ownOf (.loc d))) X) :
    erwp (ℍ := ℍ) Φ (opTableG (TcbN (ℍ := ℍ) Φ Φs c A) (CellFold c A (boxF A)))
      (AFPost c A (boxF A) QF) k ls (fieldF c) X := by
  set Φ₂ := Φ.set d A (famF A) with hΦ₂
  set T' := @OpTabN.claimT ℍ _ (tabOfN (ℍ := ℍ) Φ₂ (PS₀ Φs)) Φ OpTabN.empty (claimR d A (famF A))
  set R₂ : WProp := ptoOwn c (.loc d)
  set T'' := @OpTabN.claimT ℍ _ (tabOfN (ℍ := ℍ) Φ₂ (PS₀ Φs)) Φ OpTabN.empty
    (fun k => claimR d A (famF A) k ⋆ R₂)
  have hL := opTableG_local (TcbN (ℍ := ℍ) Φ Φs c A) (CellFold c A (boxF A))
  have hplug : fieldF c = (Kont.appR (.app (.val cbField) (.val .unit)) .hole).plug (ldA c) := rfl
  rw [hplug]
  refine erwp_bindR hΦ hL _ (rwp_load ls c (.loc d) _ ⟨_, _, ResU.CompS.comm hX, rfl,
    fun ρ₁ ρ₂ h₁ hc => ?_⟩)
  subst h₁
  generalize k - 1 = k'
  rcases k' with _ | _ | k₀
  · exact erwp_zero
  · exact erwp_step hL (fun μ => step1Only_plug (Head.beta μ _ Val.unit) rfl
      (.appL .hole (Val.loc d))) erwp_zero
  refine erwp_step hL (fun μ => step1Only_plug (Head.beta μ _ Val.unit) rfl
    (.appL .hole (Val.loc d))) ?_
  refine erwp_step hL (fun μ => step1Only_plug (Head.beta μ _ (Val.loc d)) rfl .hole) ?_
  have e₁ : Kont.hole.plug (Expr.subst 0 (Val.loc d) (Expr.subst (0 + 1) (Val.shift 1 0 Val.unit)
      (letE BoCa.Fig16.Tree.Wp.SchedProgs.SpawnProgs.parkE
        (letE (forget.app (.var 1)) (.val Val.unit))))) = fieldBody d := by
    simp [Expr.subst, Expr.shift, Kont.plug, letE, fieldBody, fieldBody.parkE,
      BoCa.Fig16.Tree.Wp.SchedProgs.SpawnProgs.parkE, forget, unit', performE, opPayload,
      Val.shift, Val.pair, Val.i32, Val.unit, Val.loc, Expr.val, Val.prim, Val.lam, Expr.loc]
  rw [e₁]
  have hTfield : erwp (ℍ := ℍ) Φ (opTableG T' (CellFold d A (famF A))) (Qlend d) k₀ ls
      (fieldBody d) (ResU.single d (CellU.ownOf u)) :=
    erwp_M_frameTF (famF_down A) (tabOfN_lendOKC Φ₂ A (PS₀_empty Φs)) (claimT_twin _ _ _ _)
      (claimT_canS (famF_down A) (empty_lendOK A) (tabOfN_fin Φ₂) (tabOfN_unr Φ₂))
      k₀ k₀ le_rfl ls (fieldBody d) u PMap.empty _ PMap.empty _ (inStratum_empty A)
      (inStratum_empty _) (famF A k₀) (fun _ _ h => h) rfl (ResU.comp_empty_right _)
      (ResU.comp_empty_right _) (fieldBody_ok hΦ Φs d A u k₀ ls)
  have hT'e : ∀ m i en, T' m i = some en → en.abort = false → en.q ≠ .unr ∧ en.wc = extF := by
    intro m i en h ha
    obtain ⟨en₀, h₀, rfl⟩ := claimT_some h
    rw [if_pos (tabOfN_ent h₀).2.1] at ha ⊢
    exact tabOfN_e Φ₂ m i en₀ h₀ ha
  have hT'T'' : T'.Twin T'' := by
    intro m i en h
    obtain ⟨en₀, h₀, rfl⟩ := claimT_some h
    have hq := (tabOfN_ent h₀).2.1
    refine ⟨OpEntN.mk en₀.q en₀.abort en₀.PA en₀.PB
      (some (@cancelOblRN ℍ _ Φ OpTabN.empty (fun k => claimR d A (famF A) k ⋆ R₂))) en₀.wc,
      by simp [T'', OpTabN.claimT, h₀, hq], ?_⟩
    simp [hq]
  have hfr := erwpG_frameT hT'e hT'T'' R₂ (fun m i en en' h h' hql k ls' K ρk σ₂ ρk₂ hk hR hcan => by
      obtain ⟨en₀, h₀, rfl⟩ := claimT_some h
      obtain ⟨en₁, h₁, rfl⟩ := claimT_some h'
      rw [h₀] at h₁; cases h₁
      have hqc : en₀.q = .cancel := (tabOfN_ent h₀).2.1
      simp only [hqc, if_true] at hcan ⊢
      intro P hP
      cases hP
      exact erwp_frame_cancelRun R₂ k ls' _ ρk σ₂ ρk₂ hk hR (hcan _ rfl))
    k₀ ls (fieldBody d) _ _ _ hc rfl hTfield
  have hR : ∀ k ρ, (claimR d A (famF A) k ⋆ R₂) ρ → claimR c A (boxF A) k ρ := by
    rintro k ρ ⟨ρ₁, ρ₂', hc₁, ⟨w, σ, hσ, hF, hcw⟩, rfl⟩
    have hσ0 : σ = PMap.empty := hF
    subst hσ0
    obtain rfl := ResU.CompS.functional hcw (ResU.comp_empty_right _)
    exact ⟨Val.loc d, ResU.single d (CellU.ownOf w), inStratum_own A d w, ⟨d, w, rfl, rfl⟩,
      ResU.CompS.comm hc₁⟩
  refine erwp_mono (fun k ls' v ρ h => ?_)
    (opTableG_twinC (AntiCancelProg.claimT_twinC (tabOfN_twin Φ₂ Φ) hR) fun k ls' ρ h => ?_) _ _ _ _ hfr
  · obtain ⟨ρ₁, ρ₂, hc₁, ⟨rfl, w, rfl⟩, rfl⟩ := h
    refine ⟨Val.loc d, ResU.single d (CellU.ownOf w), inStratum_own A d w, ⟨d, w, rfl, rfl⟩,
      PMap.empty, _, ResU.CompS.comm hc₁, ResU.comp_empty_right _, fun X hX => ?_⟩
    obtain rfl := eq_of_compS_empty_left hX
    exact noOwn_single_mut c
  · obtain ⟨ρ₁, ρ₂, hc₁, ⟨w, χ, hχ, hw, R, rest, hr1, hr2⟩, rfl⟩ := h
    have hχ0 : χ = PMap.empty := hw
    subst hχ0
    obtain rfl := eq_of_compS_empty_left hr2
    exact ⟨Val.loc d, ResU.single d (CellU.ownOf w), inStratum_own A d w, ⟨d, w, rfl, rfl⟩, _,
      ρ₁, ResU.CompS.comm hc₁, hr1⟩

/-! ### The record's borrow: the borrow opened, the field reborrowed, the borrow forgotten -/

/-- `withborU`'s callback run on the record: `cbRec () c`. -/
def cbBody (c : Loc) : Expr := .app (.app (.val cbRec) (.val .unit)) (.val (Val.loc c))

/-- `withborF`'s `then` and `unwind`: `λb. (c, b)` and `λ_. dFwd c`. -/
def NF (c : Loc) : Val := Val.lam (.pair (.val (Val.loc c)) (.var 0))
def DF (c : Loc) : Val := Val.lam (.app (.val dFwd) (.val (Val.loc c)))

/-- What the field's reborrow answers: the pair, owning nothing. -/
def QN (c : Loc) : PostN := fun _ _ v ρ => (∃ b, v = Val.pair (Val.loc c) b) ∧ NoOwn ρ

/-- `withborF`'s finaliser holds nothing. -/
theorem DF_finOK (Φ : LocFam) (hΦ : Φ.Down) (c : Loc) :
    BoCa.Fig16.LogRel.Core.Chain.SI.FinOK (ℍ := ℍ) Φ (DF c) PMap.empty := by
  intro k ls
  rw [rwp_iff_rwpG]
  have hQ : PostG.Down (valPostN (fun _ _ v ρ' => v = Val.unit ∧ ρ' = PMap.empty)) :=
    fun _ _ _ _ ⟨v, hv, hq⟩ => ⟨v, hv, hq⟩
  refine rwpG_det hΦ hQ (fun μ => step1Only_plug (Head.beta μ _ Val.unit) rfl .hole) ?_
  refine rwpG_det hΦ hQ (fun μ => step1Only_plug (Head.beta μ _ (Val.loc c)) rfl .hole) ?_
  exact rwpG_here (fun μ => final_val μ Val.unit) ⟨Val.unit, rfl, rfl, rfl⟩

/-- **The record's borrowed computation**: `withborF dFwd c cbField`, the borrow opened around
the field's read and reborrow (`erwp_M_antiFrameC`, `openF_ok`), the field's finaliser frame
outside it (`erwp_ubind`), then the borrow forgotten and the sealed cell dumped. -/
theorem methodF_ok {Φ : LocFam} (hΦ : Φ.Down) (Φs : LocFam) (c d : Loc) (u : Val) (A : Life)
    (k : Nat) (ls : List SRec) (BM : WRes)
    (hBM : ResU.CompS PMap.empty (ResU.single c (CellU.mutOf A (.loc d)
      (ResU.single d (CellU.ownOf u)) (inStratum_own A d u) (boxF A k) ⟨d, u, rfl, rfl⟩)) BM) :
    erwp (ℍ := ℍ) (Φ.set c A (boxF A)) (opTableN (tabOfN (ℍ := ℍ) (Φ.set c A (boxF A)) (PS₀ Φs)))
      (MFPost c A (boxF A) (AntiLendProg.QA c)) k ls (cbBody c) BM := by
  set Φ' := Φ.set c A (boxF A) with hΦ'e
  have hΦ' : Φ'.Down := LocFam.set_down (l := c) hΦ (boxF_down A)
  have hFl : Φ' c = some ⟨A, boxF A⟩ := by simp [Φ', LocFam.set]
  obtain rfl := eq_of_compS_empty_left hBM
  set T := tabOfN (ℍ := ℍ) Φ' (PS₀ Φs)
  have hTd : T.Down := tabOfN_down hΦ' (spawnPAN_down _ _)
  have hTD := opTableN_down hTd
  have hL := opTableN_local T
  set QM : PostN := fun k ls' v X => NoOwn X ∧
    MFPost c A (boxF A) (AntiLendProg.QA c) k ls' v PMap.empty
  have hQM : QM.Down := fun _ _ _ _ ⟨h₁, h₂, h₃⟩ => ⟨h₁, h₂, fun w Y hY σ hσ Z hZ =>
    h₃ w Y hY σ hσ Z hZ⟩
  have hQN : (QN c).Down := fun _ _ _ _ h => h
  refine erwp_dump hL k ls _ _ ?_
  refine erwp_det hΦ' hTD hQM (fun μ => step1Only_plug (Head.beta μ _ Val.unit) rfl
    (.appL .hole (Val.loc c))) ?_
  refine erwp_det hΦ' hTD hQM (fun μ => step1Only_plug (Head.beta μ _ (Val.loc c)) rfl .hole) ?_
  set LP : Expr := (Expr.var 0).letpair (forget.app (Expr.var 1))
  have e₁ : Kont.hole.plug (Expr.subst 0 (Val.loc c) (Expr.subst (0 + 1) (Val.shift 1 0 Val.unit)
      (letE (((Expr.val (withborFV (Expr.val dFwd))).app (Expr.var 0)).app (Expr.val cbField))
        LP))) = (Kont.appR (.lam LP) .hole).plug
          (((Expr.val (withborFV (Expr.val dFwd))).app (.val (Val.loc c))).app (.val cbField)) := by
    simp [LP, Expr.subst, Expr.shift, Kont.plug, letE, withborFV, withborFE, thenE, cbField, dFwd,
      forget, unit', BoCa.Fig16.Tree.Wp.SchedProgs.SpawnProgs.parkE, performE, opPayload,
      Val.shift, Val.pair, Val.i32, Val.unit, Val.loc, Expr.val, Val.prim, Val.lam, Expr.loc]
  rw [e₁]
  have hKH : ∀ m, (Kont.appR (.lam LP) .hole).HasHnd m = false := fun m => by simp [Kont.HasHnd]
  have hKC : ∀ m, (Kont.appR (.lam LP) .hole).Catches m = false := fun m => by simp [Kont.Catches]
  refine erwp_bind hΦ' _ hKH hKC (tabOfN_ctxClosed hΦ' _ hKH hKC) (Q' := QN c) ?_ k ls _ _ ?_
  · rintro k' ls' v ρ ⟨⟨b, rfl⟩, hno⟩
    simp only [Kont.plug]
    refine erwp_det hΦ' hTD hQM (fun μ => step1Only_plug (Head.beta μ _ _) rfl .hole) ?_
    simp [LP, Kont.plug, Expr.subst, forget, unit']
    refine erwp_det hΦ' hTD hQM (fun μ => step1Only_plug (Head.letpair μ (Val.loc c) b _) rfl
      .hole) ?_
    simp [Kont.plug, Expr.subst, forget, unit']
    refine erwp_det hΦ' hTD hQM (fun μ => step1Only_plug (Head.beta μ _ (Val.loc c)) rfl .hole) ?_
    simp [Kont.plug, Expr.subst, unit']
    refine erwp_val (v := Val.unit) ⟨hno, inStratum_empty A,
      fun w Y hY σ ⟨hσ, d', u', hw, hσ'⟩ Z hZ => ⟨rfl, d', u', ?_⟩⟩
    obtain rfl := eq_of_compS_empty_left hY
    subst hw
    have : σ = ResU.single d' (CellU.ownOf u') := hσ'
    subst this
    exact hZ
  · refine erwp_det hΦ' hTD hQN (fun μ => step1Only_plug (Head.beta μ _ (Val.loc c)) rfl
      (.appL .hole cbField)) ?_
    refine erwp_det hΦ' hTD hQN (fun μ => step1Only_plug (Head.beta μ _ cbField) rfl .hole) ?_
    have e₂ : Kont.hole.plug (Expr.subst 0 cbField (Expr.subst (0 + 1) (Val.shift 1 0 (Val.loc c))
        (thenE ((Expr.var 2).pair (Expr.var 0)) ((Expr.val dFwd).app (Expr.var 2))
          (((Expr.var 0).app (Expr.val Val.unit)).app
            ((Expr.val (Val.prim Prim.load)).app (Expr.var 1)))))) =
        ubindE (.pair (NF c) (DF c)) (fieldF c) := by
      simp [Expr.subst, Expr.shift, Kont.plug, thenE, ubindE, NF, DF, fieldF, ldA, cbField, dFwd,
        forget, unit', letE, BoCa.Fig16.Tree.Wp.SchedProgs.SpawnProgs.parkE, performE, opPayload,
        Val.shift, Val.pair, Val.i32, Val.unit, Val.loc, Expr.val, Val.prim, Val.lam, Expr.loc]
    rw [e₂]
    have hM : erwp (ℍ := ℍ) Φ' (opTableN T) QF k ls (fieldF c)
        (ResU.single c (CellU.mutOf A (.loc d) (ResU.single d (CellU.ownOf u))
          (inStratum_own A d u) (boxF A k) ⟨d, u, rfl, rfl⟩)) :=
      erwp_M_antiFrameC hΦ' hFl (tabOfN_e Φ') (tabOfN_fin Φ') k ls (fieldF c) (.loc d) _
        (inStratum_own A d u) k ⟨d, u, rfl, rfl⟩ PMap.empty _ (ResU.comp_empty_right _)
        fun W X hW hX => by
          obtain rfl := eq_of_compS_empty_left hX
          exact openF_ok hΦ' Φs c d u A k ls _ hW
    refine erwp_ubind hΦ' hTd hTd hQN (NF c) (DF c) (DF_finOK Φ' hΦ' c) ?_ ?_ (tabOfN_unr Φ')
      (fun _ _ en h ha => absurd ha (by rw [(tabOfN_ent h).1]; simp)) k ls (fieldF c) _ _
      (ResU.comp_empty_right _) hM
    · intro k' ls' v ρ X hX hv
      obtain rfl := ResU.CompS.functional hX (ResU.comp_empty_right _)
      refine erwp_det hΦ' hTD hQN (fun μ => step1Only_plug (Head.beta μ _ v) rfl .hole) ?_
      simp [Kont.plug, Expr.subst, NF]
      exact erwp_val (v := Val.pair (Val.loc c) v) ⟨⟨v, rfl⟩, hv⟩
    · intro m i en h _
      refine ⟨en, h, rfl, (tabOfN_ent h).1, rfl, rfl, rfl, fun k' ls' K ρk X hX hc P hP => ?_⟩
      obtain rfl := ResU.CompS.functional hX (ResU.comp_empty_right _)
      rw [(tabOfN_ent h).2.2.1] at hP
      cases hP
      rw [dead_comp, ubK_dead, Kont.plug_comp]
      exact cancelOblN_ubind hΦ' OpTabN.empty_down
        (fun _ _ _ h => by simp [OpTabN.empty] at h) (NF c) (DF c) (DF_finOK Φ' hΦ' c) k' ls' _
        _ _ (ResU.comp_empty_right _) (hc _ (tabOfN_ent h).2.2.1)

/-! ### Task A -/

/-- A det step in front of an `rwp`. -/
theorem rwp_det' {Φ : LocFam} (hΦ : Φ.Down) {n : Nat} {ls : List SRec} {e e' : Expr}
    {ρ : WRes} (hdet : ∀ μ, Step1Only (ℍ := ℍ) μ e μ e')
    (h : rwp (ℍ := ℍ) Φ (fun _ _ _ ρ' => ρ' = PMap.empty) n ls e' ρ) :
    rwp (ℍ := ℍ) Φ (fun _ _ _ ρ' => ρ' = PMap.empty) n ls e ρ := by
  rw [rwp_iff_rwpG] at h ⊢
  exact rwpG_det hΦ (fun _ _ _ _ ⟨v, hv, hq⟩ => ⟨v, hv, hq⟩) hdet h

/-- A det step in front of an `rwp` at a postcondition that does not read the index. -/
theorem rwp_det'' {Φ : LocFam} (hΦ : Φ.Down) {Q : List SRec → Val → WProp} {n : Nat}
    {ls : List SRec} {e e' : Expr} {ρ : WRes} (hdet : ∀ μ, Step1Only (ℍ := ℍ) μ e μ e')
    (h : rwp (ℍ := ℍ) Φ (fun _ ls v => Q ls v) n ls e' ρ) :
    rwp (ℍ := ℍ) Φ (fun _ ls v => Q ls v) n ls e ρ := by
  rw [rwp_iff_rwpG] at h ⊢
  exact rwpG_det hΦ (fun _ _ _ _ ⟨v, hv, hq⟩ => ⟨v, hv, hq⟩) hdet h

/-- **The record's finaliser frees the record and its field.** -/
theorem dRec_ok {Φ : LocFam} (hΦ : Φ.Down) (c d : Loc) (u : Val) (k : Nat) (ls : List SRec)
    (ρ : WRes)
    (hρ : ResU.CompS (ResU.single c (CellU.ownOf (.loc d))) (ResU.single d (CellU.ownOf u)) ρ) :
    rwp (ℍ := ℍ) Φ (fun _ _ _ ρ' => ρ' = PMap.empty) k ls (.app (.val dRec) (.val (Val.loc c)))
      ρ := by
  refine rwp_det' hΦ (fun μ => step1Only_plug (Head.beta μ _ (Val.loc c)) rfl .hole) ?_
  have e₁ : Kont.hole.plug (Expr.subst 0 (Val.loc c) (letE (.app (.val (.prim .load)) (.var 0))
      (letE (freeE (.var 1)) (freeE (.var 1))))) =
      (Kont.appR (.lam (.app (.lam (freeE (.var 1))) (freeE (.val (Val.loc c))))) .hole).plug
        (ldA c) := by
    simp [Expr.subst, Expr.shift, Kont.plug, letE, freeE, ldA, Val.loc, Expr.val, Val.prim,
      Expr.loc]
  rw [e₁]
  refine rwp_bind hΦ _ (rwp_load ls c (.loc d) _ ⟨_, _, hρ, rfl, fun ρ₁ ρ₂ h₁ hc => ?_⟩)
  subst h₁
  obtain rfl := ResU.CompS.functional (ResU.CompS.comm hc) hρ
  refine rwp_det' hΦ (fun μ => step1Only_plug (Head.beta μ _ (Val.loc d)) rfl .hole) ?_
  have e₂ : Kont.hole.plug (Expr.subst 0 (Val.loc d)
      (.app (.lam (freeE (.var 1))) (freeE (.val (Val.loc c))))) =
      (Kont.appR (.lam (freeE (.val (Val.loc d)))) .hole).plug (freeE (.val (Val.loc c))) := by
    simp [Expr.subst, Kont.plug, freeE, Val.loc, Expr.val, Val.prim, Expr.shift]
  rw [e₂]
  refine rwp_bind hΦ _ (rwp_free ls c (.loc d) _ ⟨_, _, hρ, rfl, ?_⟩)
  refine rwp_det' hΦ (fun μ => step1Only_plug (Head.beta μ _ (Val.loc d)) rfl .hole) ?_
  have e₃ : Kont.hole.plug (Expr.subst 0 (Val.loc d) (freeE (.val (Val.loc d)))) =
      freeE (.val (Val.loc d)) := by
    simp [Expr.subst, Kont.plug, freeE, Val.loc, Expr.val, Val.prim]
  rw [e₃]
  exact rwp_free ls d u _ ⟨_, PMap.empty, ResU.comp_empty_right _, rfl, rfl⟩

/-- What the record's lend answers: the pair, the record whole again. -/
def QR (c : Loc) : PostN := fun _ _ v ρ => ∃ (b : Val) (d : Loc) (u : Val),
  v = Val.pair (Val.loc c) b ∧
    ResU.CompS (ResU.single c (CellU.ownOf (.loc d))) (ResU.single d (CellU.ownOf u)) ρ

/-- `withborU`'s finaliser: `λ_. dRec c`. -/
def DR (c : Loc) : Val := Val.lam (.app (.val dRec) (.val (Val.loc c)))

/-- **Task A at the scheduler's table**: the record and its field allocated, the record lent `mut`
to `cbRec` across cancellable stops (`erwp_M_frameT`, `claimT_canS`, `methodF_ok`), its cancel
runs ending at the record's claim, consumed by `dRec` in the finaliser frame (`erwp_ubindClaim`);
then `dRec` frees both cells. -/
theorem dRec_closed : closedAt 0 dRec.1 = true := rfl
theorem cbRec_closed : closedAt 0 cbRec.1 = true := rfl
theorem withborUd_closed : closedAt 0 (withborUV (.val dRec)).1 = true := rfl
theorem alloc_closed : closedAt 0 (Val.prim .alloc).1 = true := rfl

/-- The record's lend and its end, under the binder of the record. -/
def B2 : Expr := .app (.lam (.letpair (.var 0) (.app (.val dRec) (.var 1))))
  (.app (.app (.val (withborUV (.val dRec))) (.var 0)) (.val cbRec))

theorem taskA_ok {Φ : LocFam} (hΦ : Φ.Down) (A : Life) (n : Nat) (ls : List SRec) :
    erwp (ℍ := ℍ) Φ (opTableN (TJN (ℍ := ℍ) Φ)) QVN n ls taskA PMap.empty := by
  have hTd := TJN_down (ℍ := ℍ) hΦ
  have hTD := opTableN_down hTd
  have hL := opTableN_local (TJN (ℍ := ℍ) Φ)
  have hQ : QVN.Down := QVN_down
  simp only [taskA, letE, allocE]
  refine erwp_alloc hΦ hL (.appR _ .hole) Val.unit (fun kk σ₁ σ₂ hk hc => ?_)
  obtain rfl := eq_of_compS_empty_left hc
  refine erwp_det hΦ hTD hQ (fun μ => step1Only_plug (Head.beta μ _ (Val.loc kk)) rfl .hole) ?_
  have e₁ : ∀ s : Val, Kont.hole.plug (Expr.subst 0 s (.app (.lam B2)
      (.app (.val (.prim .alloc)) (.var 0)))) =
      (Kont.appR (.lam B2) .hole).plug (.app (.val (.prim .alloc)) (.val s)) := by
    intro s
    simp [B2, Kont.plug, Expr.subst, subst_closedAt _ _ dRec_closed (Nat.zero_le _),
      subst_closedAt _ _ cbRec_closed (Nat.zero_le _),
      subst_closedAt _ _ withborUd_closed (Nat.zero_le _),
      subst_closedAt _ _ alloc_closed (Nat.zero_le _)]
  show erwp (ℍ := ℍ) Φ _ _ _ _ (Kont.hole.plug (Expr.subst 0 (Val.loc kk) (.app (.lam B2)
    (.app (.val (.prim .alloc)) (.var 0))))) _
  rw [e₁]
  refine erwp_alloc hΦ hL (.appR (.lam B2) .hole) (Val.loc kk) (fun c τ₁ τ₂ hcl hc₂ => ?_)
  refine erwp_det hΦ hTD hQ (fun μ => step1Only_plug (Head.beta μ _ (Val.loc c)) rfl .hole) ?_
  set LPD : Expr := .letpair (.var 0) (.app (.val dRec) (.var 1))
  set W : Expr := .app (.app (.val (withborUV (.val dRec))) (.val (Val.loc c))) (.val cbRec)
  have e₂ : Kont.hole.plug (Expr.subst 0 (Val.loc c) B2) = (Kont.appR (.lam LPD) .hole).plug W := by
    simp [B2, LPD, W, Kont.plug, Expr.subst, subst_closedAt _ _ dRec_closed (Nat.zero_le _),
      subst_closedAt _ _ cbRec_closed (Nat.zero_le _),
      subst_closedAt _ _ withborUd_closed (Nat.zero_le _)]
  rw [e₂]
  have hKH : ∀ m, (Kont.appR (.lam LPD) .hole).HasHnd m = false := fun m => by simp [Kont.HasHnd]
  have hKC : ∀ m, (Kont.appR (.lam LPD) .hole).Catches m = false := fun m => by
    simp [Kont.Catches]
  have hQR : (QR c).Down := fun _ _ _ _ h => h
  subst hk hcl
  refine erwp_bind hΦ _ hKH hKC (tabOfN_ctxClosed hΦ _ hKH hKC) (Q' := QR c) ?_ _ ls W τ₂ ?_
  · rintro k' ls' v ρ ⟨b, d, u, rfl, hρ'⟩
    simp only [Kont.plug]
    refine erwp_det hΦ hTD hQ (fun μ => step1Only_plug (Head.beta μ _ _) rfl .hole) ?_
    simp [LPD, Kont.plug, Expr.subst, subst_closedAt _ _ dRec_closed (Nat.zero_le _)]
    refine erwp_det hΦ hTD hQ (fun μ => step1Only_plug (Head.letpair μ (Val.loc c) b _) rfl
      .hole) ?_
    simp [Kont.plug, Expr.subst, subst_closedAt _ _ dRec_closed (Nat.zero_le _)]
    exact erwp_of_rwp (dRec_ok hΦ c d u k' ls' ρ hρ')
  · refine erwp_det hΦ hTD hQR (fun μ => step1Only_plug (Head.beta μ _ (Val.loc c)) rfl
      (.appL .hole cbRec)) ?_
    refine erwp_det hΦ hTD hQR (fun μ => step1Only_plug (Head.beta μ _ cbRec) rfl .hole) ?_
    have e₃ : Kont.hole.plug (Expr.subst 0 cbRec (Expr.subst (0 + 1) (Val.shift 1 0 (Val.loc c))
        (thenE ((Expr.var 2).pair (Expr.var 0)) ((Expr.val dRec).app (Expr.var 2))
          (((Expr.var 0).app (Expr.val Val.unit)).app (Expr.var 1))))) =
        ubindE (.pair (NF c) (DR c)) (cbBody c) := by
      simp [Kont.plug, Expr.subst, Expr.shift, thenE, ubindE, NF, DR, cbBody, Val.shift,
        Val.pair, Val.loc, Val.lam, Expr.val, Val.prim, Expr.loc,
        subst_closedAt _ _ dRec_closed (Nat.zero_le _), subst_closedAt _ _ cbRec_closed
          (Nat.zero_le _)]
    rw [e₃]
    set Φ' := Φ.set c A (boxF A)
    have hM := erwp_M_frameT (Φ := Φ) (boxF_down A)
      (tabOfN_lendOKC (ℍ := ℍ) (PS := PS₀ Φ) Φ' A (PS₀_empty Φ))
      (claimT_twin (tabOfN (ℍ := ℍ) Φ' (PS₀ Φ)) Φ OpTabN.empty (claimR c A (boxF A)))
      (claimT_canS (boxF_down A) (empty_lendOK A) (tabOfN_fin Φ') (tabOfN_unr Φ'))
      (n - 1 - 1) (n - 1 - 1) le_rfl ls (cbBody c) (.loc kk)
      (ResU.single kk (CellU.ownOf Val.unit)) τ₂ PMap.empty τ₂ (inStratum_own A kk Val.unit)
      (inStratum_empty _) (boxF A (n - 1 - 1)) (fun _ _ h => h) ⟨kk, Val.unit, rfl, rfl⟩
      (ResU.CompS.comm hc₂) (ResU.comp_empty_right _)
      (methodF_ok hΦ Φ c kk Val.unit A (n - 1 - 1) ls)
    rw [claimT_tabOfN Φ' Φ Φ] at hM
    refine erwp_ubindClaim hΦ hTd OpTabN.empty_down (fun _ _ _ h => by simp [OpTabN.empty] at h)
      (fun m i en h => ⟨(tabOfN_ent h).1, tabOfN_unr Φ m i en h⟩) (tabOfN_fin Φ) (NF c) (DR c)
      ?_ hQR (Qin := AntiLendProg.QA c) ?_ _ ls _ _ hM
    · rintro k' ls' ρ ⟨w, σ, hσ, ⟨d, u, rfl, hσ'⟩, hcw⟩
      have : σ = ResU.single d (CellU.ownOf u) := hσ'
      subst this
      refine rwp_det' hΦ (fun μ => step1Only_plug (Head.beta μ _ Val.unit) rfl .hole) ?_
      have e₄ : Kont.hole.plug (Expr.subst 0 Val.unit (.app (.val dRec) (.val (Val.loc c)))) =
          .app (.val dRec) (.val (Val.loc c)) := by
        simp [Kont.plug, Expr.subst, Val.loc, Expr.val, Expr.loc,
          subst_closedAt _ _ dRec_closed (Nat.zero_le _)]
      rw [e₄]
      exact dRec_ok hΦ c d u k' ls' _ hcw
    · rintro k' ls' v ρ ⟨rfl, d, u, hρ'⟩
      refine erwp_det hΦ hTD hQR (fun μ => step1Only_plug (Head.beta μ _ Val.unit) rfl .hole) ?_
      simp [Kont.plug, Expr.subst, NF]
      exact erwp_val (v := Val.pair (Val.loc c) Val.unit) ⟨Val.unit, d, u, rfl, hρ'⟩

/-! ### The children -/

open BoCa.Fig16.Tree.Wp.SchedProgs.SpawnProgs (thL thC L Lbody Lbody_beta L_closed Nf Cbody
  cancelE spawnE)

section Children
variable {Φ : LocFam} {PS : Nat → List SRec → Val → WProp}

/-- A cancel run from a context with no finaliser, owning nothing: the cancel's `raise`. -/
theorem cancel_plain (K : Kont) (hKH : ∀ m, K.HasHnd m = false) (hKC : ∀ m, K.Catches m = false)
    (k : Nat) (ls : List SRec) :
    cancelOblN (ℍ := ℍ) Φ OpTabN.empty k ls (K.dead.plug (raiseE (.val (cancelVal none))))
      PMap.empty := by
  show erwp (ℍ := ℍ) Φ (cancelTabN OpTabN.empty) (fun _ _ _ _ => False) k ls _ _
  rw [dead_plain _ hKH (hKC 0), erwp_eq]
  exact rwpG_here (final_opPlug (r := true) (payloadName_cancelVal none) (hKC 0))
    (Or.inr (Or.inl ⟨_, none, pure_sep_mk ⟨rfl, hKC 0⟩
      ⟨PMap.empty, _, compS_empty_left _, emp_empty, noOwn_empty⟩⟩))

/-- **A `park` or `cancel` holding nothing, in a context with no handler and no catcher**:
resumed at `()`, the context's run; cancelled, the cancel's `raise`. -/
theorem erwp_parkAt (hΦ : Φ.Down) (hPS : ∀ k ls v ρ, PS (k + 1) ls v ρ → PS k ls v ρ)
    {i : UInt32} (hi : tabOfN (ℍ := ℍ) Φ PS nP i = some (enParkN (ℍ := ℍ) Φ)) (K : Kont)
    (hKH : ∀ m, K.HasHnd m = false) (hKC : ∀ m, K.Catches m = false) {n : Nat}
    {ls : List SRec}
    (hk : ∀ k', k' < n → ∀ ls', erwp (ℍ := ℍ) Φ (opTableN (tabOfN (ℍ := ℍ) Φ PS)) QVN k' ls'
      (K.plug (.val Val.unit)) PMap.empty) :
    erwp (ℍ := ℍ) Φ (opTableN (tabOfN (ℍ := ℍ) Φ PS)) QVN n ls
      (K.plug (performE (.val (opPayload nP i Val.unit)))) PMap.empty :=
  erwp_performG K (hKH nP) hi rfl (compS_empty_left _) ⟨rfl, rfl⟩ (fun _ => rfl)
    (fun ls' _ k' hk' w σB XB ⟨hw, hσ⟩ hXB => by
      subst hw hσ
      obtain rfl := eq_of_compS_empty_left hXB
      exact hk k' hk' ls')
    (fun ls' _ _ P hP => by cases hP; exact cancel_plain K hKH hKC _ _)

theorem L_body (a : Loc) : Lbody.subst 0 (Val.loc a) = ubindE (.pair (Nf a) (Nf a))
    (performE (.val (opPayload nP 0 Val.unit))) := by
  rw [Lbody_beta]; rfl

/-- `λ_. free a` releases the cell. -/
theorem Nf_finOK (hΦ : Φ.Down) (a : Loc) :
    BoCa.Fig16.LogRel.Core.Chain.SI.FinOK (ℍ := ℍ) Φ (Nf a)
      (ResU.single a (CellU.ownOf Val.unit)) := by
  intro k ls
  refine rwp_det'' hΦ (fun μ => step1Only_plug (Head.beta μ _ Val.unit) rfl .hole) ?_
  have e : Kont.hole.plug (Expr.subst 0 Val.unit (freeE (.val (Val.loc a)))) =
      freeE (.val (Val.loc a)) := by simp [Expr.subst, Kont.plug, freeE, Val.loc, Expr.val,
        Val.prim]
  rw [e]
  exact rwp_free ls a Val.unit _ ⟨_, PMap.empty, ResU.comp_empty_right _, rfl, rfl, rfl⟩

/-- **The loan child** `L`: the cell allocated, held in the finaliser frame across `park`, freed
on both paths (`erwp_ubind`). -/
theorem thL_ok (hΦ : Φ.Down) (hPS : ∀ k ls v ρ, PS (k + 1) ls v ρ → PS k ls v ρ) (n : Nat)
    (ls : List SRec) :
    erwp (ℍ := ℍ) Φ (opTableN (tabOfN (ℍ := ℍ) Φ PS)) QVN n ls (.app thL.1 (.val Val.unit))
      PMap.empty := by
  have hTd := tabOfN_down (ℍ := ℍ) hΦ hPS
  have hTD := opTableN_down hTd
  have hL := opTableN_local (tabOfN (ℍ := ℍ) Φ PS)
  refine erwp_det hΦ hTD QVN_down (fun μ => step1Only_plug (Head.beta μ _ Val.unit) rfl .hole) ?_
  rw [Kont.plug_hole, L_closed]
  refine erwp_alloc hΦ hL (.appR (.lam Lbody) .hole) Val.unit (fun a σ₁ σ₂ ha hc => ?_)
  obtain rfl := eq_of_compS_empty_left hc
  subst ha
  refine erwp_det hΦ hTD QVN_down (fun μ => step1Only_plug (Head.beta μ _ (Val.loc a)) rfl
    .hole) ?_
  rw [Kont.plug_hole, L_body]
  refine erwp_ubind hΦ hTd hTd QVN_down (Nf a) (Nf a) (Nf_finOK hΦ a) (Qin := QVN) ?_ ?_
    (tabOfN_unr Φ) (fun _ _ en h ha => absurd ha (by rw [(tabOfN_ent h).1]; simp)) _ ls _ _ _
    (compS_empty_left _) ?_
  · intro k' ls' v ρ X hX hv
    subst hv
    obtain rfl := eq_of_compS_empty_left hX
    refine erwp_of_rwp (rwp_det'' hΦ (fun μ => step1Only_plug (Head.beta μ _ v) rfl .hole) ?_)
    have e : Kont.hole.plug (Expr.subst 0 v (freeE (.val (Val.loc a)))) =
        freeE (.val (Val.loc a)) := by simp [Expr.subst, Kont.plug, freeE, Val.loc, Expr.val,
          Val.prim]
    rw [e]
    exact rwp_free ls' a Val.unit _ ⟨_, PMap.empty, ResU.comp_empty_right _, rfl, rfl⟩
  · intro m i en h _
    refine ⟨en, h, rfl, (tabOfN_ent h).1, rfl, rfl, rfl, fun k' ls' K ρk X hX hcn P hP => ?_⟩
    rw [(tabOfN_ent h).2.2.1] at hP
    cases hP
    rw [dead_comp, ubK_dead, Kont.plug_comp]
    exact cancelOblN_ubind hΦ OpTabN.empty_down (fun _ _ _ h => by simp [OpTabN.empty] at h)
      (Nf a) (Nf a) (Nf_finOK hΦ a) k' ls' _ ρk X hX (hcn _ (tabOfN_ent h).2.2.1)
  · exact erwp_parkAt hΦ hPS (tabOfN_park _ _) .hole (fun _ => rfl) (fun _ => rfl)
      fun k' _ ls' => erwp_val (v := Val.unit) rfl

theorem Cbody_closed (v : Val) : Cbody.subst 0 v = Cbody := by
  simp [Cbody, cancelE, BoCa.Fig16.Tree.Wp.SchedProgs.SpawnProgs.parkE, Expr.subst, performE,
    opPayload, Val.pair, Val.i32, Val.unit, Expr.val, Val.prim]

/-- **The canceller child** `park (); cancel ()`. -/
theorem thC_ok (hΦ : Φ.Down) (hPS : ∀ k ls v ρ, PS (k + 1) ls v ρ → PS k ls v ρ) (n : Nat)
    (ls : List SRec) :
    erwp (ℍ := ℍ) Φ (opTableN (tabOfN (ℍ := ℍ) Φ PS)) QVN n ls (.app thC.1 (.val Val.unit))
      PMap.empty := by
  have hTD := opTableN_down (tabOfN_down (ℍ := ℍ) hΦ hPS)
  refine erwp_det hΦ hTD QVN_down (fun μ => step1Only_plug (Head.beta μ _ Val.unit) rfl .hole) ?_
  rw [Kont.plug_hole, Cbody_closed]
  refine erwp_parkAt hΦ hPS (tabOfN_park _ _) (.appR (.lam (.app (.lam (.val .unit)) cancelE)) .hole)
    (fun _ => rfl) (fun _ => rfl) fun k' _ ls' => ?_
  refine erwp_det hΦ hTD QVN_down (fun μ => step1Only_plug (Head.beta μ _ Val.unit) rfl .hole) ?_
  have e : Kont.hole.plug (Expr.subst 0 Val.unit (.app (.lam (.val .unit)) cancelE)) =
      (Kont.appR (.lam (.val .unit)) .hole).plug
        (performE (.val (opPayload nP 2 Val.unit))) := by
    simp [Expr.subst, Kont.plug, cancelE, performE, opPayload, Val.pair, Val.i32, Val.unit,
      Expr.val, Val.prim]
  rw [e]
  refine erwp_parkAt hΦ hPS (tabOfN_cancel _ _) (.appR (.lam (.val .unit)) .hole) (fun _ => rfl)
    (fun _ => rfl) fun k'' _ ls'' => ?_
  refine erwp_det hΦ hTD QVN_down (fun μ => step1Only_plug (Head.beta μ _ Val.unit) rfl .hole) ?_
  exact erwp_val (v := Val.unit) rfl

end Children

/-- Each child is verified at every indexed table, so is a spawn payload. -/
theorem childOK_thL {Φ : LocFam} (hΦ : Φ.Down) (k : Nat) :
    ChildOKN (ℍ := ℍ) Φ (tabAtN (ℍ := ℍ) Φ) k thL := fun j _ ls => by
  rw [tabAtN_eq]; exact thL_ok hΦ (spawnPAN_down _ _) j ls

theorem childOK_thC {Φ : LocFam} (hΦ : Φ.Down) (k : Nat) :
    ChildOKN (ℍ := ℍ) Φ (tabAtN (ℍ := ℍ) Φ) k thC := fun j _ ls => by
  rw [tabAtN_eq]; exact thC_ok hΦ (spawnPAN_down _ _) j ls

/-! ### The roots and the hardest case -/

/-- **A spawn holding nothing, then a continuation**, at the scheduler's table. -/
theorem erwp_spawnThen {Φ : LocFam} (hΦ : Φ.Down) {th : Val}
    (hth : ∀ k, ChildOKN (ℍ := ℍ) Φ (tabAtN (ℍ := ℍ) Φ) k th) (b : Expr)
    (hb : ∀ k ls, erwp (ℍ := ℍ) Φ (opTableN (TJN (ℍ := ℍ) Φ)) QVN k ls (b.subst 0 Val.unit)
      PMap.empty) (n : Nat) (ls : List SRec) :
    erwp (ℍ := ℍ) Φ (opTableN (TJN (ℍ := ℍ) Φ)) QVN n ls (letE (spawnE th) b) PMap.empty := by
  have hTD := opTableN_down (TJN_down (ℍ := ℍ) hΦ)
  have hKH : ∀ m, (Kont.appR (.lam b) .hole).HasHnd m = false := fun _ => rfl
  have hKC : ∀ m, (Kont.appR (.lam b) .hole).Catches m = false := fun _ => rfl
  show erwp (ℍ := ℍ) Φ _ _ _ _ ((Kont.appR (.lam b) .hole).plug
    (performE (.val (opPayload nP 1 th)))) _
  refine erwp_performG _ (hKH nP) (tabOfN_spawn _ _) rfl (compS_empty_left _) ⟨rfl, hth n⟩
    (fun _ => rfl) (fun ls' _ k' hk' w σB XB ⟨hw, hσ⟩ hXB => ?_)
    (fun ls' _ _ P hP => by cases hP; exact cancel_plain _ hKH hKC _ _)
  subst hw hσ
  obtain rfl := eq_of_compS_empty_left hXB
  exact erwp_det hΦ hTD QVN_down (fun μ => step1Only_plug (Head.beta μ b Val.unit) rfl .hole)
    (hb k' ls')

theorem taskA_closed (v : Val) : taskA.subst 0 v = taskA := by
  simp [taskA, letE, allocE, Expr.subst, subst_closedAt _ _ dRec_closed (Nat.zero_le _),
    subst_closedAt _ _ cbRec_closed (Nat.zero_le _),
    subst_closedAt _ _ withborUd_closed (Nat.zero_le _), Val.prim, Expr.val]

/-- **`rootMut` at the scheduler's table**: spawn `thL`, then task A. -/
theorem rootMut_ok {Φ : LocFam} (hΦ : Φ.Down) (n : Nat) (ls : List SRec) :
    erwp (ℍ := ℍ) Φ (opTableN (TJN (ℍ := ℍ) Φ)) QVN n ls rootMut PMap.empty :=
  erwp_spawnThen hΦ (childOK_thL hΦ) taskA (fun k ls => by
    rw [taskA_closed]; exact taskA_ok hΦ default k ls) n ls

/-- **`rootMutC` at the scheduler's table**: spawn `thL`, spawn `thC`, then task A. -/
theorem rootMutC_ok {Φ : LocFam} (hΦ : Φ.Down) (n : Nat) (ls : List SRec) :
    erwp (ℍ := ℍ) Φ (opTableN (TJN (ℍ := ℍ) Φ)) QVN n ls rootMutC PMap.empty := by
  refine erwp_spawnThen hΦ (childOK_thL hΦ) _ (fun k ls => ?_) n ls
  have e : (letE (spawnE thC) taskA).subst 0 Val.unit = letE (spawnE thC) taskA := by
    simp [letE, spawnE, thC, Cbody, cancelE, Expr.subst, performE, opPayload, Val.pair, Val.i32,
      Val.unit, Val.lam, Expr.val, Val.prim, taskA_closed]
    repeat (first | rfl | constructor)
  rw [e]
  exact erwp_spawnThen hΦ (childOK_thC hΦ) taskA (fun k ls => by
    rw [taskA_closed]; exact taskA_ok hΦ default k ls) k ls

open BoCa.Fig16.Tree.Wp.Goal791 (HardestCase791 HardestCase791C progMut progMutC)

/-- **#791's hardest case, resumed**, through `poolSchedAdequacyN` (`progOfN_orDiverges`): task A
holds a `mut` reborrow of the boxed field of its `mut`-borrowed record across `park`, while `thL`
holds its cell across its own `park`; every configuration a run of `progOf rootMut` reaches steps
or is a value, a value only at the empty memory, and every `free` finds its cell. -/
theorem hardestCase791 : HardestCase791 (ℍ := ℍ) :=
  progOfN_orDiverges Φ₀_down fun n => rootMut_ok Φ₀_down n []

/-- **#791's hardest case, cancelled**: `thC` cancels task A while A holds the field's borrow; the
cancel unwinds through the field's lend, the anti-frame and the record's lend to `dRec`. -/
theorem hardestCase791C : HardestCase791C (ℍ := ℍ) :=
  progOfN_orDiverges Φ₀_down fun n => rootMutC_ok Φ₀_down n []

end BoCa.Fig16.LogRel.Core.Chain.SI.Hardest791

end
