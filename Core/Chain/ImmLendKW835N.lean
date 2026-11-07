import Core.Chain.ImmImageKW835N

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

/-!
# `withbor (1)` and `withbor (2)` at the pure row, at the typed world  `[spec §62]`

`ImmLend833N`'s pure-row lends at `SemJN`: the callback stops nowhere, so the one-world Imm and
Mut Frames apply at `F A`'s empty table (`cN_ret_iff`).
-/

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel (LtLife substAll)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Kont Head ubindE)

/-! ### A dead context -/

/-- **A consumed context's slots hold at every world and every lower index** (Core's
`semV_dead_closed`): its live slots are persistent, own nothing, and so are read at every
extension (`ExtR` at `∅` relates every two worlds) and lower index. -/
theorem gN_dead_any {δ : LSub} {Θ : LocTy} {n : Nat} : ∀ {Γ : Ctx VTy}, Ctx.DeadP Γ →
    ∀ {γ : List Val} {ρ : WRes}, gN (ℍ := ℍ) δ Θ Γ γ n ρ →
      ∀ (Θ' : LocTy) (k : Nat), k ≤ n → gN (ℍ := ℍ) δ Θ' Γ γ k PMap.empty := by
  intro Γ hd
  induction hd with
  | nil => intro γ ρ _ Θ' k _; cases γ <;> rfl
  | cons _ ih =>
      intro γ ρ h Θ' k hk
      cases γ with
      | nil => rfl
      | cons v γ' =>
          simp only [gN] at h ⊢
          exact ih h Θ' k hk
  | weaken hT _ ih =>
      intro γ ρ h Θ' k hk
      cases γ with
      | nil => rfl
      | cons v γ' =>
          simp only [gN, if_true] at h ⊢
          obtain ⟨ρ₁, ρ₂, hc, hv, hrest⟩ := h
          have h₁ := vN_empty_of_persistent _ hT hv
          subst h₁
          have hE : Θ.ExtR Θ' PMap.empty :=
            ⟨fun _ _ _ _ hc => absurd hc (fun ⟨m, ψ, e, _⟩ => by simp at e),
              fun _ _ hc => absurd hc (fun ⟨m, ψ, e, _⟩ => by simp at e)⟩
          exact ⟨PMap.empty, PMap.empty, ResU.comp_empty_right _,
            vN_le hk (vN_extR _ δ n v _ hE hv), ih hrest Θ' k hk⟩

/-! ### `withbor (1)` at the pure row -/

/-- **`withbor (1)` is a value of its type**: `withbor` at
`Ref A ⊸ (∀'x ⊏ @Δ. Imm 'x A ⊸ ['x] B) ⊸ Ref A ⊗ B`. Core's `withbor1_compatX`, step by step,
at the pure row: the source read at the callback's world, the lend at a lifetime below the bound,
the content's stratum and the callback's, its record in the callback's world (Core's
`ext_add hadd hout₂`), the borrow a value of `Imm 'x A` there; `f ()` and the borrow's application
under the pair (Core's `wpTS_bind (.pairR ℓ □)`), framed beside the borrow; the result `['x] B`
back at the world without the record (`ext_drop`); the Imm Frame (`erwp_I_frameR`). -/
theorem withbor1_sem {Δ : LifeCtx} {x : LifeVar} {A B : VTy} {δ : LSub} (hδ : Δ.Models δ)
    (hadm : AdmWf A δ) (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) (Θ₀ : LocTy) (n : Nat) :
    vN (ℍ := ℍ) (axWithbor1Ty x Δ.meetOfDom A B) δ Θ₀ n withborVal PMap.empty := by
  intro Θ₂ _ _ c₁ _ ls c₂ k hk u ρv ρu hc hu _
  obtain rfl := eq_of_compS_empty_left hc
  obtain ⟨l, w₀, σ₀, rfl, hcl, hw₀⟩ := hu
  have hΦ₂ : (Θ₂.view c₂).Down := LocTy.view_down (by assumption : Θ₂.OK).1 c₂
  have hQ₂ : PostN.Down (fun k _ v ρ => vN (ℍ := ℍ)
      (.lolli (.all x Δ.meetOfDom (.lolli (.imm (.var x) A) (.box (.var x) B)))
        (.tensor (.ref A) B)) δ Θ₂ k v ρ) := fun k _ v ρ h => vN_down _ δ Θ₂ k v ρ h
  refine cN_ret_of ?_
  refine erwp_det hΦ₂ (opTableN_down OpTabN.empty_down) hQ₂
    (fun μ => step1Only_plug (Head.beta μ _ (Val.loc l)) rfl .hole) ?_
  have e₁ : Kont.hole.plug (Expr.subst 0 (Val.loc l)
      (Val.lam (.pair BoCa.v1 (.app (.app BoCa.v0 unit') BoCa.v1))).1) = (withborAt l).1 := by
    simp [Kont.plug, Expr.subst, Expr.shift, withborAt, BoCa.v0, BoCa.v1, unit', Val.loc,
      Val.lam, Expr.val, Val.unit]
  rw [e₁]
  refine erwp_val (v := withborAt l) ?_
  intro Θ' hE₃ hΘ' c _ ls' c' k' hk' f ρf ρ'' hc' hf hcon
  -- the source at the callback's world
  obtain ⟨l₁, w₀', σ₀', hl₁, hcl', hw₀'⟩ := vN_le hk'
    (vN_extR (.ref A) δ k _ ρu hE₃ ⟨l, w₀, σ₀, rfl, hcl, hw₀⟩)
  obtain rfl : l = l₁ := by
    have := congrArg Subtype.val hl₁; simpa [Val.loc] using this
  have hΦ : (Θ'.view c').Down := LocTy.view_down hΘ'.1 c'
  have hQo : PostN.Down (fun k _ v ρ => vN (ℍ := ℍ) (.tensor (.ref A) B) δ Θ' k v ρ) :=
    fun k _ v ρ h => vN_down _ δ Θ' k v ρ h
  refine cN_ret_of ?_
  refine erwp_det hΦ (opTableN_down OpTabN.empty_down) hQo
    (fun μ => step1Only_plug (Head.beta μ _ f) rfl .hole) ?_
  have e₂ : Kont.hole.plug (Expr.subst 0 f
      (.pair (.val (Val.loc l)) (.app (.app BoCa.v0 unit') (.val (Val.loc l))))) =
      (Kont.pairR (Val.loc l) (Kont.appL Kont.hole (Val.loc l))).plug
        (.app (.val f) (.val Val.unit)) := by
    simp [Kont.plug, Expr.subst, BoCa.v0, unit', Val.loc, Expr.val, Val.unit]
  rw [e₂]
  refine erwp_of_valid fun hv'' => ?_
  have hvu : ResU.Valid ρu := (ResU.Valid.split hc' hv'').1
  have hcf : ConsistentX c' ρf := consistentX_right hc' hcon hv''
  -- the lend's lifetime and record
  obtain ⟨γ, hγ⟩ : ∃ m, Δ.meetOfDom.interp δ = some m :=
    Lifetime.Life.interp_defined_of_wf hδ (Lifetime.meetOfDomL_wf Δ.entries)
  obtain ⟨βf, hβf⟩ := ResU.exists_stratum ρf
  obtain ⟨βP, hβP⟩ := ResU.exists_stratum σ₀'
  set α : Life := ↓(βP ⊓ βf ⊓ γ) with hαdef
  have hαlt : α < βP ⊓ βf ⊓ γ := Life.down_sqsubset _
  have houtP : σ₀'.InStratum α := hβP.mono (hαlt.le.trans (inf_le_left.trans inf_le_left))
  have houtb : ρf.InStratum α := hβf.mono (hαlt.le.trans (inf_le_left.trans inf_le_right))
  have hLt : LtLife δ Δ.meetOfDom α := ⟨γ, hγ, lt_of_lt_of_le hαlt inf_le_right⟩
  set δ' := δ.extend x α with hδ'
  set p : FrameRec := ⟨l, w₀', σ₀', A, δ⟩ with hpdef
  have hvσ : ResU.Valid σ₀' := (ResU.Valid.split hcl' hvu).2
  obtain ⟨-, eR, -, heR, -, -⟩ := hvσ
  obtain ⟨ds, hds⟩ := lineage_list (r := p) (vN_vShape A δ Θ' k' w₀' σ₀' hw₀') hadm heR
  set Θ'' := Θ'.addImm (p, α) with hΘ''
  have hOK'' : Θ''.OK := ⟨fun l' b F h => hΘ'.1 l' b F h,
    let ⟨N, hN⟩ := hΘ'.2; ⟨N, fun l' b h => hN l' b h⟩⟩
  have hΦi : (Θ''.view c').Down := LocTy.view_down hOK''.1 c'
  set ρi : WRes := ResU.single l (CellU.immOf (LSet.singleton α) w₀' σ₀' houtP) with hρi
  set P : List SRec → Val → WProp := fun _ v ρ => vN (ℍ := ℍ) A δ Θ' k' v ρ with hP
  set Q : PostN := fun k _ v ρ => vN (ℍ := ℍ) (.tensor (.ref A) B) δ Θ' k v ρ with hQ
  have hIF := erwp_I_frameR (Φ := Θ'.view c') l A δ hadm w₀' P
    (fun _ ρ h => vN_vShape A δ Θ' k' w₀' ρ h) (fun _ _ _ _ h => h)
    (Tb := OpTabN.empty) (empty_iLendOKR α)
    (Q := Q) (fun _ _ _ _ _ _ h => h) k' ls'
    ((Kont.pairR (Val.loc l) (Kont.appL Kont.hole (Val.loc l))).plug (.app (.val f) (.val Val.unit)))
    σ₀' ρu ρf ρ'' houtP houtb hw₀' hcl' hc' ds hds
    (fun BI hBI => ?_)
  · refine erwp_mono (fun _ _ _ _ h => h) (fun j ls₁ t Ψ Ψ' ρ hΨ h => ?_) k' ls' _ ρ'' hIF
    rcases h with ⟨K, m, i, v, en, h⟩ | ⟨K, m, i, v, en, h⟩
    · obtain ⟨⟨-, -, hTe, -⟩, -⟩ := pure_sep_iff.mp h; simp [OpTabN.empty] at hTe
    · obtain ⟨⟨-, -, hTe, -⟩, -⟩ := pure_sep_iff.mp h; simp [OpTabN.empty] at hTe
  · -- the borrow at the callback's world
    have hvO : vO (ℍ := ℍ) A δ' Θ'' k' w₀' σ₀' := by
      rw [vO_extend_of_not_free hfree₁]
      exact vO_extR A δ k' w₀' σ₀' (LocTy.extR_addImm Θ' p houtP) (vN_vO A δ Θ' k' w₀' σ₀' hw₀')
    have hcell : vN (ℍ := ℍ) (.imm (.var x) A) δ' Θ'' k' (Val.loc l) ρi := by
      refine ⟨α, interp_ext_self δ x α, ⟨l, LSet.singleton α, w₀', σ₀', houtP, rfl, rfl,
        le_refl _, hvO⟩, fun l₀ s₀ u₀ σ₁ h₀ e => ?_⟩
      obtain ⟨rfl, e'⟩ := single_immOf_inj e
      obtain ⟨rfl, -⟩ := CellU.immOf_inj e'
      exact ⟨(p, α), List.mem_cons_self .., le_refl _, p, DescR.refl _, A, δ', TyEq.refl _ _,
        Or.inl ⟨p, List.mem_singleton_self _, rfl, rfl, fun y hy =>
          BoCa.Fig16.LogRel.find?_extend_ne δ α (fun e => by subst e; exact hfree₁ hy)⟩⟩
    have hci : ConsistentX c' ρi := consistentX_allImm (fun m ψ e => by
      obtain ⟨-, rfl⟩ := ResU.single_get_eq_some e
      exact CellU.kind_immOf _ _ _ _) c'
    -- the run, at the callback's world, read at the lender's view
    refine erwp_tieEntry (Φ := Θ'.view c') (Φ' := Θ''.view c') (T := OpTabN.empty) rfl
      (fun _ _ _ h => by simp [OpTabN.empty] at h)
      (fun y hy => by
        rcases List.mem_cons.mp hy with rfl | hy
        · exact .inr (List.mem_cons_self ..)
        · exact .inl hy) (erwp_of_rwp ?_)
    refine rwp_bind hΦi _ ?_
    -- `f ()`, beside the borrow
    have hcb := (hf Θ'' (LocTy.extR_addImm Θ' p houtb) hOK'' c' hcf (frameList p ds α ls')) α hLt
    have hfr := rwp_frame (fun _ τ => τ = ρi) (fun _ _ _ _ h => h) hBI (rwp_of_erwp_empty (erwp_of_cN_ret hcb)) rfl
    refine rwp_mono_le (fun j hj ls₂ g τ hg => ?_) (rwp_consistentXV hfr
      (consistentX_compS hBI hcf hci))
    obtain ⟨⟨τg, τi, hcτ, hgv, rfl⟩, hcτ', hvτ⟩ := hg
    -- the borrow's application
    have happ := hgv Θ'' (LocTy.extR_refl _ _) hOK'' c' (consistentX_left hcτ hcτ' hvτ) ls₂
      c' j le_rfl (Val.loc l) ρi τ hcτ (vN_le hj hcell) hcτ'
    show rwp (ℍ := ℍ) _ _ j ls₂ ((Kont.pairR (Val.loc l) Kont.hole).plug
      (.app (.val g) (.val (Val.loc l)))) τ
    refine rwp_bind hΦi _ ?_
    refine rwp_mono_le (fun j' hj' ls₃ b ρb hb => ?_) (rwp_of_erwp_empty (erwp_of_cN_ret happ))
    -- the pair, and the result back at the world without the record
    refine rwp_val (v := Val.pair (Val.loc l) b) ?_
    obtain ⟨β, hβ, hbB, hst⟩ := hb
    rw [interp_ext_self] at hβ
    cases Option.some.inj hβ
    refine ⟨fun Y X hY hX σ Z hσ hZ => ?_, hst⟩
    subst hY
    obtain ⟨Wc, hWc, hZ'⟩ :=
      (ResU.CompS.assoc ρb (ResU.single l (CellU.ownOf w₀')) σ Z).mpr ⟨X, hX, hZ⟩
    have hbB' : vN (ℍ := ℍ) B δ Θ' j' b ρb := by
      rw [vN_extend_of_not_free hfree₂] at hbB
      exact vN_extR B δ j' b ρb (LocTy.extR_of_addImm Θ' p hst) hbB
    exact ⟨Val.loc l, b, Wc, ρb, rfl, ResU.CompS.comm hZ',
      ⟨l, w₀', σ, rfl, hWc, vN_le (hj'.trans (hj.trans le_rfl)) hσ⟩, hbB'⟩

/-- **`withbor1` at `SemJN`** (Core's `withbor1_compatX`). -/
theorem withbor1_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {A B : VTy} (x : LifeVar)
    (hΓ : Ctx.DeadP Γ) (hsc₁ : VScoped Δ A) (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) :
    SemJN (ℍ := ℍ) Δ Γ withbor (.val (axWithbor1Ty x Δ.meetOfDom A B)) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  obtain rfl := gN_deadP hΓ hg
  refine cN_ret_of ?_
  show erwp (ℍ := ℍ) (Θ.view c) (opTableN OpTabN.empty) _ n ls (substAll γ withbor) _
  rw [show substAll γ withbor = withbor from psub_closedAt _ γ (by decide) (Nat.zero_le 0)]
  exact erwp_val (v := withborVal) (withbor1_sem hδ (admWf_of_vScoped hsc₁ hδ) hfree₁ hfree₂ Θ n)

/-! ### `withbor (2)` at the pure row -/

/-- **`withbor (2)` is a value of its type**: `withbor` at
`Ref A ⊸ (∀'x ⊏ @Δ. Mut 'x A ⊸ ['x] B) ⊸ Ref A ⊗ B`. Core's `withbor2_compatX`, step by step, at
the pure row: the source read at the callback's world; the lend at a lifetime fresh for the world,
below the bound, `[TR]` 6.60's stratum at the side condition and the callback's; the callback's
world `Θ + (ℓ, α) ↦ famL α 𝒱⟦A⟧`; `f ()` and the borrow's application under the pair, framed beside
the borrow; the result `['x] B` back at the world without the lend (`vN_local`); the Mut Frame
(`erwp_M_frameR`, Core's `wpTS_M_frameX`). -/
theorem withbor2_sem {Δ : LifeCtx} {x : LifeVar} {A B : VTy} {δ : LSub} (hδ : Δ.Models δ)
    (hO : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A) (hA : ¬ VFree x A) (hB : ¬ VFree x B)
    (Θ₀ : LocTy) (n : Nat) :
    vN (ℍ := ℍ) (axWithbor2Ty x Δ.meetOfDom A B) δ Θ₀ n withborVal PMap.empty := by
  intro Θ₂ _ _ c₁ _ ls c₂ k hk u ρv ρu hc hu _
  obtain rfl := eq_of_compS_empty_left hc
  obtain ⟨l, w₀, σ₀, rfl, hcl, hw₀⟩ := hu
  have hΦ₂ : (Θ₂.view c₂).Down := LocTy.view_down (by assumption : Θ₂.OK).1 c₂
  have hQ₂ : PostN.Down (fun k _ v ρ => vN (ℍ := ℍ)
      (.lolli (.all x Δ.meetOfDom (.lolli (.mut (.var x) A) (.box (.var x) B)))
        (.tensor (.ref A) B)) δ Θ₂ k v ρ) := fun k _ v ρ h => vN_down _ δ Θ₂ k v ρ h
  refine cN_ret_of ?_
  refine erwp_det hΦ₂ (opTableN_down OpTabN.empty_down) hQ₂
    (fun μ => step1Only_plug (Head.beta μ _ (Val.loc l)) rfl .hole) ?_
  have e₁ : Kont.hole.plug (Expr.subst 0 (Val.loc l)
      (Val.lam (.pair BoCa.v1 (.app (.app BoCa.v0 unit') BoCa.v1))).1) = (withborAt l).1 := by
    simp [Kont.plug, Expr.subst, Expr.shift, withborAt, BoCa.v0, BoCa.v1, unit', Val.loc,
      Val.lam, Expr.val, Val.unit]
  rw [e₁]
  refine erwp_val (v := withborAt l) ?_
  intro Θ' hE₃ hΘ' c _ ls' c' k' hk' f ρf ρ'' hc' hf hcon
  obtain ⟨l₁, w₀', σ₀', hl₁, hcl', hw₀'⟩ := vN_le hk'
    (vN_extR (.ref A) δ k _ ρu hE₃ ⟨l, w₀, σ₀, rfl, hcl, hw₀⟩)
  obtain rfl : l = l₁ := by
    have := congrArg Subtype.val hl₁; simpa [Val.loc] using this
  have hΦ : (Θ'.view c').Down := LocTy.view_down hΘ'.1 c'
  have hQo : PostN.Down (fun k _ v ρ => vN (ℍ := ℍ) (.tensor (.ref A) B) δ Θ' k v ρ) :=
    fun k _ v ρ h => vN_down _ δ Θ' k v ρ h
  refine cN_ret_of ?_
  refine erwp_det hΦ (opTableN_down OpTabN.empty_down) hQo
    (fun μ => step1Only_plug (Head.beta μ _ f) rfl .hole) ?_
  have e₂ : Kont.hole.plug (Expr.subst 0 f
      (.pair (.val (Val.loc l)) (.app (.app BoCa.v0 unit') (.val (Val.loc l))))) =
      (Kont.pairR (Val.loc l) (Kont.appL Kont.hole (Val.loc l))).plug
        (.app (.val f) (.val Val.unit)) := by
    simp [Kont.plug, Expr.subst, BoCa.v0, unit', Val.loc, Expr.val, Val.unit]
  rw [e₂]
  refine erwp_of_valid fun hv'' => ?_
  have hvu : ResU.Valid ρu := (ResU.Valid.split hc' hv'').1
  have hcf : ConsistentX c' ρf := consistentX_right hc' hcon hv''
  have hcσ : ConsistentX c' σ₀' := consistentX_right hcl' (consistentX_left hc' hcon hv'') hvu
  have hko : (CellU.ownOf (Loc := Loc) w₀').kind ≠ Kind.imm := by simp
  have hown : ρu.get l = some (CellU.ownOf w₀') :=
    (ResU.CompS.get_left_of_ne_imm hcl' (ResU.single_get_self _ _) hko).2
  -- the lend's lifetime
  obtain ⟨γ, hγ⟩ : ∃ m, Δ.meetOfDom.interp δ = some m :=
    Lifetime.Life.interp_defined_of_wf hδ (Lifetime.meetOfDomL_wf Δ.entries)
  obtain ⟨b, hdef, hOb⟩ := hO
  obtain ⟨βP, hβP⟩ : ∃ β : Life, b.interp δ = some β := hdef δ hδ
  obtain ⟨βf, hβf⟩ := ResU.exists_stratum ρf
  obtain ⟨α, hαle, hfr⟩ := LocTy.exists_fresh hΘ'.2 (↓(βP ⊓ βf ⊓ γ))
  have hαlt : α < βP ⊓ βf ⊓ γ := lt_of_le_of_lt hαle (Life.down_sqsubset _)
  have hαP : α < βP := lt_of_lt_of_le hαlt (inf_le_left.trans inf_le_left)
  have hunif : ∀ (Θ'' : LocTy) (j : Nat) (u : Val) (r : WRes), vN (ℍ := ℍ) A δ Θ'' j u r →
      r.InStratum α :=
    vN_outlivesLe hδ hβP hαP hOb
  have houtP : σ₀'.InStratum α := hunif Θ' k' w₀' σ₀' hw₀'
  have houtf : ρf.InStratum (↓α) := hβf.mono
    ((Life.down_sqsubset α).le.trans (hαlt.le.trans (inf_le_left.trans inf_le_right)))
  have hLt : LtLife δ Δ.meetOfDom α := ⟨γ, hγ, lt_of_lt_of_le hαlt inf_le_right⟩
  set δ' := δ.extend x α with hδ'
  have hAδ : vN (ℍ := ℍ) A δ' = vN (ℍ := ℍ) A δ := vN_extend_of_not_free hA δ α
  have hBδ : vN (ℍ := ℍ) B δ' = vN (ℍ := ℍ) B δ := vN_extend_of_not_free hB δ α
  set P : CPredL := fun Θ'' j u r => vN (ℍ := ℍ) A δ' Θ'' j u r with hP
  set Fam : Nat → Val → SPropS Loc Val α := famL α P Θ' with hFam
  have hFamD : DownFam α Fam := vN_fam_down A δ' α Θ'
  have hwit : Fam k' w₀' ⟨σ₀', houtP⟩ := (vN_above A δ' Θ' houtP).mpr (by rw [hAδ]; exact hw₀')
  set Θ'' := Θ'.add l α Fam with hΘ''
  set c'' := setLife c' l α with hc''def
  have hOK'' : Θ''.OK := by
    obtain ⟨N, hN⟩ := hΘ'.2
    exact ⟨LocTy.down_add hΘ'.1 l hFamD, ⟨min N (↓α), LocTy.fresh_add hN (min_le_left _ _)
      (lt_of_le_of_lt (min_le_right _ _) (Life.down_sqsubset α)) l Fam⟩⟩
  have hview : Θ''.view c'' = (Θ'.view c').set l α Fam := LocTy.view_add Θ' c' l α Fam
  have hcf'' : ConsistentX c'' ρf :=
    consistentX_setLife hcf (exS_none_of_part hc' hv'' hown hko) α
  have hcσ' : ConsistentX c'' σ₀' :=
    consistentX_setLife hcσ (exS_none_of_part hcl' hvu (ResU.single_get_self _ _) hko) α
  set Q : PostN := fun k _ v ρ => vN (ℍ := ℍ) (.tensor (.ref A) B) δ Θ' k v ρ with hQ
  have hMF := erwp_M_frameR (Φ := Θ'.view c') (l := l) (A := α) (F := Fam) hFamD
    (T := OpTabN.empty) ⟨fun _ _ _ h => by simp [OpTabN.empty] at h,
      fun _ _ _ h => by simp [OpTabN.empty] at h, fun _ _ _ h => by simp [OpTabN.empty] at h⟩
    (Q := Q) k' k' le_rfl ls'
    ((Kont.pairR (Val.loc l) (Kont.appL Kont.hole (Val.loc l))).plug (.app (.val f) (.val Val.unit)))
    w₀' σ₀' ρu ρf ρ'' houtP houtf (Fam k') (fun _ _ h => h) hwit hcl' hc' (fun BM hBM => ?_)
  · refine erwp_mono (fun _ _ _ _ h => h) (fun j ls₁ t Ψ Ψ' ρ hΨ h => ?_) k' ls' _ ρ'' hMF
    rcases h with ⟨K, m, i, v, en, h⟩ | ⟨K, m, i, v, en, h⟩
    · obtain ⟨⟨-, -, hTe, -⟩, -⟩ := pure_sep_iff.mp h; simp [OpTabN.empty] at hTe
    · obtain ⟨⟨-, -, hTe, -⟩, -⟩ := pure_sep_iff.mp h; simp [OpTabN.empty] at hTe
  · -- the callback, at the lend's world and view, from the borrow
    rw [← hview]
    have hΦi : (Θ''.view c'').Down := LocTy.view_down hOK''.1 c''
    have hcell : vN (ℍ := ℍ) (.mut (.var x) A) δ' Θ'' k' (Val.loc l)
        (ResU.single l (CellU.mutOf α w₀' σ₀' houtP (Fam k') hwit)) :=
      ⟨α, interp_ext_self δ x α, α, le_rfl, lend_mutL Θ' l α P le_rfl houtP hwit,
        fun Θ₃ j u r h => hunif Θ₃ j u r (by rw [← hAδ]; exact h)⟩
    have hcm : ConsistentX c'' (ResU.single l (CellU.mutOf α w₀' σ₀' houtP (Fam k') hwit)) :=
      consistentX_single_mut hcσ' (by simp [hc''def, setLife])
    refine erwp_of_rwp (rwp_bind hΦi _ ?_)
    have hcb := (hf Θ'' ((LocTy.extA_add hfr l Fam).extR ρf) hOK'' c'' hcf'' ls') α hLt
    have hfr' := rwp_frame (fun _ τ => τ = ResU.single l (CellU.mutOf α w₀' σ₀' houtP (Fam k') hwit))
      (fun _ _ _ _ h => h) hBM (rwp_of_erwp_empty (erwp_of_cN_ret hcb)) rfl
    refine rwp_mono_le (fun j hj ls₂ g τ hg => ?_) (rwp_consistentXV hfr'
      (consistentX_compS hBM hcf'' hcm))
    obtain ⟨⟨τg, τm, hcτ, hgv, rfl⟩, hcτ', hvτ⟩ := hg
    have happ := hgv Θ'' (LocTy.extR_refl _ _) hOK'' c'' (consistentX_left hcτ hcτ' hvτ) ls₂
      c'' j le_rfl (Val.loc l) _ τ hcτ (vN_le hj hcell) hcτ'
    show rwp (ℍ := ℍ) _ _ j ls₂ ((Kont.pairR (Val.loc l) Kont.hole).plug
      (.app (.val g) (.val (Val.loc l)))) τ
    refine rwp_bind hΦi _ ?_
    refine rwp_mono_le (fun j' hj' ls₃ b ρb hb => ?_) (rwp_of_erwp_empty (erwp_of_cN_ret happ))
    refine rwp_val (v := Val.pair (Val.loc l) b) ?_
    obtain ⟨β, hβ, hbB, hst⟩ := hb
    rw [interp_ext_self] at hβ
    cases Option.some.inj hβ
    refine ⟨hst, fun w Y hY σ ⟨hσ, hFσ⟩ Z hZ => ?_⟩
    obtain ⟨Wc, hWc, hZ'⟩ :=
      (ResU.CompS.assoc ρb (ResU.single l (CellU.ownOf w)) σ Z).mpr ⟨Y, hY, hZ⟩
    have hwσ : vN (ℍ := ℍ) A δ Θ' j' w σ := by
      rw [← hAδ]; exact (vN_above A δ' Θ' hσ).mp hFσ
    have hbB' : vN (ℍ := ℍ) B δ Θ' j' b ρb :=
      vN_local B δ Θ' l α Fam j' b ρb hst (by rw [← hBδ]; exact hbB)
    exact ⟨Val.loc l, b, Wc, ρb, rfl, ResU.CompS.comm hZ', ⟨l, w, σ, rfl, hWc, hwσ⟩, hbB'⟩

/-- **`withbor2` at `SemJN`** (Core's `withbor2_compatX`). -/
theorem withbor2_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {A B : VTy} (x : LifeVar)
    (hΓ : Ctx.DeadP Γ) (hside : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A) (hfree₁ : ¬ VFree x A)
    (hfree₂ : ¬ VFree x B) :
    SemJN (ℍ := ℍ) Δ Γ withbor (.val (axWithbor2Ty x Δ.meetOfDom A B)) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  obtain rfl := gN_deadP hΓ hg
  refine cN_ret_of ?_
  show erwp (ℍ := ℍ) (Θ.view c) (opTableN OpTabN.empty) _ n ls (substAll γ withbor) _
  rw [show substAll γ withbor = withbor from psub_closedAt _ γ (by decide) (Nat.zero_le 0)]
  exact erwp_val (v := withborVal) (withbor2_sem hδ hside hfree₁ hfree₂ Θ n)

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N


end
