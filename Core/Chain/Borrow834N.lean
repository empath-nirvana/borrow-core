import Core.Chain.Rules834N

/-!
# `withswap` at `SemJN`  `[spec §62]`

Core's `withswap_compatX` (`Core/Compatibility.lean`), step by step, at the per-lend world and the
pure row. The source's cell is at its view lifetime and the view types it with its family
(`erwp_antiFrame_view`, the anti-frame at the view, Core's `wpTS_M_antiFrameX`); the content is
loaded (`rwp_load`), handed to the callback, framed beside the cell (`erwp_bind_frame`, Core's
`wpTS_bind_frame`), and the callback's first component stored back (`rwp_store`); the resealed cell
is a `Mut @a A` value again, at the content's index.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel (LtLife substAll)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Kont Head eLoad eStore)

/-- `withswap` as a value. -/
def withswapV : Val := ⟨withswap, .lam⟩

/-- A single owned cell is consistent with every view: it is in the top stratum. -/
theorem consistentX_single_own (c : Loc → Option Life) (l : Loc) (w : Val) :
    ConsistentX c (ResU.single l (CellU.ownOf w)) :=
  consistentX_of_top (ResU.inStratum_single_own _ l w) c

/-- The body of `withswap` at the source `ℓ`, after the first β step. -/
def withswapAt (l : Loc) : Val :=
  Val.lam (.letpair (.app BoCa.v0 (eLoad l))
    (.seq (.app (.app store' (.val (.loc l))) BoCa.v1) (.pair (.val (.loc l)) BoCa.v0)))

/-- **`withswap` at `SemJN`** (Core's `withswap_compatX`):
`Mut @a A ⊸ (A ⊸ A ⊗ B) ⊸ Mut @a A ⊗ B` at the pure row. -/
theorem withswap_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {A B : VTy}
    (hΓ : Ctx.DeadP Γ) : SemJN (ℍ := ℍ) Δ Γ withswap (.val (axWithswapTy a A B)) := by
  intro δ γ Θ c n ls ρ _ _ _ _ hg
  obtain rfl := gN_deadP hΓ hg
  show erwp (ℍ := ℍ) (Θ.view c) (opTableN OpTabN.empty) _ n ls (substAll γ withswap) _
  rw [show substAll γ withswap = withswap from psub_closedAt _ γ (by decide) (Nat.zero_le 0)]
  refine erwp_val (v := withswapV) ?_
  -- the source, at the world the constant's `U` reached
  intro Θ₁ _ hΘ₁ _ _ ls₁ c₂ k₁ _ v₁ τ₀ ρ₁ hcomp hv₁ _
  obtain rfl := eq_of_compS_empty_left hcomp
  obtain ⟨α₀, hα₀, b, hα₀b, hm₁, hunif⟩ := hv₁
  obtain ⟨l, -, -, -, -, -, -, rfl, -, -⟩ := id hm₁
  have hΦ₁ : (Θ₁.view c₂).Down := LocTy.view_down hΘ₁.1 c₂
  refine erwp_det hΦ₁ (opTableN_down OpTabN.empty_down) (fun k _ v ρ h => vN_down _ δ Θ₁ k v ρ h)
    (fun μ => step1Only_plug (Head.beta μ _ (Val.loc l)) rfl .hole) ?_
  have e₁ : Kont.hole.plug (Expr.subst 0 (Val.loc l)
      (Expr.val (Val.lam (.letpair (.app BoCa.v0 (.app load' BoCa.v1))
        (.seq (.app (.app store' BoCa.v3) BoCa.v1) (.pair BoCa.v3 BoCa.v0)))))) =
      (withswapAt l).1 := by
    simp [Kont.plug, eLoad, Expr.subst, Expr.shift, BoCa.v0, BoCa.v1, BoCa.v3, load', store',
      withswapAt, Val.loc, Val.lam, Expr.val, Val.prim]
  rw [e₁]
  refine erwp_val (v := withswapAt l) ?_
  -- the callback, at the world the body's `U` reached; the source arrives there along `ExtR`
  intro Θ₂ hE₂ hΘ₂ _ _ ls₂ c₄ k₂ hk₂ vf ρf τ₂ hc₂ hvf hcon
  have hΦ : (Θ₂.view c₄).Down := LocTy.view_down hΘ₂.1 c₄
  set P : CPredL := fun Θ' j u r => vN (ℍ := ℍ) A δ Θ' j u r with hP
  have hm : mutL b P Θ₂ k₂ (Val.loc l) ρ₁ := by
    obtain ⟨l₀, w, χ, hχ, j, hw, hj, h₁, h₂, h₃⟩ := hm₁
    exact mutL_extR hE₂ ⟨l₀, w, χ, hχ, j, hw, by omega, h₁, h₂, h₃⟩
  set Q : PostN := fun k _ v ρ => vN (ℍ := ℍ) (.tensor (.mut a A) B) δ Θ₂ k v ρ with hQ
  refine erwp_det hΦ (opTableN_down OpTabN.empty_down) (fun k _ v ρ h => vN_down _ δ Θ₂ k v ρ h)
    (fun μ => step1Only_plug (Head.beta μ _ vf) rfl .hole) ?_
  have e₂ : Kont.hole.plug (Expr.subst 0 vf (.letpair (.app BoCa.v0 (eLoad l))
      (.seq (.app (.app store' (.val (.loc l))) BoCa.v1) (.pair (.val (.loc l)) BoCa.v0)))) =
      (Kont.letpair (.appR (.val vf) .hole)
        (.seq (.app (.app store' (.val (.loc l))) BoCa.v1) (.pair (.val (.loc l)) BoCa.v0))).plug
        (eLoad l) := by
    simp [Kont.plug, eLoad, Expr.subst, BoCa.v0, BoCa.v1, store', Val.loc, Expr.val, Val.prim]
  rw [e₂]
  refine erwp_of_valid fun hv => ?_
  -- the source's cell is at its view lifetime
  obtain ⟨l', w₀, σ₀, hσ₀, j₀, hw₀, hkj, hl', hlΘ, rfl⟩ := id hm
  obtain rfl : l = l' := by have := congrArg Subtype.val hl'; simpa [Val.loc] using this
  have hkm : (CellU.mutOf b w₀ σ₀ hσ₀ (famL b P Θ₂ j₀) hw₀).kind ≠ Kind.imm := by
    rw [CellU.kind_mutOf]; exact fun c => Kind.noConfusion c
  have hget : τ₂.get l = some (CellU.mutOf b w₀ σ₀ hσ₀ (famL b P Θ₂ j₀) hw₀) :=
    (ResU.CompS.get_left_of_ne_imm hc₂ (ResU.single_get_self _ _) hkm).2
  have hcb : c₄ l = some b := by
    have h := consistentX_get hcon hv hget (CellU.kind_mutOf _ _ _ _ _ _)
    rwa [CellU.at_mutOf] at h
  have hvc : ResU.Valid (ResU.single l (CellU.mutOf b w₀ σ₀ hσ₀ (famL b P Θ₂ j₀) hw₀)) :=
    (ResU.Valid.split hc₂ hv).1
  have hcf : ConsistentX c₄ ρf := consistentX_right hc₂ hcon hv
  have hcσ : ConsistentX c₄ σ₀ := consistentX_mut_wit (consistentX_left hc₂ hcon hv) hvc
  -- `wp-m-anti-frame` at the view; the payload it hands over is the cell's own
  refine erwp_M_antiFrame hΦ (LocTy.view_some hcb hlΘ) (T := OpTabN.empty)
    (fun _ _ _ h => by cases h) k₂ ls₂ _ w₀ σ₀ hσ₀ j₀ hw₀ ρf τ₂ hc₂ (fun W X hW hX => ?_)
  have hwA : vN (ℍ := ℍ) A δ Θ₂ j₀ w₀ σ₀ := (vN_above A δ Θ₂ hσ₀).mp hw₀
  -- `wp-bind` at the argument `load ℓ`, then `wp-load`
  obtain ⟨rest, hrest, hXr⟩ := compS_lcomm (ResU.CompS.comm hW) hX
  refine erwp_bindR hΦ (opTableG_local _ _) _ ?_
  refine rwp_load ls₂ l w₀ _ ⟨_, rest, hXr, rfl, fun ρ₁' ρ₂' hpto hcomp' => ?_⟩
  obtain rfl := hpto
  obtain rfl : X = ρ₂' := (ResU.CompS.functional hcomp' (ResU.CompS.comm hXr)).symm
  simp only [Kont.plug]
  -- the callback at the payload, framing the cell through its run
  have hcrest : ConsistentX c₄ rest := consistentX_compS hrest hcf hcσ
  have hcX : ConsistentX c₄ X := consistentX_compS hXr (consistentX_single_own c₄ l w₀) hcrest
  have happ := hvf Θ₂ (LocTy.extR_refl _ _) hΘ₂ c₄ hcf ls₂ c₄ (k₂ - 1) (Nat.sub_le _ _) w₀ σ₀ rest
    hrest (vN_le (by omega) hwA) hcrest
  refine erwp_bind_frame hΦ (opTableG_local _ _)
    (.letpair .hole (.seq (.app (.app store' (.val (.loc l))) BoCa.v1) (.pair (.val (.loc l)) BoCa.v0)))
    (ptoOwn l w₀) (ResU.CompS.comm hXr) hcX happ rfl ?_
  intro k₃ hk₃ ls₃ v σ₁ σ₂ σ hcσ₃ hvσ hown _ _
  obtain rfl := hown
  obtain ⟨w₃, w₄, ρ₃, ρ₄, rfl, hc34, h₃, h₄⟩ := hvσ
  -- the pair taken apart: a deterministic step, at the index it costs
  cases k₃ with
  | zero => exact erwp_zero
  | succ m =>
  refine erwp_step (opTableG_local _ _) (fun μ => step1Only_plug (Head.letpair μ w₃ w₄ _) rfl .hole) ?_
  have e₃ : Kont.hole.plug (Expr.subst 0 w₃ (Expr.subst 0 (w₄.shift 1 0)
        (.seq (.app (.app store' (.val (.loc l))) BoCa.v1) (.pair (.val (.loc l)) BoCa.v0)))) =
      (Kont.seq .hole (.pair (.val (.loc l)) (.val w₄))).plug
        (.app (.val (Val.storeV (Val.loc l))) (.val w₃)) := by
    simp [Kont.plug, Expr.subst, BoCa.v0, BoCa.v1, store', Val.storeV, Val.loc, Expr.val,
      Val.prim, Expr.subst_shift 0 0 0 w₃ w₄.val (Nat.le_refl 0) (Nat.le_refl 0), Expr.shift_zero]
  rw [e₃]
  -- `wp-store` of the first component, then the pair
  refine erwp_bindR hΦ (opTableG_local _ _) _ ?_
  refine rwp_store ls₃ l w₀ w₃ _ ⟨_, σ₁, ResU.CompS.comm hcσ₃, rfl, fun t₁ t hpto hct => ?_⟩
  obtain rfl := hpto
  simp only [Kont.plug]
  cases m with
  | zero => exact erwp_zero
  | succ m₁ =>
  rw [Nat.add_sub_cancel]
  cases m₁ with
  | zero => exact erwp_zero
  | succ m' =>
  refine erwp_step (opTableG_local _ _) (fun μ => step1Only_plug (Head.seq μ _) rfl .hole) ?_
  refine erwp_val (v := Val.pair (Val.loc l) w₄) ?_
  -- the resealed cell: the stored component, at its index, beside the result
  have hρ₃ : ρ₃.InStratum b := hunif _ _ _ _ h₃
  have hw₃ : famL b P Θ₂ m' w₃ ⟨ρ₃, hρ₃⟩ :=
    (vN_above A δ Θ₂ hρ₃).mpr (vN_le (by omega) h₃)
  refine ⟨w₃, ρ₃, hρ₃, hw₃, ρ₄, σ₁, ResU.CompS.comm hct, hc34, fun X' hX' => ?_⟩
  exact ⟨Val.loc l, w₄, _, ρ₄, rfl, ResU.CompS.comm hX',
    ⟨α₀, hα₀, b, hα₀b, ⟨l, w₃, ρ₃, hρ₃, m', hw₃, le_rfl, rfl, hlΘ, rfl⟩, hunif⟩,
    vN_le (by omega) h₄⟩

/-! ### `withbor (3)` at the pure row -/

/-- **`withbor (3)` at `SemJN`** (Core's `withbor3_compatX`):
`Mut @a A ⊸ (∀'x ⊏ @Δ. Mut 'x A ⊸ ['x] B) ⊸ Mut @a A ⊗ B` at the pure row. Core's steps: the
source's `Mut` value at the callback's world; the anti-frame at its cell (`wpTS_M_antiFrameX`),
the opened content lent at a fresh `α` below the cell, the bound and the callback's stratum
(`wpTS_M_frameX`), the two together `erwp_withbor3` at the view (the source's cell at its view
lifetime, `consistentX_get`); `f ()` and the borrow's application under the pair, framed beside
the borrow (`wpTS_bind (.pairR ℓ □)`, `wpTS_bind_frame`); the result `['x] B` back at the world
without the lend (`vN_local`); the content handed back in `F_i k` is in `F_o k` (`hunif`), and the
resealed cell is a `Mut @a A` value again. -/
theorem withbor3_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {A B : VTy}
    (x : LifeVar) (hΓ : Ctx.DeadP Γ) (hA : ¬ VFree x A) (hB : ¬ VFree x B) :
    SemJN (ℍ := ℍ) Δ Γ withbor (.val (axWithbor3Ty a x Δ.meetOfDom A B)) := by
  intro δ γ Θ c n ls ρ hδ _ _ _ hg
  obtain rfl := gN_deadP hΓ hg
  show erwp (ℍ := ℍ) (Θ.view c) (opTableN OpTabN.empty) _ n ls (substAll γ withbor) _
  rw [show substAll γ withbor = withbor from psub_closedAt _ γ (by decide) (Nat.zero_le 0)]
  refine erwp_val (v := withborVal) ?_
  intro Θ₁ _ hΘ₁ _ _ ls₁ c₂ k₁ _ v₁ τ₀ ρ₁ hcomp hv₁ _
  obtain rfl := eq_of_compS_empty_left hcomp
  obtain ⟨α₀, hα₀, b, hα₀b, hm₁, hunif⟩ := hv₁
  obtain ⟨l, -, -, -, -, -, -, rfl, -, -⟩ := id hm₁
  have hΦ₁ : (Θ₁.view c₂).Down := LocTy.view_down hΘ₁.1 c₂
  refine erwp_det hΦ₁ (opTableN_down OpTabN.empty_down) (fun k _ v ρ h => vN_down _ δ Θ₁ k v ρ h)
    (fun μ => step1Only_plug (Head.beta μ _ (Val.loc l)) rfl .hole) ?_
  have e₁ : Kont.hole.plug (Expr.subst 0 (Val.loc l)
      (Val.lam (.pair BoCa.v1 (.app (.app BoCa.v0 unit') BoCa.v1))).1) = (withborAt l).1 := by
    simp [Kont.plug, Expr.subst, Expr.shift, withborAt, BoCa.v0, BoCa.v1, unit', Val.loc,
      Val.lam, Expr.val, Val.unit]
  rw [e₁]
  refine erwp_val (v := withborAt l) ?_
  -- the callback, at the world the body's `U` reached; the source arrives there along `ExtR`
  intro Θ₂ hE₂ hΘ₂ _ _ ls₂ c k₂ hk₂ f ρf τ₂ hc₂ hf hcon
  have hΦ : (Θ₂.view c).Down := LocTy.view_down hΘ₂.1 c
  set P : CPredL := fun Θ' j u r => vN (ℍ := ℍ) A δ Θ' j u r with hP
  have hm : mutL b P Θ₂ k₂ (Val.loc l) ρ₁ := by
    obtain ⟨l₀, w, χ, hχ, j, hw, hj, h₁, h₂, h₃⟩ := hm₁
    exact mutL_extR hE₂ ⟨l₀, w, χ, hχ, j, hw, by omega, h₁, h₂, h₃⟩
  set Q : PostN := fun k _ v ρ => vN (ℍ := ℍ) (.tensor (.mut a A) B) δ Θ₂ k v ρ with hQ
  refine erwp_det hΦ (opTableN_down OpTabN.empty_down) (fun k _ v ρ h => vN_down _ δ Θ₂ k v ρ h)
    (fun μ => step1Only_plug (Head.beta μ _ f) rfl .hole) ?_
  have e₂ : Kont.hole.plug (Expr.subst 0 f
      (.pair (.val (Val.loc l)) (.app (.app BoCa.v0 unit') (.val (Val.loc l))))) =
      (Kont.pairR (Val.loc l) (Kont.appL Kont.hole (Val.loc l))).plug
        (.app (.val f) (.val Val.unit)) := by
    simp [Kont.plug, Expr.subst, BoCa.v0, unit', Val.loc, Expr.val, Val.unit]
  rw [e₂]
  refine erwp_of_valid fun hv => ?_
  -- the source's cell is at its view lifetime, and the view types it with `F_o`
  obtain ⟨l', w₀, σ₀, hσ₀, j₀, hw₀, hkj, hl', hlΘ, rfl⟩ := id hm
  obtain rfl : l = l' := by have := congrArg Subtype.val hl'; simpa [Val.loc] using this
  have hkm : (CellU.mutOf b w₀ σ₀ hσ₀ (famL b P Θ₂ j₀) hw₀).kind ≠ Kind.imm := by
    rw [CellU.kind_mutOf]; exact fun c => Kind.noConfusion c
  have hget : τ₂.get l = some (CellU.mutOf b w₀ σ₀ hσ₀ (famL b P Θ₂ j₀) hw₀) :=
    (ResU.CompS.get_left_of_ne_imm hc₂ (ResU.single_get_self _ _) hkm).2
  have hcb : c l = some b := by
    have h := consistentX_get hcon hv hget (CellU.kind_mutOf _ _ _ _ _ _)
    rwa [CellU.at_mutOf] at h
  have hvc : ResU.Valid (ResU.single l (CellU.mutOf b w₀ σ₀ hσ₀ (famL b P Θ₂ j₀) hw₀)) :=
    (ResU.Valid.split hc₂ hv).1
  have hcf : ConsistentX c ρf := consistentX_right hc₂ hcon hv
  have hcσ : ConsistentX c σ₀ := consistentX_mut_wit (consistentX_left hc₂ hcon hv) hvc
  -- the lend's lifetime: fresh, below the cell, the bound and the callback's stratum
  obtain ⟨γb, hγb⟩ : ∃ m, Δ.meetOfDom.interp δ = some m :=
    Lifetime.Life.interp_defined_of_wf hδ (Lifetime.meetOfDomL_wf Δ.entries)
  obtain ⟨βf, hβf⟩ := ResU.exists_stratum ρf
  obtain ⟨α, hαle, hfr⟩ := LocTy.exists_fresh hΘ₂.2 (↓(b ⊓ βf ⊓ γb))
  have hαlt : α < b ⊓ βf ⊓ γb := lt_of_le_of_lt hαle (Life.down_sqsubset _)
  have hαβ : α ≤ b := hαlt.le.trans (inf_le_left.trans inf_le_left)
  have houtP : σ₀.InStratum α := hσ₀.mono hαβ
  have houtf : ρf.InStratum (↓α) := hβf.mono
    ((Life.down_sqsubset α).le.trans (hαlt.le.trans (inf_le_left.trans inf_le_right)))
  have hLt : LtLife δ Δ.meetOfDom α := ⟨γb, hγb, lt_of_lt_of_le hαlt inf_le_right⟩
  set δ' := δ.extend x α with hδ'
  have hAδ : vN (ℍ := ℍ) A δ' = vN (ℍ := ℍ) A δ := vN_extend_of_not_free hA δ α
  have hBδ : vN (ℍ := ℍ) B δ' = vN (ℍ := ℍ) B δ := vN_extend_of_not_free hB δ α
  set P' : CPredL := fun Θ' j u r => vN (ℍ := ℍ) A δ' Θ' j u r with hP'
  set Fam : Nat → Val → SPropS Loc Val α := famL α P' Θ₂ with hFam
  have hFamD : DownFam α Fam := vN_fam_down A δ' α Θ₂
  have hwit : Fam j₀ w₀ ⟨σ₀, houtP⟩ :=
    (vN_above A δ' Θ₂ houtP).mpr (by rw [hAδ]; exact (vN_above A δ Θ₂ hσ₀).mp hw₀)
  have hoi : ∀ k w σ (h : σ.InStratum α), Fam k w ⟨σ, h⟩ →
      ∃ h' : σ.InStratum b, famL b P Θ₂ k w ⟨σ, h'⟩ := by
    intro k w σ h hw
    have hv' : vN (ℍ := ℍ) A δ Θ₂ k w σ := by rw [← hAδ]; exact (vN_above A δ' Θ₂ h).mp hw
    exact ⟨hunif Θ₂ k w σ hv', (vN_above A δ Θ₂ (hunif Θ₂ k w σ hv')).mpr hv'⟩
  -- the callback's world and view
  set Θ' := Θ₂.add l α Fam with hΘ'
  set c' := setLife c l α with hc'def
  have hOK' : Θ'.OK := by
    obtain ⟨N, hN⟩ := hΘ₂.2
    exact ⟨LocTy.down_add hΘ₂.1 l hFamD, ⟨min N (↓α), LocTy.fresh_add hN (min_le_left _ _)
      (lt_of_le_of_lt (min_le_right _ _) (Life.down_sqsubset α)) l Fam⟩⟩
  have hview : Θ'.view c' = (Θ₂.view c).set l α Fam := LocTy.view_add Θ₂ c l α Fam
  have hcf' : ConsistentX c' ρf :=
    consistentX_setLife hcf (exS_none_of_part hc₂ hv (ResU.single_get_self _ _) hkm) α
  have hcσ' : ConsistentX c' σ₀ := consistentX_setLife hcσ (exS_wit_none hvc) α
  -- the anti-frame at the source and the Mut Frame at the lend (`erwp_withbor3`)
  refine erwp_withbor3 hΦ (LocTy.view_some hcb hlΘ) hFamD (T := OpTabN.empty)
    ⟨fun _ _ _ h => by simp [OpTabN.empty] at h, fun _ _ _ h => by simp [OpTabN.empty] at h,
      fun _ _ _ h => by simp [OpTabN.empty] at h⟩
    (fun _ _ _ h => by simp [OpTabN.empty] at h) hoi (Q := Q) k₂ ls₂ _ w₀ σ₀ hσ₀ j₀ hkj hw₀ houtP hwit ρf τ₂
    houtf hc₂ (fun BM hBM => ?_)
  -- the callback, at the lend's world and view, from the borrow
  rw [← hview]
  have hΦi : (Θ'.view c').Down := LocTy.view_down hOK'.1 c'
  have hcell : vN (ℍ := ℍ) (.mut (.var x) A) δ' Θ' k₂ (Val.loc l)
      (ResU.single l (CellU.mutOf α w₀ σ₀ houtP (Fam j₀) hwit)) :=
    ⟨α, interp_ext_self δ x α, α, le_rfl, lend_mutL Θ₂ l α P' hkj houtP hwit,
      fun Θ₃ j u r h => (hunif Θ₃ j u r (by rw [← hAδ]; exact h)).mono hαβ⟩
  have hcm : ConsistentX c' (ResU.single l (CellU.mutOf α w₀ σ₀ houtP (Fam j₀) hwit)) :=
    consistentX_single_mut hcσ' (by simp [hc'def, setLife])
  refine erwp_of_rwp (rwp_bind hΦi _ ?_)
  have hcb' := (hf Θ' ((LocTy.extA_add hfr l Fam).extR ρf) hOK' c' hcf' ls₂) α hLt
  have hfr' := rwp_frame (fun _ τ => τ = ResU.single l (CellU.mutOf α w₀ σ₀ houtP (Fam j₀) hwit))
    (fun _ _ _ _ h => h) hBM (rwp_of_erwp_empty hcb') rfl
  refine rwp_mono_le (fun j hj ls₃ g τ hg => ?_) (rwp_consistentXV hfr'
    (consistentX_compS hBM hcf' hcm))
  obtain ⟨⟨τg, τm, hcτ, hgv, rfl⟩, hcτ', hvτ⟩ := hg
  have happ := hgv Θ' (LocTy.extR_refl _ _) hOK' c' (consistentX_left hcτ hcτ' hvτ) ls₃
    c' j le_rfl (Val.loc l) _ τ hcτ (vN_le hj hcell) hcτ'
  show rwp (ℍ := ℍ) _ _ j ls₃ ((Kont.pairR (Val.loc l) Kont.hole).plug
    (.app (.val g) (.val (Val.loc l)))) τ
  refine rwp_bind hΦi _ ?_
  refine rwp_mono_le (fun j' hj' ls₄ b' ρb hb => ?_) (rwp_of_erwp_empty happ)
  refine rwp_val (v := Val.pair (Val.loc l) b') ?_
  obtain ⟨β', hβ', hbB, hst⟩ := hb
  rw [interp_ext_self] at hβ'
  cases Option.some.inj hβ'
  refine ⟨hst, fun w Y hY σ ⟨hσ, hFσ⟩ Z hZ => ?_⟩
  -- the result back at `Θ₂`; the content in `F_o k`, the cell resealed
  obtain ⟨h', hw'⟩ := hoi j' w σ hσ hFσ
  obtain ⟨ac, hac, hacZ⟩ := compS_exch hY hZ
  have hbB' : vN (ℍ := ℍ) B δ Θ₂ j' b' ρb :=
    vN_local B δ Θ₂ l α Fam j' b' ρb hst (by rw [← hBδ]; exact hbB)
  exact ⟨w, σ, h', hw', ρb, ac, ResU.CompS.comm hacZ, ResU.CompS.comm hac, fun X' hX' =>
    ⟨Val.loc l, b', _, ρb, rfl, ResU.CompS.comm hX',
      ⟨α₀, hα₀, b, hα₀b, ⟨l, w, σ, h', j', hw', le_rfl, rfl, hlΘ, rfl⟩, hunif⟩, hbB'⟩⟩

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
