import Core.Chain.LetKW835N

/-!
# `[then]` at the typed world  `[spec §14, §19, §27]`

`Then835N`'s `then_compatN` at `SemJN`, step for step: `erwpK_frame_then` around `M` at the
relation's reading (`rdN`), the frame the context of `N` and `D` at the frame's world, consistent
with its view, at a world whose location typing is `OK` (`letFrN`). At a stop the frame moves to the
world the continuation is resumed at along the order the entry owes (as `gNFrame_carryKW`); `M`'s
values are consistent with the view of the world they are posted at (`erwpK_consistentAns`), so `N`
is read there, from the value beside the frame, and `D` at the world its run starts at.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel (substAll)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Head Kont performE raiseE cancelVal opPayload)

/-- **`[let]`'s frame along an entry's order**: the frame at the stop's world, at a part of a valid
share at which the entry owes `y`, is the frame at `y` (`gN_extR`, `consistentX_right`, and `y`'s
location typing `OK` from `KW.Owed`). -/
theorem letFrN_carry (δ : LSub) (Γ : Ctx VTy) (γ : List Val) (N : Nat) :
    ∀ (μ : Unit) (m : UInt32) (x : KW) (f : Life) (y : KW) (ls ls' : List SRec)
      (ρ σ ρ' : WRes), ResU.CompS ρ σ ρ' → ResU.Valid ρ' → (rdN (ℍ := ℍ) δ).wk μ m x f y ρ' →
      extF ls ls' ρ' → letFrN (ℍ := ℍ) δ Γ γ N x ls σ → letFrN (ℍ := ℍ) δ Γ γ N y ls' σ := by
  intro _ m x f y ls ls' ρ σ ρ' hc hv hy _ hF
  have hy' : x.Owed f y ρ' := hy
  exact ⟨gN_extR (hy'.1.extR.right hc) hF.1, consistentX_right hc hy'.2.2.1 hv, hy'.2.1⟩

/-- **`[then]` at `SemJN`** (Core's `then_compatC`): `M then x. N unwind D` at `Σ`, `M` at
`Σ_M ≤ Σ`, the finaliser at `Σ_D ≤ Σ`, each capturable operation of `Σ_M` with
`Σ(o).fin ≥ Σ_M(o).fin ⋈ Σ_D`, the errors pending at the finaliser persistent where `Σ_D` has an
unrestricted operation. `erwpK_frame_then` around `M` at every floor, the frame the context of `N`
and `D` (`letFrN`); `M`'s value consistent with the view across its resumptions
(`erwpK_consistentAns`), so `N` is read at the world the value is posted at, from the value beside
the frame. -/
theorem then_compatN {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {M N D : Expr} {A B : VTy}
    {S SM SD : Row} (hsp : Ctx.SplitP Γ Γ₁ Γ₂) (hNZ : S.NZ) (hU : S.UnrD → Ctx.Banged Γ₂)
    (hMS : RowLe SM S) (hDS : RowLe SD S)
    (hfin : ∀ n i o o', Row.find SM n i = some o → Row.find S n i = some o' →
      capB o.q o.B = true → ThenLe o.fin SD o'.fin)
    (hP : SD.UnrD → SM.PendPers)
    (hM : SemJN (ℍ := ℍ) Δ Γ₁ M (.comp (CTy.effOf SM A)))
    (hN : SemJN (ℍ := ℍ) Δ (⟨A, true⟩ :: Γ₂) N (.comp (CTy.effOf S B)))
    (hD : SemJN (ℍ := ℍ) Δ (⟨.unit, false⟩ :: Γ₂) D (.comp (CTy.effOf SD .unit))) :
    SemJN (ℍ := ℍ) Δ Γ (thenE N D M) (.comp (CTy.effOf S B)) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  refine (cN_effOf_tabF S B δ Θ c n ls _ ρ).mpr fun lo => erwpK_of_valid fun hv => ?_
  obtain ⟨ρ₁, ρ₂, hcρ, hg₁, hg₂, hc₁, hc₂⟩ := gN_splitC hsp hg hc hv
  obtain ⟨hlw₁, hlw₂⟩ := hsp.liveWithin hlw
  have hM' := (cN_effOf_tabF SM A δ Θ c n ls _ ρ₁).mp (hM δ γ Θ c n ls ρ₁ hδ hΘ hc₁ hlw₁ hg₁) lo
  rw [tabF_effOf_ret (rdN (ℍ := ℍ) δ) () SM A .unit] at hM'
  have hM'' := erwpK_consistentAns (c := fun z : KW => z.c)
    (fun x m i en hT y k ls w ρ hB => tabF_ansC δ _ x m i en hT y k ls w ρ hB)
    (fun x m i en hT f y ρ hy _ => (tabF_wkC δ _ x m i en hT f y ρ hy).2.1)
    (fun x y (h : y = x) => by rw [h]) n n le_rfl (⟨Θ, c, lo⟩ : KW) ls _ ρ₁ hM' hc₁
  have hQd : ∀ (y : KW) (k : Nat) (ls : List SRec) (v : Val) (ρ : WRes),
      vN (ℍ := ℍ) .unit δ y.Θ k v ρ → v = .unit ∧ NoOwn ρ := by
    rintro y k ls' v σ ⟨rfl, rfl⟩
    exact ⟨rfl, noOwn_empty⟩
  -- the finaliser, from the frame, at the world its run starts at
  have hD' : ∀ x : KW, x.Θ.Down → ∀ k, k ≤ n → ∀ ls' σ, letFrN (ℍ := ℍ) δ Γ₂ γ n x ls' σ →
      erwpK (ℍ := ℍ) KW.PostK (fun z => z.Θ.view z.c)
        (fun z => opTableK z.lo (tabF (ℍ := ℍ) (rdN (ℍ := ℍ) δ) () (CTy.effOf SD .unit) z))
        (fun z k _ v ρ => vN (ℍ := ℍ) .unit δ z.Θ k v ρ) x k ls'
        (.app (.val (Val.lam (Expr.psub 1 γ D))) (.val .unit)) σ := by
    rintro x - k hk ls' σ ⟨hσ, hcσ, hxOK⟩
    refine (cN_effOf_tabF SD .unit δ x.Θ x.c k ls' _ σ).mp ?_ x.lo
    refine cN_head (CTy.effOf SD .unit) δ x.Θ hxOK.1 x.c k ls' σ .hole _ _
      (fun μ => Head.beta μ (Expr.psub 1 γ D) Val.unit) rfl ?_
    rw [show Kont.hole.plug (Expr.subst 0 Val.unit (Expr.psub 1 γ D)) =
      substAll (Val.unit :: γ) D from (substAll_cons_psub Val.unit γ D).symm]
    exact hD δ (Val.unit :: γ) x.Θ x.c k ls' σ hδ hxOK hcσ hlw₂
      (gN_dead_cons .unit Val.unit (gN_le hk hσ))
  -- the continuation, from the value beside the frame, at the world it is posted at
  have hk : ∀ x : KW, x.Θ.Down → ∀ k, k ≤ n → ∀ ls' (v : Val) σ,
      ((fun (y : KW) (k : Nat) (_ : List SRec) (v : Val) (ρ : WRes) => k ≤ n ∧
        vN (ℍ := ℍ) A δ y.Θ k v ρ ∧ ConsistentX y.c ρ ∧ ResU.Valid ρ) x k ls' v ⋆
          letFrN (ℍ := ℍ) δ Γ₂ γ n x ls') σ →
      erwpK (ℍ := ℍ) KW.PostK (fun z => z.Θ.view z.c)
        (fun z => opTableK z.lo (tabF (ℍ := ℍ) (rdN (ℍ := ℍ) δ) () (CTy.effOf S .unit) z))
        (fun z k _ v ρ => vN (ℍ := ℍ) B δ z.Θ k v ρ) x k ls'
        ((ubindK (Val.lam (Expr.psub 1 γ N)) (Val.lam (Expr.psub 1 γ D))).plug (.val v)) σ := by
    rintro x - k hk ls' v σ ⟨σ₁, σ₂, hcσ, ⟨-, hv, hcv, -⟩, hg₂', hc₂', hxOK⟩
    rw [← tabF_effOf_ret (rdN (ℍ := ℍ) δ) () S B .unit]
    refine (cN_effOf_tabF S B δ x.Θ x.c k ls' _ σ).mp ?_ x.lo
    refine cN_head (CTy.effOf S B) δ x.Θ hxOK.1 x.c k ls' σ .hole _ _
      (fun μ => Head.uthen μ _ _ v) rfl ?_
    refine cN_head (CTy.effOf S B) δ x.Θ hxOK.1 x.c k ls' σ .hole _ _
      (fun μ => Head.beta μ (Expr.psub 1 γ N) v) rfl ?_
    rw [show Kont.hole.plug (Expr.subst 0 v (Expr.psub 1 γ N)) = substAll (v :: γ) N
      from (substAll_cons_psub v γ N).symm]
    exact hN δ (v :: γ) x.Θ x.c k ls' σ hδ hxOK (consistentX_compS hcσ hcv hc₂') hlw₂
      (gN_live_cons hcσ hv (gN_le hk hg₂'))
  change erwpK (ℍ := ℍ) _ _ _ _ _ n ls
    ((ubindK (Val.lam (Expr.psub 1 γ N)) (Val.lam (Expr.psub 1 γ D))).plug (substAll γ M)) ρ
  rw [tabF_effOf_ret (rdN (ℍ := ℍ) δ) () S B .unit]
  exact erwpK_frame_then (rdN_ok δ) (rdN_payExt δ) S SM SD hNZ hMS hDS hfin hP _ _
    (letFrN (ℍ := ℍ) δ Γ₂ γ n) (fun _ _ _ _ _ h => h)
    (fun μ m x f y ls ls' ρ σ ρ' _ => letFrN_carry δ Γ₂ γ n μ m x f y ls ls' ρ σ ρ')
    (fun hu _ _ σ h => gN_persistent (hU hu) h.1) hQd n hD' _ _
    (fun z k _ v ρ h => vN_down B δ z.Θ k v ρ h) hk n le_rfl (⟨Θ, c, lo⟩ : KW) hΘ.1 ls _ ρ₁
    hM'' ρ₂ ρ ⟨hg₂, hc₂, hΘ⟩ hcρ

/-- **`[then]` with a finaliser that may loop** (Core's `then_compatC_div`): `M`'s row has no
capturable operation (`hcap`), so `then_compatN`'s cancel-row record holds of no operation, and
this is `then_compatN`. -/
theorem thenDiv_compatN {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {M N D : Expr} {A B : VTy}
    {S SM SD : Row} (hsp : Ctx.SplitP Γ Γ₁ Γ₂) (hNZ : S.NZ) (hU : S.UnrD → Ctx.Banged Γ₂)
    (hMS : RowLe SM S) (hDS : RowLe SD S)
    (hP : SD.UnrD → SM.PendPers) (hcap : ∀ o ∈ SM, capB o.q o.B = false)
    (hM : SemJN (ℍ := ℍ) Δ Γ₁ M (.comp (CTy.effOf SM A)))
    (hN : SemJN (ℍ := ℍ) Δ (⟨A, true⟩ :: Γ₂) N (.comp (CTy.effOf S B)))
    (hD : SemJN (ℍ := ℍ) Δ (⟨.unit, false⟩ :: Γ₂) D (.comp (CTy.effOf SD .unit))) :
    SemJN (ℍ := ℍ) Δ Γ (thenE N D M) (.comp (CTy.effOf S B)) :=
  then_compatN hsp hNZ hU hMS hDS (fun _ _ o _ hf _ h => by
    rw [hcap o (Row.find_mem hf).1] at h; cases h) hP hM hN hD

/-! ### The loop -/

/-- **`cN`'s tables are closed in the index at the worlds whose location typing is `OK`**, and every
world an entry owes at is one (`KW.Owed`). -/
theorem tabN_downI_OK (F : CTy) (δ : LSub) (x : KW) :
    (tabN (ℍ := ℍ) F δ x).DownI (fun z : KW => z.Θ.OK) := by
  have h := tabNK_downI (ℍ := ℍ) valRelOK_vN id F δ x
  rw [tabNK_vN] at h
  refine ⟨h.pa, fun n i en P hT hP y hy => h.fin n i en P hT hP y hy.1,
    fun n i en hT f y ρ hy => ?_⟩
  rw [tabN_eq] at hT
  obtain ⟨o, -, rfl⟩ := tabF_rowOf_find hT
  exact (show x.Owed f y ρ from hy).2.1

/-- **E5 at `cN`'s tables, at the worlds whose location typing is `OK`** (`tabNK_ctxClosed`). -/
theorem tabN_ctxClosed_OK (F : CTy) (δ : LSub) (K : Kont) (hH : ∀ m, K.HasHnd m = false)
    (hC : K.Catches 0 = false) (x : KW) :
    (tabN (ℍ := ℍ) F δ x).CtxClosedI (fun z : KW => z.Θ.OK) K := by
  have h := tabNK_ctxClosed (ℍ := ℍ) valRelOK_vN id F δ K hH hC x
  rw [tabNK_vN] at h
  exact fun m i en P hT hP y hy => h m i en P hT hP y hy.1

/-- **`iterate` is sound at `SemJN`**, at a row holding `Div` (Core's `iterate_compatX`): the step
`f` and the state `s` from the argument; E14 at the invariant `𝒱⟦S⟧ ∧ ConsistentX` read at a
world (`erwpK_iterateCI`, at the worlds whose location typing is `OK`), the tick the row's `tick`
(`tabN_tick`), the invariant carried along the tick's order. A turn runs at the world the loop is
at: the step, a `!` thunk owning nothing, is read there (`LocTy.extR_empty`), its turn's answer
consistent with that world's view (`erwpK_consistentAns`). -/
theorem iterate_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {Sg : Row} {St B R : VTy}
    (hS : Row.divB Sg = true) (hΓ : Ctx.DeadP Γ) :
    SemJN (ℍ := ℍ) Δ Γ (.val (.prim .iterate)) (.val (iterTy Sg St B R)) := by
  intro δ γ Θ c n ls ρ _ _ _ _ hg
  obtain rfl := gN_deadP hΓ hg
  refine cN_ret_of ?_
  show erwp (ℍ := ℍ) _ _ _ n ls (substAll γ (.val (.prim .iterate))) PMap.empty
  rw [show substAll γ (.val (.prim .iterate)) = .val (.prim .iterate) from
    psub_closedAt _ γ (by decide) (Nat.zero_le 0)]
  refine erwp_val (v := Val.prim .iterate) ⟨rfl, ?_⟩
  intro Θ' _ hΘ' _ _ ls' c'' k hk v σ τ hcomp hv hcon
  obtain rfl := eq_of_compS_empty_left hcomp
  obtain ⟨f, s, σf, σs, rfl, hcfs, ⟨rfl, hf⟩, hs⟩ := hv
  obtain rfl := eq_of_compS_empty_left hcfs
  refine (cN_effOf Sg (.sum B R) δ Θ' c'' k ls' _ _).mpr fun lo => ?_
  -- the step, at every world the loop reaches
  have hstep : ∀ y : KW, y.Θ.OK → ∀ j, j ≤ k → ∀ s' ls₁ ρ₁, vN (ℍ := ℍ) St δ y.Θ j s' ρ₁ →
      ConsistentX y.c ρ₁ →
      cN (ℍ := ℍ) (.amp (CTy.effOf Sg (.sum B St)) (CTy.effOf Sg R)) δ y.Θ y.c j ls₁
        (.app (.val f) (.val s')) ρ₁ := by
    intro y hy j hj s' ls₁ ρ₁ hs' hc'
    exact hf y.Θ (LocTy.extR_empty Θ' y.Θ) hy y.c (consistentX_empty _) ls₁ y.c j hj s' ρ₁ ρ₁
      (compS_empty_left ρ₁) hs' hc'
  have hD : ∀ x, (tabN (ℍ := ℍ) (CTy.effOf Sg (.sum B R)) δ x).DownI (fun z : KW => z.Θ.OK) :=
    fun x => tabN_downI_OK _ δ x
  have hK : ∀ (K : Kont), (∀ m, K.HasHnd m = false) → K.Catches 0 = false → ∀ x,
      (tabN (ℍ := ℍ) (CTy.effOf Sg (.sum B R)) δ x).CtxClosedI (fun z : KW => z.Θ.OK) K :=
    fun K hH hC x => tabN_ctxClosed_OK _ δ K hH hC x
  refine erwpK_iterateCI (V := KW.PostK) KW.postK_refl (fun _ _ _ h₁ h₂ => h₁.trans h₂)
    (Φ := fun z => z.Θ.view z.c) (Inv := fun z : KW => z.Θ.OK)
    (fun x hx => LocTy.view_down hx.1 x.c) (fun _ _ h => by rw [h])
    (fun _ _ h hx => by rw [h]; exact hx) (fl := fun z => z.lo) hD
    (fun _ _ h => tabLe_postK (fun z => opTableK z.lo (tabN (ℍ := ℍ) _ δ z)) h)
    (hK (iterK f) (fun m => by simp [iterK, Kont.HasHnd]) (by simp [iterK, Kont.Catches]))
    (hK inrK inrK_plain.1 (inrK_plain.2 0))
    (QL := fun z k _ v ρ => vN (ℍ := ℍ) (.sum B R) δ z.Θ k v ρ)
    (QR := fun z k _ v ρ => vN (ℍ := ℍ) R δ z.Θ k v ρ)
    (fun z k _ v ρ h => vN_down _ δ z.Θ k v ρ h)
    (I := fun z k s ρ => vN (ℍ := ℍ) St δ z.Θ k s ρ ∧ ConsistentX z.c ρ)
    (fun _ _ _ _ _ hk h => ⟨vN_le hk h.1, h.2⟩)
    (fun x => _root_.BoCa.Fig16.LogRel.Core.Chain.SI.tabN_tick hS St (.sum B R) δ x) k ?_ ?_ (fun _ _ _ r _ h => Or.inr ⟨r, rfl, h⟩) k le_rfl
    (⟨Θ', c'', lo⟩ : KW) hΘ' s ls' _ ⟨hs, hcon⟩
  · -- a turn: `(f s′).1`, its answer consistent with the view of the world it is posted at
    rintro y hy j hj s' ls₁ ρ₁ ⟨hs', hc'⟩
    have h₁ := (cN_effOf Sg (.sum B St) δ y.Θ y.c j ls₁ _ _).mp (hstep y hy j hj s' ls₁ ρ₁ hs' hc').1
      y.lo
    rw [show (tabN (ℍ := ℍ) (CTy.effOf Sg (.sum B St)) δ) = tabN (ℍ := ℍ) (CTy.effOf Sg (.sum B R)) δ
      from funext fun x => by rw [tabN_eq, tabN_eq, tabF_effOf_ret]] at h₁
    have h₂ := erwpK_consistentAns (c := fun z : KW => z.c)
      (fun x m i en hT y k ls w ρ hB =>
        tabF_ansC δ _ x m i en (by rw [← tabN_eq]; exact hT) y k ls w ρ hB)
      (fun x m i en hT f y ρ hy _ =>
        (tabF_wkC δ _ x m i en (by rw [← tabN_eq]; exact hT) f y ρ hy).2.1)
      (fun x y (h : y = x) => by rw [h]) j j le_rfl y ls₁ _ ρ₁ h₁ hc'
    refine erwpK_mono
      (Tb := fun z : KW => opTableK z.lo (tabN (ℍ := ℍ) (CTy.effOf Sg (.sum B R)) δ z))
      (Tb' := fun z : KW => opTableK z.lo (tabN (ℍ := ℍ) (CTy.effOf Sg (.sum B R)) δ z))
      (fun _ _ h => h) (fun y' k₁ ls₂ v₁ ρ₂ hq => ?_)
      (fun z k ls t Ψ Ψ' ρ hΨ hh => opTableK_local _ _ k ls t Ψ Ψ' ρ hΨ hh) j y ls₁ _ ρ₁ h₂
    obtain ⟨-, hq, hcq, -⟩ := hq
    rcases hq with ⟨x, rfl, hx⟩ | ⟨s'', rfl, hs''⟩
    · exact Or.inl ⟨x, rfl, Or.inl ⟨x, rfl, hx⟩⟩
    · exact Or.inr ⟨s'', rfl, hs'', hcq⟩
  · -- the close path's observation `(f s′).2`
    rintro y hy j hj s' ls₁ ρ₁ ⟨hs', hc'⟩
    have h₂ := (cN_effOf Sg R δ y.Θ y.c j ls₁ _ _).mp (hstep y hy j hj s' ls₁ ρ₁ hs' hc').2 y.lo
    rw [show (tabN (ℍ := ℍ) (CTy.effOf Sg R) δ) = tabN (ℍ := ℍ) (CTy.effOf Sg (.sum B R)) δ
      from funext fun x => by rw [tabN_eq, tabN_eq, tabF_effOf_ret]] at h₂
    exact h₂

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
