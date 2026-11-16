import Core.Chain.HandleTKW835N

/-!
# The storing clause at the typed world  `[spec §19]`

A handler of one must-resume operation `n.0 : B ↠^lin B` whose clause is fixed: it stores the
continuation `κ` in an owned cell, runs a closed computation `N` at a row `Σ_N` of must-resume
operations below `Σ`, takes `κ` back out of the cell and resumes it with the payload it received:

  `λ(p, κ). c ← alloc κ; _ ← N; k ← free c; k (inj₁ ()) p`.

`erwp_handle_store` is its handler law at `erwpK`, generic in `N`, the rows and the payload type `B`,
by `erwp_handle_tail`'s proof (`erwpK_handle_leI` at the table pre-passed by `erwpK_postPA`). The
clause pays its `β` step, allocates the cell and runs `N` from the floor `f` the handled stop chose
(`erwpK_flr_tabN`), under a frame (`erwpK_frame_plain_orI`, from `Σ_N` to `Σ`) of three parts:

* the cell `c ↦ κ`;
* the payload `p`, a value of `B` at the world reached, consistent with its view, moved along
  `ExtR` at each stop of `N` (`vN_extR`);
* `κ`'s relation at its share, the world reached owed from the clause's at `f`: at the start by
  `postOK`, and across each stop of `N`, taken at a floor no higher than `f`, by `KW.Owed.left`,
  `KW.Owed.floor_le` and `KW.Owed.trans`.

At `N`'s value the cell is freed, and `κ` is resumed with `p` at the world reached, by its relation.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa.BoLo (Heap Head Kont performE raiseE cancelVal opPayload hndE hndVal clauseAt capTag)
open BoCa.Lifetime (LSub LifeCtx)

/-! ### The clause -/

/-- `k (inj₁ ()) p`, under `k` and the `d` binders above it (`p` the payload). -/
def storeResE (v : Val) (d : Nat) : Expr :=
  .app (.app (.var 0) (.val (Val.inj₁ .unit))) (.val (v.shift d 0))

/-- The clause's body under `λ(p, κ)`: `c ← alloc κ; _ ← N; k ← free c; k (inj₁ ()) p`. -/
def storeBody (N : Expr) : Expr :=
  .app (.val (Val.lam (.app (.val (Val.lam (.app (.val (Val.lam
    (.app (.app (.var 0) (.val (Val.inj₁ .unit))) (.var 4)))) (BoLo.freeE (.var 1))))) N)))
    (.app (.val (Val.prim .alloc)) (.var 0))

/-- **The storing clause**: `λ(p, κ). c ← alloc κ; _ ← N; k ← free c; k (inj₁ ()) p`. -/
def storeClause (N : Expr) : Val := Val.lam (.letpair (.var 0) (storeBody N))

/-- The handler of one operation at the storing clause, its return clause `vr`. -/
def storeH (n : UInt32) (vr : Val) (N : Expr) : Val :=
  hndVal n (qualsVal [.lin]) vr ⟨.pair (storeClause N).1 (.val .unit), .pair .lam .unit⟩

/-- The context of the allocation. -/
def storeK₁ (v : Val) (N : Expr) : Kont :=
  .appR (.val (Val.lam (.app (.val (Val.lam (.app (.val (Val.lam (storeResE v 3)))
    (BoLo.freeE (.var 1))))) N))) .hole

/-- The context of `N`, the cell at `ℓ`. -/
def storeK₂ (v : Val) (ℓ : Loc) : Kont :=
  .appR (.val (Val.lam (.app (.val (Val.lam (storeResE v 2))) (BoLo.freeE (.val (Val.loc ℓ))))))
    .hole

/-- The context of the release. -/
def storeK₃ (v : Val) : Kont := .appR (.val (Val.lam (storeResE v 1))) .hole

theorem storeK₂_plain (v : Val) (ℓ : Loc) :
    (∀ n, (storeK₂ v ℓ).HasHnd n = false) ∧ (∀ n, (storeK₂ v ℓ).Catches n = false) :=
  ⟨fun n => by simp [storeK₂, Kont.HasHnd], fun n => by simp [storeK₂, Kont.Catches]⟩

theorem storeBody_steps (N : Expr) (hN : closedAt 0 N = true) (v κ : Val) :
    PureSteps (Expr.subst 0 (Val.pair v κ) (.letpair (.var 0) (storeBody N)))
      ((storeK₁ v N).plug (.app (.val (Val.prim .alloc)) (.val κ))) := by
  refine (PureSteps.head (fun μ => Head.letpair μ v κ _) rfl).trans ?_
  have e : ((Expr.subst 2 ((Val.pair v κ).shift 2 0) (storeBody N)).subst 0 (κ.shift 1 0)).subst
      0 v = (storeK₁ v N).plug (.app (.val (Val.prim .alloc)) (.val κ)) := by
    simp [storeBody, storeK₁, storeResE, Kont.plug, subst_shift_succ, Expr.subst, Val.val_shift,
      Expr.shift_shift, Expr.shift_zero, subst_closedAt N _ hN, BoLo.freeE]
  rw [e]
  exact .refl

theorem storeK₁_steps (N : Expr) (hN : closedAt 0 N = true) (v : Val) (ℓ : Loc) :
    PureSteps ((storeK₁ v N).plug (.val (Val.loc ℓ))) ((storeK₂ v ℓ).plug N) := by
  refine (PureSteps.beta _ _).trans ?_
  simp [storeK₂, storeResE, Kont.plug, subst_shift_succ, Expr.subst, Val.val_shift,
    subst_closedAt N _ hN, BoLo.freeE]
  exact .refl

theorem storeK₂_steps (v : Val) (ℓ : Loc) :
    PureSteps ((storeK₂ v ℓ).plug (.val .unit))
      ((storeK₃ v).plug (BoLo.freeE (.val (Val.loc ℓ)))) := by
  refine (PureSteps.beta _ _).trans ?_
  simp [storeK₃, storeResE, Kont.plug, subst_shift_succ, Expr.subst, Val.val_shift, BoLo.freeE]
  exact .refl

theorem storeK₃_steps (v κ : Val) :
    PureSteps ((storeK₃ v).plug (.val κ))
      (.app (.app (.val κ) (.val (Val.inj₁ .unit))) (.val v)) := by
  refine (PureSteps.beta _ _).trans ?_
  simp [storeResE, subst_shift_succ, Expr.subst, Val.val_shift, Expr.shift_zero]
  exact .refl

/-! ### The handler law -/

section
variable {δ : LSub} {Θ : LocTy} {c : Loc → Option Life} {S SN : Row} {fs : Nat → CTy}
  {n : UInt32} {A B R : VTy}

/-- **A handler at the storing clause, at the typed world**: the handled computation at the row of
`n.0 : B ↠^lin B` before `Σ`, the clause's work `N` closed and at `F_{Σ_N} 1` at every valid world,
`Σ_N ≤ Σ` of must-resume operations. -/
theorem erwp_handle_store (hΘ : Θ.OK) (hnS : ∀ o ∈ S, o.n ≠ n) (hSN : RowLe SN S)
    (hLin : ∀ o ∈ SN, o.q = .lin ∧ o.abort = false) {vr : Val} {Nw : Expr}
    (hNc : closedAt 0 Nw = true)
    (hNw : ∀ (Θ' : LocTy) (c' : Loc → Option Life) (k : Nat) (ls' : List SRec), Θ'.OK →
      cN (ℍ := ℍ) (CTy.effOf SN .unit) δ Θ' c' k ls' Nw PMap.empty)
    {N : Nat} (hVr : vN (ℍ := ℍ) (retTy S A R) δ Θ N vr PMap.empty) {lo : Life}
    {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : erwpK (ℍ := ℍ) KW.PostK (fun z => z.Θ.view z.c)
      (fun z => opTableK z.lo (tabN (ℍ := ℍ)
        (CTy.effOf (Row.ofEff n [(.lin, B, B)] 0 fs ++ S) A) δ z))
      (fun z k _ v ρ => vN (ℍ := ℍ) A δ z.Θ k v ρ) ⟨Θ, c, lo⟩ N ls e ρ)
    (hc : ConsistentX c ρ) :
    erwpK (ℍ := ℍ) KW.PostK (fun z => z.Θ.view z.c)
      (fun z => opTableK z.lo (tabN (ℍ := ℍ) (CTy.effOf S R) δ z))
      (fun z k _ v ρ => vN (ℍ := ℍ) R δ z.Θ k v ρ) ⟨Θ, c, lo⟩ N ls (hndE (storeH n vr Nw) e) ρ := by
  set E : List (Qual × VTy × VTy) := [(.lin, B, B)] with hE
  have hlen : E.length ≤ 2 ^ 32 := by simp [hE]
  set Tin : KW → OpTabK KW := fun z =>
    tabN (ℍ := ℍ) (CTy.effOf (Row.ofEff n E 0 fs ++ S) A) δ z with hTin
  set Tout : KW → OpTabK KW := fun z => tabN (ℍ := ℍ) (CTy.effOf S R) δ z with hTout
  have hQout : ∀ z : KW, PostN.Down (fun k _ v ρ => vN (ℍ := ℍ) R δ z.Θ k v ρ) :=
    fun z k _ v ρ h => vN_down _ δ z.Θ k v ρ h
  have hVt : ∀ x y z : KW, KW.PostK x y → KW.PostK y z → KW.PostK x z :=
    fun _ _ _ (h₁ : _ = _) (h₂ : _ = _) => h₂.trans h₁
  have h' := erwpK_postPA (ℍ := ℍ) (V := KW.PostK) (fl := fun z : KW => z.lo) (T := Tin)
    (c := fun z : KW => z.c) (I := fun z : KW => z.Θ.OK) (P := postOK)
    (fun x m i en hT y k ls w ρ hB => tabF_ansC δ _ x m i en (tabF_of_tabN hT) y k ls w ρ hB)
    (fun x m i en hT f y ρ hy _ => (tabN_wkC δ _ x m i en hT f y ρ hy).2.2.1)
    (fun x m i en hT f y ρ hy => (tabN_wkC δ _ x m i en hT f y ρ hy).2.1)
    (fun x m i en hT f _ y ρ hP hcx hx => by
      obtain ⟨o, -, rfl⟩ := tabF_rowOf_find (tabF_of_tabN hT)
      exact KW.owed_of_post hP.1 hx f hcx)
    (fun x y (h : y = x) => by rw [h]) (fun x y (h : y = x) hx => h ▸ hx) n N ⟨Θ, c, lo⟩ ls e ρ
    h hc hΘ
  refine erwpK_handle_leI (V := KW.PostK) (Φ := fun z : KW => z.Θ.view z.c)
    (Inv := fun z : KW => z.Θ.OK) (fl := fun z : KW => z.lo) hVt
    (fun z hz => LocTy.view_down hz.1 z.c) (fun x y (h : y = x) => by rw [h]) N
    (fun z => (Tin z).withPAP z.c z.Θ.OK (postOK z) n) Tout
    (fun x _ => OpTabK.withPAP_downAt ⟨(tabN_downI_OK _ δ x).pa, (tabN_downI_OK _ δ x).fin⟩)
    (fun x _ => opTableK_downI (tabN_downI_OK _ δ x))
    (fun x y (h : y = x) => by subst h; exact fun _ _ _ _ _ h => h)
    n (fun x m i hm => by rw [OpTabK.withPAP_ne _ hm]; exact tabN_ofEff_neK A R δ x hm)
    (qualsVal (E.map Prod.fst)) vr ⟨.pair (storeClause Nw).1 (.val .unit), .pair .lam .unit⟩
    _ _ hQout ?_ ?_ ?_ (fun _ => none) (fun _ _ _ _ _ _ _ h => by cases h) KW.postK_refl ?_
    (fun _ _ h => by cases h) ?_ ?_ N le_rfl ⟨Θ, c, lo⟩ hΘ ls e ρ h'
  · intro x i en hT _
    obtain ⟨en₀, hT₀, rfl⟩ := OpTabK.withPAP_self hT
    exact capTag_ofEffK hnS hlen i en₀ hT₀
  · intro x m i en hT ls₁ ls₂ ρ₁ ρ₂ ρ₀ hc₁ he
    obtain ⟨en₀, hT₀, -, -, -, -, hwc, -⟩ := OpTabK.withPAP_inv hT
    rw [hwc] at he ⊢
    exact tabF_wcl (tabF_of_tabN hT₀) hc₁ he
  · intro x i en hT _ f y ρ₁ ρ₂ ρ₀ hc₁ hv₁ hy
    obtain ⟨en₀, hT₀, rfl⟩ := OpTabK.withPAP_self hT
    exact hy.imp (tabF_wkLeft (rdN_ok δ) (tabF_of_tabN hT₀) hc₁ hv₁) id
  · intro x m i en hT _ f y ρ₁ hy
    obtain ⟨en₀, hT₀, -, -, -, -, -, -, hwk⟩ := OpTabK.withPAP_inv hT
    rcases hwk f y ρ₁ hy with hy' | hy'
    · exact (tabN_wkC δ _ x m i en₀ hT₀ f y ρ₁ hy').2.1
    · exact hy'.2
  · -- `[ret]`: `h_ret` at the value, at the world it is posted at
    rintro x k hk ls' v σ ⟨⟨hv, hcv⟩, hxOK⟩
    obtain ⟨-, hr⟩ := vN_extR (retTy S A R) δ N vr PMap.empty (LocTy.extR_empty Θ x.Θ) hVr
    exact (cN_effOf S R δ x.Θ x.c k ls' _ σ).mp (hr x.Θ (LocTy.extR_refl _ _) hxOK x.c
      (consistentX_empty _) ls' x.c k hk v σ σ (compS_empty_left σ) hv hcv) x.lo
  · intro x i en' hT
    obtain ⟨en, hT₀, rfl⟩ := OpTabK.withPAP_self hT
    obtain ⟨j, hj, hji, -, rfl⟩ := tabN_ofEff_selfK hnS hlen hT₀
    obtain rfl : j = 0 := by simp [hE] at hj; omega
    refine ⟨storeClause Nw, by rw [hji]; simp [clauseAt, show IsVal (storeClause Nw).1 from IsVal.lam], fun ha k hk ls' v κ σ hσ => ?_,
      fun ha => absurd ha (by simp [hE, RowRd.ent, OpEntK.withPAP])⟩
    obtain ⟨σa, σk, hck, ⟨hA', hcA, hxOK⟩, hu, f, hf, hκ⟩ := hσ
    cases k with
    | zero => exact erwpK_zero
    | succ k₀ =>
    refine erwpK_step (fun _ => opTableK_local _ _) (e' := Expr.subst 0 (Val.pair v κ) _)
      (fun μ => step1Only_plug (Head.beta μ _ (Val.pair v κ)) rfl .hole) ?_
    refine erwpK_flr_tabN (F := CTy.effOf S R) (δ := δ) f
      (Q := fun z k _ v ρ => vN (ℍ := ℍ) R δ z.Θ k v ρ) (fun _ _ _ _ _ h => h) k₀ x ls' _ σ ?_
    have hx'OK : (x.flr f).Θ.OK := hxOK
    have hΦ' : ((x.flr f).Θ.view (x.flr f).c).Down := LocTy.view_down hxOK.1 x.c
    have hTd' : (opTableK (x.flr f).lo (Tout (x.flr f))).Down :=
      opTableK_downI (tabN_downI_OK _ δ _)
    refine erwpK_pureSteps (Φ := fun z : KW => z.Θ.view z.c) (x := x.flr f) hΦ' hTd' hQout
      (storeBody_steps Nw hNc v κ) ?_
    refine erwpK_allocV (Φ := fun z : KW => z.Θ.view z.c) (x := x.flr f)
      (fun _ => opTableK_local _ _) hΦ' (storeK₁ v Nw) κ
      (fun ℓ σ₁ σ₂ hp hcs hv₂ => ?_)
    refine erwpK_pureSteps (Φ := fun z : KW => z.Θ.view z.c) (x := x.flr f) hΦ' hTd' hQout
      (storeK₁_steps Nw hNc v ℓ) ?_
    -- `N`'s run at `Σ_N`, from the empty resource, consistent with the view
    have hy := hNw x.Θ x.c (k₀ - 1) ls' hxOK
    have hy' := (cN_effOf SN .unit δ x.Θ x.c (k₀ - 1) ls' _ PMap.empty).mp hy (x.flr f).lo
    have hy'' := erwpK_consistentAns (c := fun z : KW => z.c)
      (fun x m i en hT y k ls w ρ hB => tabF_ansC δ _ x m i en (tabF_of_tabN hT) y k ls w ρ hB)
      (fun x m i en hT f y ρ hy _ => (tabN_wkC δ _ x m i en hT f y ρ hy).2.2.1)
      (fun x y (h : y = x) => by rw [h]) (k₀ - 1) (k₀ - 1) le_rfl (x.flr f) ls' _ PMap.empty hy'
      (consistentX_empty _)
    -- the frame: the cell, the payload at the world reached, and `κ`'s relation
    set en₁ := ((rdN (ℍ := ℍ) δ).ent () n E[0].1 E[0].2.1 E[0].2.2
      (finF (ℍ := ℍ) (rdN (ℍ := ℍ) δ) () (fs 0)) x).withPAP x.c x.Θ.OK (postOK x) with hen₁
    set KR : List SRec → WProp := fun ls₁ τ =>
      ∀ y', en₁.wk f y' τ → ∀ ls₂, en₁.wc ls₁ ls₂ τ → ∀ k', k' < k₀ + 1 →
        (∀ w : Val, (en₁.PB y' k' ls₂ w ─⋆ erwpK (ℍ := ℍ) KW.PostK (fun z => z.Θ.view z.c)
          (fun z => opTableK z.lo (Tout z)) (fun z k _ v ρ => vN (ℍ := ℍ) R δ z.Θ k v ρ) y' k'
          ls₂ (.app (.app κ.1 (.val (Val.inj₁ .unit))) (.val w))) τ) ∧
        (en₁.q ≠ .lin → ∀ Tk, (none : Option (KW → OpTabK KW)) = some Tk →
          erwpK (ℍ := ℍ) KW.PostK (fun z => z.Θ.view z.c) (fun z => opTableK z.lo (Tk z))
            (fun _ => unitPost) y' k' ls₂ (.app κ.1 (.val (Val.inj₂ .unit))) τ) with hKR
    set Fr : KW → List SRec → WProp := fun y ls₁ τ => ∃ τak τc τa τk : WRes,
      ResU.CompS τak τc τ ∧ ptoOwn ℓ κ τc ∧ ResU.CompS τa τk τak ∧ y.lo ≤ f ∧
        (vN (ℍ := ℍ) B δ y.Θ k₀ v τa ∧ ConsistentX y.c τa) ∧ en₁.wk f y τk ∧ KR ls₁ τk with hFr
    have hFext : ∀ y ls₁ ls₂ τ, extF ls₁ ls₂ τ → Fr y ls₁ τ → Fr y ls₂ τ := by
      rintro y ls₁ ls₂ τ he ⟨τak, τc, τa, τk, h₁, h₂, h₃, hlo, hp, hwk, hk'⟩
      have heK : extF ls₁ ls₂ τk := extF_right h₃ (extF_left ls₁ ls₂ τak τc τ h₁ he)
      exact ⟨τak, τc, τa, τk, h₁, h₂, h₃, hlo, hp, hwk,
        fun y' hy' ls₃ he' => hk' y' hy' ls₃ (extF_trans heK he')⟩
    refine erwpK_frame_plain_orI (V := KW.PostK) (Φ := fun z : KW => z.Θ.view z.c)
      (Inv := fun z : KW => z.Θ.OK) (fl := fun z : KW => z.lo) hVt
      (fun z hz => LocTy.view_down hz.1 z.c) (fun x y (h : y = x) => by rw [h])
      (fun x y (h : y = x) hx => h ▸ hx)
      (T := fun z => tabN (ℍ := ℍ) (CTy.effOf SN .unit) δ z) (T' := Tout)
      (fun z => by
        have h := tabF_le_of_rowLe (ℍ := ℍ) (rdN (ℍ := ℍ) δ) hSN () .unit R z
        rw [← tabN_eq, ← tabN_eq] at h; exact h)
      (fun x y (h : y = x) => by subst h; exact fun _ _ _ _ _ h => h)
      (storeK₂ v ℓ) (storeK₂_plain v ℓ).1 (storeK₂_plain v ℓ).2 Fr
      (fun _ ls₁ ls₂ hs τ hF => hFext _ ls₁ ls₂ τ (extF_of_same hs τ) hF)
      (fun x y (h : y = x) _ _ hF => h ▸ hF)
      (fun x m i en hT f y ρ hy => (tabN_wkC δ _ x m i en hT f y ρ hy).2.1)
      (fun x m i en hT ls₁ ls₂ ρ₁ σ₁ ρ₁' hc₁ he₁ => tabF_wcl (tabF_of_tabN hT) hc₁ he₁)
      (fun x m i en hT f y ρ₁ σ₁ ρ₁' hc₁ hv₁ hy =>
        tabF_wkLeft (rdN_ok δ) (tabF_of_tabN hT) hc₁ hv₁ hy)
      (fun x m i en hT ls₁ ls₂ ρ₁ σ₁ ρ₁' hc₁ he₁ hF => by
        obtain ⟨o, -, rfl⟩ := tabF_rowOf_find (tabF_of_tabN hT)
        exact hFext x ls₁ ls₂ σ₁ (extF_right hc₁ he₁) hF)
      ?_ (fun _ m i en₂ hT₂ ha₂ => absurd ha₂ (by simp [(lin_condsK hLin hT₂).2]))
      (fun _ m i en₂ hT₂ hq₂ => absurd hq₂ (by simp [(lin_condsK hLin hT₂).1]))
      (fun _ m i en₂ hT₂ _ hq₂ => absurd (lin_condsK hLin hT₂).1 hq₂)
      _ _ ?_ (k₀ - 1) (x.flr f) hx'OK ls' _ PMap.empty hy'' σ₂ σ₂
      ⟨σ, σ₁, σa, σk, hcs, hp, hck, min_le_right _ _,
        ⟨vN_le (by omega) hA', hcA⟩, Or.inr ⟨⟨rfl, rfl, min_le_left _ _⟩, hxOK⟩, hκ⟩
      (compS_empty_left σ₂)
    · -- the frame across a stop of `N`, at a floor no higher than `f`
      rintro x₁ m i en₂ hT₂ f₁ hf₁ y ls₁ ρ₁ τ ρ₁' hc₁ hv₁ hy
        ⟨τak, τc, τa, τk, h₁, h₂, h₃, hlo, ⟨hpv, hpc⟩, hwk, hk'⟩
      have hy₁ : x₁.Owed f₁ y ρ₁' := tabN_wkC δ _ x₁ m i en₂ hT₂ f₁ y ρ₁' hy
      have hvτ : τ.Valid := (ResU.Valid.split hc₁ hv₁).2
      have hyτ : x₁.Owed f y τ :=
        (hy₁.left (ResU.CompS.comm hc₁) hv₁).floor_le (le_trans hf₁ hlo)
      have hvak : τak.Valid := (ResU.Valid.split h₁ hvτ).1
      have hyak : x₁.Owed f y τak := hyτ.left h₁ hvτ
      have hya : x₁.Owed f y τa := hyak.left h₃ hvak
      have hyk : x₁.Owed f y τk := hyak.left (ResU.CompS.comm h₃) hvak
      refine ⟨τak, τc, τa, τk, h₁, h₂, h₃, le_trans hy₁.2.2.2.1 hlo,
        ⟨vN_extR B δ k₀ v τa hya.1.1 hpv, hya.2.2.1⟩, Or.inl ?_, hk'⟩
      rcases hwk with hw | ⟨hpost, -⟩
      · exact KW.Owed.trans hw hyk
      · exact KW.Owed.of_post hpost hyk
    · -- `N`'s value: the cell is freed and `κ` resumed with the payload
      rintro y hyOK k' ls₁ w τ ⟨τ₁, τ₂, hcτ, ⟨hk'', ⟨rfl, rfl⟩, -, -⟩,
        ⟨τak, τc, τa, τk, h₁, h₂, h₃, -, ⟨hpv, hpc⟩, hwk, hk'⟩⟩
      have hτ : τ = τ₂ := eq_of_compS_empty_left hcτ
      subst hτ
      have hΦy : (y.Θ.view y.c).Down := LocTy.view_down hyOK.1 y.c
      have hTdy : (opTableK y.lo (Tout y)).Down := opTableK_downI (tabN_downI_OK _ δ _)
      refine erwpK_pureSteps (Φ := fun z : KW => z.Θ.view z.c) (x := y) hΦy hTdy hQout
        (storeK₂_steps v ℓ) ?_
      refine erwpK_free (Φ := fun z : KW => z.Θ.view z.c) (x := y)
        (fun _ => opTableK_local _ _) hΦy (storeK₃ v) ℓ κ
        ⟨τc, τak, ResU.CompS.comm h₁, h₂, ?_⟩
      refine erwpK_pureSteps (Φ := fun z : KW => z.Θ.view z.c) (x := y) hΦy hTdy hQout
        (storeK₃_steps v κ) ?_
      exact (hk' y hwk ls₁ (extF_refl ls₁ τk) (k' - 1) (by omega)).1 v τa τak
        ⟨vN_le (by omega) hpv, hpc⟩ (ResU.CompS.comm h₃)

end

#print axioms erwp_handle_store

/-! ### At `SemJN` -/

theorem storeClause_closed {N : Expr} (hN : closedAt 0 N = true) :
    closedAt 0 (storeClause N).1 = true := by
  have h4 : closedAt 4 N = true := closedAt_mono N hN (by omega)
  simp [storeClause, storeBody, closedAt, h4, BoLo.freeE, Val.inj₁, Val.unit]

namespace Goal791N

/-- **`[handle]` at the storing clause, at `SemJN`**: the return clause `Hr` a value form at its
type, the clause's work `N` closed and at `F_{Σ_N} 1`, `Σ_N ≤ Σ` of must-resume operations, the
handled computation at the row of `n.0 : B ↠^lin B` before `Σ`. As `handleT_compatN`, the return
clause is read off its run at the run's start (`erwp_val_post`) and the handler is
`erwp_handle_store`. -/
theorem handleStore_compatN {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {Hr Nw e : Expr} {S SN : Row}
    {fs : Nat → CTy} {n : UInt32} {A B R : VTy}
    (hsp : Ctx.SplitP Γ Γ₁ Γ₂) (hd : Ctx.DeadP Γ₁) (hHr : Hr.ValFormIn Γ₁)
    (hr : SemJN (ℍ := ℍ) Δ Γ₁ Hr (.val (retTy S A R)))
    (hnS : ∀ o ∈ S, o.n ≠ n) (hSN : RowLe SN S) (hLin : ∀ o ∈ SN, o.q = .lin ∧ o.abort = false)
    (hNc : closedAt 0 Nw = true) (hN : SemJN (ℍ := ℍ) Δ [] Nw (.comp (CTy.effOf SN .unit)))
    (he : SemJN (ℍ := ℍ) Δ Γ₂ e (.comp (CTy.effOf (Row.ofEff n [(.lin, B, B)] 0 fs ++ S) A))) :
    SemJN (ℍ := ℍ) Δ Γ (hndExpr n [.lin] (.pair Hr (.pair (storeClause Nw).1 (.val .unit))) e)
      (.comp (CTy.effOf S R)) := by
  intro δ γ Θ c N ls ρ hδ hΘ hcρ hlw hg
  refine (cN_effOf S R δ Θ c N ls _ ρ).mpr fun lo => erwpK_of_valid fun hv => ?_
  obtain ⟨ρ₁, ρ₂, hc12, hg₁, hg₂, -, hc₂⟩ := gN_splitC hsp hg hcρ hv
  obtain ⟨hlw₁, hlw₂⟩ := hsp.liveWithin hlw
  have hρ₁ : ρ₁ = PMap.empty := gN_deadP hd hg₁
  subst hρ₁
  rw [eq_of_compS_empty_left hc12]
  have hval : IsVal (substAll γ Hr) := isVal_psub_valFormIn hlw₁ hHr
  have hH' : erwp (ℍ := ℍ) (Θ.view c) (opTableN OpTabN.empty)
      (fun k _ v ρ => vN (ℍ := ℍ) (retTy S A R) δ Θ k v ρ) N ls
      (⟨substAll γ Hr, hval⟩ : Val).1 PMap.empty :=
    erwp_of_cN_ret (hr δ γ Θ c N ls PMap.empty hδ hΘ (consistentX_empty c) hlw₁ hg₁)
  have hE' := (cN_effOf _ A δ Θ c N ls _ ρ₂).mp (he δ γ Θ c N ls ρ₂ hδ hΘ hc₂ hlw₂ hg₂) lo
  have hNw : ∀ (Θ' : LocTy) (c' : Loc → Option Life) (k : Nat) (ls' : List SRec), Θ'.OK →
      cN (ℍ := ℍ) (CTy.effOf SN .unit) δ Θ' c' k ls' Nw PMap.empty := by
    intro Θ' c' k ls' hΘ'
    have h := hN δ [] Θ' c' k ls' PMap.empty hδ hΘ' (consistentX_empty c') trivial rfl
    rwa [substAll, psub_closedAt Nw [] hNc le_rfl] at h
  show erwpK (ℍ := ℍ) _ _ _ _ _ N ls
    (Expr.psub 0 γ (hndExpr n [.lin] (.pair Hr (.pair (storeClause Nw).1 (.val .unit))) e)) ρ₂
  rw [psub_hndExpr]
  simp only [Expr.psub]
  rw [show Expr.psub 0 γ (storeClause Nw).1 = (storeClause Nw).1 from
    psub_closedAt _ γ (storeClause_closed hNc) le_rfl]
  rw [erwpK_eq]
  intro ρf fρ ps μ hf hcf hT htg hI hl hfd j μ' e' hj hrun hfin
  obtain ⟨ls', ρ', -, hVr⟩ := erwp_val_post (by omega) hH'
    (ResU.hash_empty_right (hash_valid_comp hf hcf)) (ResU.comp_empty_right fρ) hT htg hI hl hfd
  have hσ : ρ' = PMap.empty := vN_empty_of_persistent _ (retTy_persistent S A R) hVr
  subst hσ
  have hH := erwp_handle_store (fs := fs) hΘ hnS hSN hLin hNc hNw hVr hE' hc₂
  rw [erwpK_eq] at hH
  exact hH ρf fρ ps μ hf hcf hT htg hI hl hfd j μ' e' hj hrun hfin

#print axioms handleStore_compatN

end Goal791N

#print axioms storeBody_steps
#print axioms storeK₃_steps

end BoCa.Fig16.LogRel.Core.Chain.SI
