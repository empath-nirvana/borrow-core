import Core.Chain.FundamentalKW835N
import Core.EffCancelTyped

/-!
# `HandlerLawN`, the named assertion for the three handler rules  `[spec §62]`

`FundamentalN` is proved at every `CDerives` derivation from `MissingN` (`fundamentalN_all`):
every rule but `[handle]` at a value form (`effHandleV`), BOXED-κ `[handle]` (`effHandleVB`) and
`reify` has a compatibility lemma at `cN`, the relation at `KW`. `HandlerLawN` names those three as
one hypothesis, a `Prop` and not an axiom, in the form of `PinLaw` (`Core/PinLaw.lean`): three
fields, each stated as its `*_compatN` would be, over `SemJN` premises only, at every row,
qualifier, handler and handled computation. It carries no restriction to a scheduler or to a class
of clauses.

**What it asserts.** `handleV` (`HandleVN`, Core's `handleV_compatC`): a handler whose clauses
are in the relation at `clausesTy`, over a handled computation in the relation at the handled row,
is in the relation at the outer row. `handleVB` (`HandleVBN`, Core's `handleV_compatCB`): the same
at `clausesTyB`, `κ` boxed at `@d`, with the context and the row's answers outliving `@d`. `reify`
(`ReifyN`, Core's `reify_compatX`): `reify_res` at a residual in the relation is in the relation at
`reifyTy`.

**Why it is believed.** Core proves all three on its own relation (`handleV_compatC`,
`handleV_compatCB`, `reify_compatX`, `Core/Fundamental.lean`), and `PinLaw` already rests on the
same belief: a borrow held across a suspension is sound under a handler written in the program.
The step `cN` does not give is the one `docs/new-core/assert-boundary.md` §2.2 names: a clause
that keeps `κ` hands it to `vN`'s `U` clause, which reads `KW.OwedR`, where the stop owes it along
`KW.Owed` at the floor the stop chose. `reify` reads its loop through the same `U` clause.

**Not refuted.** The configurations in the tree that touch this step are pointwise over a `κ`, a
world or a share (`docs/new-core/configurations.md`); `HandlerLawN` quantifies over `SemJN` of
typed terms only. Those at a `κ` use the thunk `κ = ()`, which no `[op]` step hands a clause
(`kappa_ne_unit`, `kappaC_ne_unit`): its resumption is final (`unit_resume_final`), where the
resumption of every `κ` the step does hand takes a step (`kappa_resume_not_final`,
`kappaC_resume_not_final`).

**`slice_copy_mut`.** A fourth field, `sliceCopy` (`SliceCopyN`, Core's `sliceCopyM_compatX`), is
not a handler rule: the chain has no compatibility lemma at `slice_copy_mut` (`[spec §74]`) yet, and
the field states it as that lemma would be. Core proves it on its own relation.

**Not vacuous.**
* `handle_resume_inst`: the conclusion shared by `HandleVN` and `HandleVBN` holds at the handler
  `resumeH` (`h_ret = λx. x`, one unrestricted clause `λ(x, κ). (λk'. k'.1 x) κ` that receives
  `κ` and resumes it) over every handled computation at the handled row, at every outer row; proved
  at `erwpK` through `erwpK_handle_leI`, the clause resuming `κ` at the world the handled stop
  posted it at, from the floor that stop chose. So `handleVN_at_resumeH` and
  `handleVBN_at_resumeH` are the two conjuncts at that handler.
* `handleVN_resume_premises`, `handleVBN_resume_premises`: every premise of each conjunct holds at
  that handler over `perform (1, (0, ()))`, the clauses in the relation by their derivations'
  compatibility lemmas.
* `reifyN_premises_inst`: every premise of `ReifyN` holds at the residual `λx. x`. No instance of
  `ReifyN`'s conclusion is proved.
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
open BoCa.BoLo (Heap Head Kont hndE hndVal clauseAt capTag kappa kappaC performE)
open BoCa.Fig16.LogRel.Core.CancelIntercept (idV resumeCT)

/-- **HandlerLawN**: the named assumption for the three handler rules with no compatibility lemma
at `cN`, and for `slice_copy_mut`, each stated over `SemJN` premises only. -/
structure HandlerLawN : Prop where
  /-- `[handle]` at a value form is in the relation (`effHandleV`). -/
  handleV : HandleVN (ℍ := ℍ)
  /-- BOXED-κ `[handle]` is in the relation (`effHandleVB`). -/
  handleVB : HandleVBN (ℍ := ℍ)
  /-- `reify_res` is in the relation (`reify`). -/
  reify : ReifyN (ℍ := ℍ)
  /-- `slice_copy_mut` is in the relation (`sliceCopyM`): not a handler rule, and not a belief
  about one; the chain has no compatibility lemma at it yet.  `[spec §74]` -/
  sliceCopy : SliceCopyN (ℍ := ℍ)

/-- `HandlerLawN` says what `MissingN` says. -/
theorem handlerLawN_iff : HandlerLawN (ℍ := ℍ) ↔ MissingN (ℍ := ℍ) :=
  ⟨fun h => ⟨h.handleV, h.handleVB, h.reify, h.sliceCopy⟩, fun ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩⟩

/-- **`FundamentalN` from `HandlerLawN`.** -/
theorem fundamentalN_of_handlerLaw (h : HandlerLawN (ℍ := ℍ)) : FundamentalN (ℍ := ℍ) :=
  fundamentalN_of (handlerLawN_iff.mp h)

/-! ### The continuation a clause is handed

The `[op]` step hands a clause `kappa H K` (an unrestricted operation) or, after the cell's
allocation, `kappaC b ℓ H K` (must-resume or cancellable). Neither is `()`, and the resumption of
each takes a `β` step in every context at every memory, where the resumption of `()` is final. -/

theorem kappa_ne_unit (H : Val) (K : Kont) : kappa H K ≠ Val.unit.1 := by
  unfold kappa; simp [Val.unit]

theorem kappaC_ne_unit (b : Bool) (l : Loc) (H : Val) (K : Kont) :
    kappaC b l H K ≠ Val.unit.1 := by
  unfold kappaC; simp [Val.unit]

/-- The resumption of `κ = ()` is final in every context. -/
theorem unit_resume_final (K : Kont) (μ : Heap) :
    Final (ℍ := ℍ) μ (K.plug (.app Val.unit.1 (.val (Val.inj₁ .unit)))) :=
  fun _ _ hs => stuck_no_step (stuckAt_unit_app (Val.inj₁ Val.unit)) K hs

/-- The resumption of `kappa H K₀` is not final in any context. -/
theorem kappa_resume_not_final (H : Val) (K₀ K : Kont) (μ : Heap) :
    ¬ Final (ℍ := ℍ) μ (K.plug (.app (kappa H K₀) (.val (Val.inj₁ .unit)))) :=
  fun h => h _ _ (step1Only_plug (Head.beta μ _ (Val.inj₁ Val.unit)) rfl K).1

/-- The resumption of `kappaC b ℓ H K₀` is not final in any context. -/
theorem kappaC_resume_not_final (b : Bool) (l : Loc) (H : Val) (K₀ K : Kont) (μ : Heap) :
    ¬ Final (ℍ := ℍ) μ (K.plug (.app (kappaC b l H K₀) (.val (Val.inj₁ .unit)))) :=
  fun h => h _ _ (step1Only_plug (Head.beta μ _ (Val.inj₁ Val.unit)) rfl K).1

/-! ### `HandleVN` and `HandleVBN` at a handler whose clause receives `κ` -/

/-- The handler of the instances: `h_ret = λx. x` and one clause `λ(x, κ). (λk'. k'.1 x) κ`,
which resumes `κ` once at the operation's argument. -/
def resumeH : Expr := .pair (.val idV) (.pair (.val resumeCT) (.val Val.unit))

/-- The effect of the instances: one unrestricted operation `1 ↠ 1`. -/
abbrev resumeE : List (Qual × VTy × VTy) := [(.unr, .unit, .unit)]

theorem resumeH_closed : closedAt 0 resumeH = true := rfl

/-- The clause's body at `((), κ)` reaches the resumption of `κ` at `()`. -/
theorem resumeCT_body_steps (κ : Val) :
    PureSteps (ℍ := ℍ)
      (Expr.subst 0 (Val.pair Val.unit κ) (.letpair (.var 0) (.app (.val (Val.lam (.app (.app
        (.var 0) (.val (Val.inj₁ Val.unit))) (.var 2)))) (.var 0))))
      (.app (.app κ.1 (.val (Val.inj₁ .unit))) (.val Val.unit)) := by
  refine (PureSteps.head (fun μ => Head.letpair μ Val.unit κ _) rfl).trans ?_
  simp [Expr.subst, Expr.val, Val.lam, Val.inj₁, Val.unit, Val.pair, Val.shift, Expr.shift,
    CancelIntercept.subst_shift_one]
  refine (PureSteps.head
    (fun μ => Head.beta μ (((Expr.var 0).app Expr.unit.inj₁).app Expr.unit) κ) rfl).trans ?_
  simp [Expr.subst]
  exact .refl

/-- **The handled run at the resuming handler**, for every computation `e` at the handled row, its
context beside a consumed one. The handled run is pre-passed (`erwpK_postPA`), so a stop at the
handler's name records that its world is valid and owes `κ` also at its own location typing and
view at a floor no higher (`postOK`). The clause pays its `β` step, moves to the floor `f` the
stop chose (`erwpK_flr_tabN`), and resumes `κ` at `()` there. -/
theorem handle_resume_inst {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {e : Expr} {S : Row}
    {fs : Nat → CTy} {n : UInt32} (hsp : Ctx.SplitP Γ Γ₁ Γ₂) (hd : Ctx.DeadP Γ₁)
    (hnS : ∀ o ∈ S, o.n ≠ n)
    (he : SemJN (ℍ := ℍ) Δ Γ₂ e (.comp (CTy.effOf (Row.ofEff n resumeE 0 fs ++ S) .unit))) :
    SemJN (ℍ := ℍ) Δ Γ (hndExpr n (resumeE.map Prod.fst) resumeH e)
      (.comp (CTy.effOf S .unit)) := by
  intro δ γ Θ c N ls ρ hδ hΘ hcρ hlw hg
  refine (cN_effOf S .unit δ Θ c N ls _ ρ).mpr fun lo => erwpK_of_valid fun hv => ?_
  obtain ⟨ρ₁, ρ₂, hc12, hg₁, hg₂, -, hc₂⟩ := gN_splitC hsp hg hcρ hv
  obtain ⟨-, hlw₂⟩ := hsp.liveWithin hlw
  obtain rfl : ρ₁ = PMap.empty := gN_deadP hd hg₁
  rw [eq_of_compS_empty_left hc12]
  have hE' := (cN_effOf _ .unit δ Θ c N ls _ ρ₂).mp
    (he δ γ Θ c N ls ρ₂ hδ hΘ hc₂ hlw₂ hg₂) lo
  show erwpK (ℍ := ℍ) _ _ _ _ _ N ls (Expr.psub 0 γ (hndExpr n _ resumeH e)) ρ₂
  rw [psub_hndExpr, psub_closedAt resumeH γ resumeH_closed le_rfl]
  set Tin : KW → OpTabK KW := fun z =>
    tabN (ℍ := ℍ) (CTy.effOf (Row.ofEff n resumeE 0 fs ++ S) .unit) δ z with hTin
  set Tout : KW → OpTabK KW := fun z => tabN (ℍ := ℍ) (CTy.effOf S .unit) δ z with hTout
  have hQout : ∀ z : KW, PostN.Down (fun k _ v ρ => vN (ℍ := ℍ) .unit δ z.Θ k v ρ) :=
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
    (fun x y (h : y = x) => by rw [h]) (fun x y (h : y = x) hx => h ▸ hx) n N ⟨Θ, c, lo⟩ ls _
    ρ₂ hE' hc₂ hΘ
  refine erwpK_handle_leI (V := KW.PostK) (Φ := fun z : KW => z.Θ.view z.c)
    (Inv := fun z : KW => z.Θ.OK) (fl := fun z : KW => z.lo) hVt
    (fun z hz => LocTy.view_down hz.1 z.c) (fun x y (h : y = x) => by rw [h]) N
    (fun z => (Tin z).withPAP z.c z.Θ.OK (postOK z) n) Tout
    (fun x _ => OpTabK.withPAP_downAt ⟨(tabN_downI_OK _ δ x).pa, (tabN_downI_OK _ δ x).fin⟩)
    (fun x _ => opTableK_downI (tabN_downI_OK _ δ x))
    (fun x y (h : y = x) => by subst h; exact fun _ _ _ _ _ h => h)
    n (fun x m i hm => by rw [OpTabK.withPAP_ne _ hm]; exact tabN_ofEff_neK .unit .unit δ x hm)
    (qualsVal (resumeE.map Prod.fst)) idV (Val.pair resumeCT Val.unit) _ _ hQout
    ?_ ?_ ?_ (fun _ => none) (fun _ _ _ _ _ _ _ h => by cases h) KW.postK_refl ?_
    (fun _ _ h => by cases h) ?_ ?_ N le_rfl ⟨Θ, c, lo⟩ hΘ ls _ ρ₂ h'
  · intro x i en hT _
    obtain ⟨en₀, hT₀, rfl⟩ := OpTabK.withPAP_self hT
    exact capTag_ofEffK hnS (by simp) i en₀ hT₀
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
  · -- `[ret]`: `λx. x` at the value, at the world it is posted at
    rintro x k _ ls' v σ ⟨⟨hv, -⟩, hxOK⟩
    refine erwpK_det (Φ := fun z : KW => z.Θ.view z.c) (x := x) (LocTy.view_down hxOK.1 x.c)
      (opTableK_downI (tabN_downI_OK _ δ _)) hQout
      (fun μ => step1Only_plug (Head.beta μ (.var 0) v) rfl .hole) ?_
    exact erwpK_val (KW.postK_refl x) hv
  · intro x i en' hT
    obtain ⟨en, hT₀, rfl⟩ := OpTabK.withPAP_self hT
    obtain ⟨j, hj, hji, -, rfl⟩ := tabN_ofEff_selfK hnS (by simp) hT₀
    obtain rfl : j = 0 := by simp at hj; omega
    refine ⟨resumeCT, by rw [hji]; simp [clauseAt, Val.pair]; exact resumeCT.2, ?_, ?_⟩
    · intro _ k _ ls' v κ σ hσ
      obtain ⟨σa, σk, hck, ⟨⟨rfl, rfl⟩, -, hxOK⟩, -, f, -, hκ⟩ := hσ
      obtain rfl := eq_of_compS_empty_left hck
      cases k with
      | zero => exact erwpK_zero
      | succ k₀ =>
      refine erwpK_step (fun _ => opTableK_local _ _)
        (fun μ => step1Only_plug (Head.beta μ _ (Val.pair Val.unit κ)) rfl .hole) ?_
      refine erwpK_flr_tabN (F := CTy.effOf S .unit) (δ := δ) f
        (Q := fun z k _ v ρ => vN (ℍ := ℍ) .unit δ z.Θ k v ρ) (fun _ _ _ _ _ h => h) k₀ x ls' _ _ ?_
      refine erwpK_pureSteps (Φ := fun z : KW => z.Θ.view z.c) (x := x.flr f)
        (LocTy.view_down hxOK.1 x.c) (opTableK_downI (tabN_downI_OK _ δ _)) hQout
        (resumeCT_body_steps κ) ?_
      exact (hκ (x.flr f) (Or.inr ⟨⟨rfl, rfl, min_le_left _ _⟩, hxOK⟩) ls' (extF_refl ls' _) k₀
        (by omega)).1 Val.unit PMap.empty _ ⟨⟨rfl, rfl⟩, consistentX_empty _⟩
        (ResU.CompS.comm (compS_empty_left _))
    · intro ha
      simp [RowRd.ent, OpEntK.withPAP, VTy.isZero] at ha

/-! ### The handler's premises at the instance -/

/-- `λx. x : !U(A ⊸ F_Σ A)` at `SemJN`: `d_idV`'s derivation, each rule its chain lemma. -/
theorem semJN_idV {Δ : LifeCtx} (S : Row) (A : VTy) :
    SemJN (ℍ := ℍ) Δ [] (.val idV) (.val (retTy S A A)) :=
  bangThunkV_compatN (dead_noLive .nil) rfl
    (lam_compatN (sub_compatN (RowLe.nil S) (ret_compatN (var_compatN (.here Ctx.Dead.nil.toP)))))

/-- The clause `λ(x, κ). (λk'. k'.1 x) κ` at `clauseTy Σ R (unr, 1, 1) F` at `SemJN`:
`d_resumeCT`'s derivation, each rule its chain lemma. -/
theorem semJN_resumeCT {Δ : LifeCtx} (S : Row) (R : VTy) (F : CTy) :
    SemJN (ℍ := ℍ) Δ [] (.val resumeCT) (.val (clauseTy S R (.unr, .unit, .unit) F)) := by
  show SemJN (ℍ := ℍ) Δ [] (.val resumeCT)
    (.val (.bang (.thunk (.arr (.tensor .unit (kTy S R .unr .unit F)) (CTy.effOf S R)))))
  refine bangThunkV_compatN (dead_noLive .nil) rfl (lam_compatN ?_)
  refine tensorE_compatN (.left .nil) (var_compatN (.here .nil)) ?_
  refine bind_compatN (A := .thunk (.amp (.arr .unit (CTy.effOf S R)) (cancelTy S F)))
    (.left (.right (.dead .nil))) (ret_compatN (bangE_compatN (var_compatN
      (.here (.cons (.cons .nil)))))) ?_
  exact app_compatN (.left (.dead (.right (.dead .nil))))
    (proj₁_compatN (force_compatN (T := .thunk _) (C := .amp (.arr .unit (CTy.effOf S R))
      (cancelTy S F)) (.here (.cons (.cons (.cons .nil)))) rfl))
    (.there (.there (.here (.cons .nil))))

/-- The handled computation of the instance: `perform (1, (0, ()))`. -/
def performOne : Expr := performE (opArgE 1 0 (.val Val.unit))

/-- The handled row of the instance: the operation `1 ↠^unr 1` at the name `1`. -/
abbrev resumeRow : Row := Row.ofEff 1 resumeE 0 finsNil ++ []

/-- **Every premise of `HandleVN` holds at the instance**: the handler `resumeH`, whose one
clause receives `κ`, at `SemJN`, over `perform (1, (0, ()))` at `SemJN`; and the conclusion holds
there. -/
theorem handleVN_resume_premises {Δ : LifeCtx} :
    Ctx.SplitP [] [] [] ∧ Ctx.DeadP ([] : Ctx VTy) ∧ resumeH.ValFormIn [] ∧
    SemJN (ℍ := ℍ) Δ [] resumeH
      (.val (.tensor (retTy [] .unit .unit) (clausesTy [] .unit resumeE finsNil))) ∧
    (1 : UInt32) ≠ 0 ∧ (∀ o ∈ ([] : Row), o.n ≠ 1) ∧ resumeE.length ≤ 2 ^ 32 ∧
    Row.divB resumeRow = false ∧
    SemJN (ℍ := ℍ) Δ [] performOne (.comp (CTy.effOf resumeRow .unit)) ∧
    SemJN (ℍ := ℍ) Δ [] (hndExpr 1 (resumeE.map Prod.fst) resumeH performOne)
      (.comp (CTy.effOf [] .unit)) := by
  have hP : SemJN (ℍ := ℍ) Δ [] performOne (.comp (CTy.effOf resumeRow .unit)) :=
    perform_compatN (S := resumeRow) (o := ⟨1, 0, .unr, .unit, .unit, finsNil 0, rcsNil 0⟩)
      rfl rfl (unitI_compatN .nil)
  exact ⟨.nil, .nil, .pair (.val _) (.pair (.val _) (.val _)),
    tensorI_compatN .nil (semJN_idV [] .unit)
      (tensorI_compatN .nil (semJN_resumeCT [] .unit _) (unitI_compatN .nil)),
    by decide, by simp, by simp, rfl, hP, handle_resume_inst .nil .nil (by simp) hP⟩

/-- The clause `λ(x, κ). (λk'. k'.1 x) κ` at the boxed clause type
`clauseTyB Σ R d (unr, 1, 1) F`: `semJN_resumeCT` with `κ` unboxed (`boxE_compatN`) before `!`
is read off it. -/
theorem semJN_resumeCTB {Δ : LifeCtx} (S : Row) (R : VTy) (d : Lifetime.Life) (F : CTy) :
    SemJN (ℍ := ℍ) Δ [] (.val resumeCT) (.val (clauseTyB S R d (.unr, .unit, .unit) F)) := by
  show SemJN (ℍ := ℍ) Δ [] (.val resumeCT)
    (.val (.bang (.thunk (.arr (.tensor .unit (.box d (kTy S R .unr .unit F))) (CTy.effOf S R)))))
  refine bangThunkV_compatN (dead_noLive .nil) rfl (lam_compatN ?_)
  refine tensorE_compatN (.left .nil) (var_compatN (.here .nil)) ?_
  refine bind_compatN (A := .thunk (.amp (.arr .unit (CTy.effOf S R)) (cancelTy S F)))
    (.left (.right (.dead .nil))) (ret_compatN (bangE_compatN (boxE_compatN (var_compatN
      (.here (.cons (.cons .nil))))))) ?_
  exact app_compatN (.left (.dead (.right (.dead .nil))))
    (proj₁_compatN (force_compatN (T := .thunk _) (C := .amp (.arr .unit (CTy.effOf S R))
      (cancelTy S F)) (.here (.cons (.cons (.cons .nil)))) rfl))
    (.there (.there (.here (.cons .nil))))

/-- **Every premise of `HandleVBN` holds at the instance**, at the bound `⊓∅` of the empty
context: `handleVN_resume_premises` at the boxed clause type, with the context and the row's
answers outliving the bound. -/
theorem handleVBN_resume_premises :
    SemJN (ℍ := ℍ) LifeCtx.empty [] resumeH
      (.val (.tensor (retTy [] .unit .unit)
        (clausesTyB [] .unit LifeCtx.empty.meetOfDom resumeE finsNil))) ∧
    CtxOutlives LifeCtx.empty [] LifeCtx.empty.meetOfDom ∧
    Row.AnsOutlives LifeCtx.empty LifeCtx.empty.meetOfDom resumeRow :=
  ⟨tensorI_compatN .nil (semJN_idV [] .unit)
      (tensorI_compatN .nil (semJN_resumeCTB [] .unit _ _) (unitI_compatN .nil)),
    ⟨BoCa.Fig16.Tree.Wp.Goal791.defines_meetOfDom_empty, fun _ h => by simp at h⟩,
    fun o ho _ => by simp [resumeRow, Row.ofEff] at ho; subst ho; exact .unit⟩

/-! ### Each handler conjunct at the instance -/

/-- **`HandleVN` at the handler `resumeH`**: the conjunct's statement with the handler, its effect
and its types fixed, every other quantifier kept. -/
theorem handleVN_at_resumeH {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {e : Expr} {S : Row}
    {fs : Nat → CTy} {n : UInt32} (hsp : Ctx.SplitP Γ Γ₁ Γ₂) (hd : Ctx.DeadP Γ₁)
    (_hH : resumeH.ValFormIn Γ₁)
    (_hc : SemJN (ℍ := ℍ) Δ Γ₁ resumeH
      (.val (.tensor (retTy S .unit .unit) (clausesTy S .unit resumeE fs))))
    (_hn0 : n ≠ 0) (hnS : ∀ o ∈ S, o.n ≠ n) (_hlen : resumeE.length ≤ 2 ^ 32)
    (_hdv : Row.divB (Row.ofEff n resumeE 0 fs ++ S) = false)
    (he : SemJN (ℍ := ℍ) Δ Γ₂ e (.comp (CTy.effOf (Row.ofEff n resumeE 0 fs ++ S) .unit))) :
    SemJN (ℍ := ℍ) Δ Γ (hndExpr n (resumeE.map Prod.fst) resumeH e)
      (.comp (CTy.effOf S .unit)) :=
  handle_resume_inst hsp hd hnS he

/-- **`HandleVBN` at the handler `resumeH`**, likewise. -/
theorem handleVBN_at_resumeH {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {e : Expr} {S : Row}
    {fs : Nat → CTy} {n : UInt32} {d : Lifetime.Life} (hsp : Ctx.SplitP Γ Γ₁ Γ₂)
    (hd : Ctx.DeadP Γ₁) (_hH : resumeH.ValFormIn Γ₁)
    (_hc : SemJN (ℍ := ℍ) Δ Γ₁ resumeH
      (.val (.tensor (retTy S .unit .unit) (clausesTyB S .unit d resumeE fs))))
    (_hn0 : n ≠ 0) (hnS : ∀ o ∈ S, o.n ≠ n) (_hlen : resumeE.length ≤ 2 ^ 32)
    (_hdv : Row.divB (Row.ofEff n resumeE 0 fs ++ S) = false)
    (he : SemJN (ℍ := ℍ) Δ Γ₂ e (.comp (CTy.effOf (Row.ofEff n resumeE 0 fs ++ S) .unit)))
    (_hΓd : CtxOutlives Δ Γ₂ d) (_hSd : Row.AnsOutlives Δ d (Row.ofEff n resumeE 0 fs ++ S)) :
    SemJN (ℍ := ℍ) Δ Γ (hndExpr n (resumeE.map Prod.fst) resumeH e)
      (.comp (CTy.effOf S .unit)) :=
  handle_resume_inst hsp hd hnS he

/-! ### `ReifyN`'s premises at an instance -/

/-- **Every premise of `ReifyN` holds at an instance**: the residual `λx. x : !U(1 ⊸ F 1)` at the
empty row. -/
theorem reifyN_premises_inst {Δ : LifeCtx} :
    (∀ o ∈ ([] : Row), o.n ≠ divEff) ∧ closedAt 0 idV.1 = true ∧
    SemJN (ℍ := ℍ) Δ [] (.val idV) (.val (resTy [] .unit .unit)) ∧
    Ctx.DeadP ([] : Ctx VTy) :=
  ⟨by simp, rfl, semJN_idV [] .unit, .nil⟩

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
