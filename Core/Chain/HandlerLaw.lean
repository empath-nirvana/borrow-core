import Core.Chain.Fundamental831N
import Core.Chain.Kappa835N
import Core.Chain.PoolSpawnN
import Core.EffCancelTyped

/-!
# `HandlerLawN`, the named assertion for the three handler rules  `[spec §62]`

`FundamentalN` is proved at every `CDerives` derivation from `MissingN` (`fundamentalN_all`):
every rule but `[handle]` at a value form (`effHandleV`), BOXED-κ `[handle]` (`effHandleVB`) and
`reify` has a chain lemma. `HandlerLawN` names those three compatibility lemmas as one hypothesis,
a `Prop` and not an axiom, in the form of `PinLaw` (`Core/PinLaw.lean`): three fields, each stated
as its `*_compatN` would be, over `SemJN` premises only, at every row, qualifier, handler and
handled computation. It carries no restriction to a scheduler or to a class of clauses.

**What it asserts.** `handleV` (`HandleVN`, Core's `handleV_compatC`): a handler whose clauses
are in the relation at `clausesTy`, over a handled computation in the relation at the handled row,
is in the relation at the outer row. `handleVB` (`HandleVBN`, Core's `handleV_compatCB`): the same
at `clausesTyB`, `κ` boxed at `@d`, with the context and the row's answers outliving `@d`. `reify`
(`ReifyN`, Core's `reify_compatX`): `reify_res` at a residual in the relation is in the relation at
`reifyTy`.

**Why it is believed.** Core proves all three on its own relation (`handleV_compatC`,
`handleV_compatCB`, `reify_compatX`, `Core/Fundamental.lean`), and `PinLaw` already rests on the
same belief: a borrow held across a suspension is sound under a handler written in the program.
What the chain lacks is one step of Core's proof, `vC_kTy_of_kapRel`: the clause is handed `κ`
with `KapRelN`, Kripke along `extF` from the stop's list, and `vN`'s `U` clause at `kTy` asks for
it at every `ExtR`-extension of the world and every consistent view (`scope-831-interface.md`
§10.1, E10). `reify` reads its loop through the same `U` clause (§12.5). The discharge route is
the Kripke stop (`scope-835-kripke-stop.md`, on the parked branch `rule-791-kstop`).

**Not refuted.** `Kappa835N.not_kapRelKTyN` refutes the step `KapRelKTyN`, not a conjunct: both of
its configurations use the thunk `κ = ()`, which no `[op]` step hands a clause
(`kappa_ne_unit`, `kappaC_ne_unit`), and their failure is the resumption of `()` being final
(`unit_resume_final`), where the resumption of every `κ` the step does hand takes a step
(`kappa_resume_not_final`, `kappaC_resume_not_final`).

**Not vacuous.**
* `handle_resume_inst`: the conclusion shared by `HandleVN` and `HandleVBN` holds at the handler
  `resumeH` (`h_ret = λx. x`, one unrestricted clause `λ(x, κ). (λk'. k'.1 x) κ` that receives
  `κ` and resumes it) over every handled computation at the handled row, at every outer row; proved
  through `erwp_handle_le`, the clause reading `κ` only by `KapRelN`'s resumption. So
  `handleVN_at_resumeH` and `handleVBN_at_resumeH` are the two conjuncts at that handler.
* `handleVN_resume_premises`, `handleVBN_resume_premises`: every premise of each conjunct holds at
  that handler over `perform (1, (0, ()))`, the clauses in the relation by their derivations' chain
  lemmas.
* `reifyN_premises_inst`: every premise of `ReifyN` holds at the residual `λx. x`. No instance of
  `ReifyN`'s conclusion is proved.
* `goal791SchedN_premises_inst`: every premise of `Goal791SchedN` holds at the task `return ()`
  under the scheduler `HS` (`hs_schedOKN` at the empty table), so the headline is applied at a
  point its premises reach (`orDiverges_inst_of_handlerLaw`).
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

/-- **HandlerLawN**: the named assumption for the three handler rules with no chain lemma, each
stated over `SemJN` premises only. -/
structure HandlerLawN : Prop where
  /-- `[handle]` at a value form is in the relation (`effHandleV`). -/
  handleV : HandleVN (ℍ := ℍ)
  /-- BOXED-κ `[handle]` is in the relation (`effHandleVB`). -/
  handleVB : HandleVBN (ℍ := ℍ)
  /-- `reify_res` is in the relation (`reify`). -/
  reify : ReifyN (ℍ := ℍ)

/-- `HandlerLawN` says what `MissingN` says. -/
theorem handlerLawN_iff : HandlerLawN (ℍ := ℍ) ↔ MissingN (ℍ := ℍ) :=
  ⟨fun h => ⟨h.handleV, h.handleVB, h.reify⟩, fun ⟨a, b, c⟩ => ⟨a, b, c⟩⟩

/-- **`FundamentalN` from `HandlerLawN`.** -/
theorem fundamentalN_of_handlerLaw (h : HandlerLawN (ℍ := ℍ)) : FundamentalN (ℍ := ℍ) :=
  fundamentalN_of (handlerLawN_iff.mp h)

/-- **#791's end goal from `HandlerLawN`**: `goal791SchedN_of_missing`. -/
theorem goal791SchedN_of_handlerLaw (h : HandlerLawN (ℍ := ℍ)) : Goal791SchedN (ℍ := ℍ) :=
  goal791SchedN_of_missing (handlerLawN_iff.mp h)

/-! ### The continuation the configurations of `Kappa835N` use

`not_kTy_world` and `not_kTy_view` refute `KapRelKTyN` at the thunk `κ = ()`. The `[op]` step hands
a clause `kappa H K` (an unrestricted operation) or, after the cell's allocation, `kappaC b ℓ H K`
(must-resume or cancellable; `erwp_handle_le`'s clause premise). Neither is `()`, and the
resumption of each takes a `β` step in every context at every memory, where the configurations'
failure is the resumption of `()` being final (`not_kTy_at`). -/

theorem kappa_ne_unit (H : Val) (K : Kont) : kappa H K ≠ Val.unit.1 := by
  unfold kappa; simp [Val.unit]

theorem kappaC_ne_unit (b : Bool) (l : Loc) (H : Val) (K : Kont) :
    kappaC b l H K ≠ Val.unit.1 := by
  unfold kappaC; simp [Val.unit]

/-- The resumption of the configurations' `κ = ()` is final in every context. -/
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
context beside a consumed one. -/
theorem handle_resume_inst {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {e : Expr} {S : Row}
    {fs : Nat → CTy} {n : UInt32} (hsp : Ctx.SplitP Γ Γ₁ Γ₂) (hd : Ctx.DeadP Γ₁)
    (hnS : ∀ o ∈ S, o.n ≠ n)
    (he : SemJN (ℍ := ℍ) Δ Γ₂ e (.comp (CTy.effOf (Row.ofEff n resumeE 0 fs ++ S) .unit))) :
    SemJN (ℍ := ℍ) Δ Γ (hndExpr n (resumeE.map Prod.fst) resumeH e)
      (.comp (CTy.effOf S .unit)) := by
  intro δ γ Θ c N ls ρ hδ hΘ hcρ hlw hg
  refine (cN_effOf S .unit δ Θ c N ls _ ρ).mpr (erwp_of_valid fun hv => ?_)
  obtain ⟨ρ₁, ρ₂, hc12, hg₁, hg₂, -, hc₂⟩ := gN_splitC hsp hg hcρ hv
  obtain ⟨-, hlw₂⟩ := hsp.liveWithin hlw
  obtain rfl : ρ₁ = PMap.empty := gN_deadP hd hg₁
  rw [eq_of_compS_empty_left hc12]
  have hE' := (cN_effOf _ .unit δ Θ c N ls _ ρ₂).mp
    (he δ γ Θ c N ls ρ₂ hδ hΘ hc₂ hlw₂ hg₂)
  show erwp (ℍ := ℍ) _ _ _ N ls (Expr.psub 0 γ (hndExpr n _ resumeH e)) ρ₂
  rw [psub_hndExpr, psub_closedAt resumeH γ resumeH_closed le_rfl]
  have hΦ := LocTy.view_down hΘ.1 c
  have hToutD : (tabN (ℍ := ℍ) (CTy.effOf S .unit) δ Θ c).Down := tabN_down _ δ Θ hΘ.1 c
  have hQout : PostN.Down (fun k _ v ρ => vN (ℍ := ℍ) .unit δ Θ k v ρ) :=
    fun k _ v ρ h => vN_down _ δ Θ k v ρ h
  have hTd := opTableN_down hToutD
  refine erwp_handle_le hΦ N _ _ (tabN_down _ δ Θ hΘ.1 c) hToutD n
    (fun m i hm => tabN_ofEff_ne .unit .unit δ Θ c hm)
    (qualsVal [.unr]) idV (Val.pair resumeCT Val.unit) _ _ hQout
    (fun i en hT _ => capTag_ofEffN (E := resumeE) hnS (by simp) i en hT)
    (fun _ => none) (fun _ _ _ _ _ _ h => by cases h) ?_ ?_ N le_rfl ls _ ρ₂ hE'
  · -- `[ret]`: `λx. x` at the value
    intro k _ ls' v σ hv
    refine erwp_det hΦ hTd hQout (fun μ => step1Only_plug (Head.beta μ (.var 0) v) rfl .hole) ?_
    exact erwp_val hv
  · intro i en hT
    obtain ⟨j, hj, hji, -, rfl⟩ := tabN_ofEff_self hnS (by simp) hT
    obtain rfl : j = 0 := by simp at hj; omega
    refine ⟨resumeCT, by rw [hji]; simp [clauseAt, Val.pair]; exact resumeCT.2, ?_, ?_⟩
    · intro _ k _ ls' v κ σ hσ
      obtain ⟨σa, σk, hck, ⟨rfl, rfl⟩, hK⟩ := hσ
      obtain rfl := eq_of_compS_empty_left hck
      cases k with
      | zero => exact erwp_zero
      | succ k₀ =>
      refine erwp_step (opTableN_local _)
        (fun μ => step1Only_plug (Head.beta μ _ (Val.pair Val.unit κ)) rfl .hole) ?_
      refine erwp_pureSteps hΦ hTd hQout (resumeCT_body_steps κ) ?_
      exact (hK.2 ls' (extF_refl ls' _) k₀ (by omega)).1 Val.unit PMap.empty _
        ⟨⟨rfl, rfl⟩, consistentX_empty c⟩ (ResU.CompS.comm (compS_empty_left _))
    · intro ha
      simp [entN, VTy.isZero] at ha

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
    (proj₁_compatN (force_compatN (C := .amp (.arr .unit (CTy.effOf S R)) (cancelTy S F))
      (.here (.cons (.cons (.cons .nil))))))
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
    (proj₁_compatN (force_compatN (C := .amp (.arr .unit (CTy.effOf S R)) (cancelTy S F))
      (.here (.cons (.cons (.cons .nil))))))
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

/-! ### `Goal791SchedN`'s premises at an instance -/

/-- A scheduler meeting its clauses at a table meets them at the empty table, its tasks' answers
weakened. -/
theorem schedOKN_empty {Φ : LocFam} {T : OpTabN} {n₀ : UInt32} {qs hr hs : Val}
    {Qin Qin' Qout : PostN} (h : SchedOKN (ℍ := ℍ) Φ T n₀ qs hr hs Qin Qout)
    (hQ : ∀ k ls v ρ, Qin' k ls v ρ → Qin k ls v ρ) :
    SchedOKN (ℍ := ℍ) Φ OpTabN.empty n₀ qs hr hs Qin' Qout := fun N =>
  { down := OpTabN.empty_down
    names := fun _ _ _ => rfl
    tags := fun _ _ h => by simp [OpTabN.empty] at h
    fin := fun _ _ h => by simp [OpTabN.empty] at h
    wc := fun _ _ h => by simp [OpTabN.empty] at h
    qdown := (h N).qdown
    ret := fun k hk ls v ρ hv => (h N).ret k hk ls v ρ (hQ k ls v ρ hv)
    op := fun _ _ h => by simp [OpTabN.empty] at h }

/-- **Every premise of `Goal791SchedN` holds at an instance**: the task `return ()` at the empty
row, typed from no constants, at the empty world, under the scheduler `HS` with its own answers
and invariant (`hs_schedOKN` at the empty table). -/
theorem goal791SchedN_premises_inst (c : Loc → Option Life) :
    (CTy.effOf [] .unit).inFrag = true ∧
    CDerives LifeCtx.empty (BoCa.Fig16.Tree.Wp.Goal791.ctx791 []) (.val Val.unit)
      (.comp (CTy.effOf [] .unit)) ∧
    LocTy.empty.OK ∧ LocTy.empty.imm = [] ∧
    (∀ k ls v ρ, PoolSpawn.QVN k ls v ρ → ρ = PMap.empty) ∧
    PoolSpawn.InvSN (ℍ := ℍ) (LocTy.empty.view c) [] ∧
    SchedOKN (ℍ := ℍ) (LocTy.empty.view c) (rowTabN (ℍ := ℍ) [] LocTy.empty c)
      BoCa.Fig16.Tree.Wp.SchedProgs.Park.nP BoCa.Fig16.Tree.Wp.SchedProgs.Spawn.qsS
      BoCa.Fig16.Tree.Wp.SchedProgs.Stack.stackRet BoCa.Fig16.Tree.Wp.SchedProgs.Spawn.hsS
      (fun k _ v ρ => vN (ℍ := ℍ) .unit LSub.empty LocTy.empty k v ρ)
      (PoolAnsN (ℍ := ℍ) (LocTy.empty.view c) PoolSpawn.QVN
        (hndVal BoCa.Fig16.Tree.Wp.SchedProgs.Park.nP BoCa.Fig16.Tree.Wp.SchedProgs.Spawn.qsS
          BoCa.Fig16.Tree.Wp.SchedProgs.Stack.stackRet BoCa.Fig16.Tree.Wp.SchedProgs.Spawn.hsS)
        (PoolSpawn.InvSN (ℍ := ℍ) (LocTy.empty.view c))) :=
  ⟨rfl, .ret (.unitI .nil), LocTy.empty_ok, rfl, fun _ _ _ _ h => h, fun _ h => by simp at h,
    schedOKN_empty (PoolSpawn.hs_schedOKN (LocTy.view_down LocTy.empty_ok.1 c))
      (fun _ _ v ρ h => (show v = Val.unit ∧ ρ = PMap.empty from h).2)⟩

/-- **`Goal791SchedN` at the instance, from `HandlerLawN`**: the scheduler's run of `return ()`. -/
theorem orDiverges_inst_of_handlerLaw (h : HandlerLawN (ℍ := ℍ)) (c : Loc → Option Life) :
    OrDiverges (ℍ := ℍ)
      (.app (hndE BoCa.Fig16.Tree.Wp.SchedProgs.Spawn.HS (substAll [] (.val Val.unit)))
        (stateValN BoCa.Fig16.Tree.Wp.SchedProgs.Spawn.HS []).1) := by
  obtain ⟨hfr, hder, hΘ, hΘI, hQ, hInv, hS⟩ := goal791SchedN_premises_inst (ℍ := ℍ) c
  exact goal791SchedN_of_handlerLaw h [] (by simp) (by simp) [] _ hfr hder LocTy.empty c _ _ _ _
    _ _ hΘ hΘI hQ hInv hS

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
