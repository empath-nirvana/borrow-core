import Core.Chain.Borrow834N
import Core.Chain.Count834N
import Core.Chain.Eff835N
import Core.Chain.Fam836N
import Core.Chain.FamCancel836N
import Core.Chain.FamFrame836N
import Core.Chain.FamImm836N
import Core.Chain.FamNew836N
import Core.Chain.FamSlice836N
import Core.Chain.FamSwap836N
import Core.Chain.FoldG836N
import Core.Chain.FoldImm836N
import Core.Chain.Fuel835N
import Core.Chain.HandleL835N
import Core.Chain.HandleT835N
import Core.Chain.ImmLend833N
import Core.Chain.Iter835N
import Core.Chain.Let835N
import Core.Chain.Mu836N
import Core.Chain.Nu837N
import Core.Chain.Rules834N
import Core.Chain.Then835N
import Core.Chain.Unwind833N
import Core.Fundamental

/-!
# `FundamentalN` assembled by induction on `CDerives`  `[spec §62]`

`docs/new-core/scope-831-interface.md` §14. `fundamentalN_all` is Core's `fundamentalC` at
`SemJN₀`: one case per constructor of `CDerives`, in `fundamentalC`'s order and with its case
splits, each calling the rule's chain lemma. The rules with no chain lemma are the conjuncts of
`MissingN`, each stated as its `*_compatN` would be: Core's compatibility lemma with `SemV`/`SemC`
read as `SemJN₀`.

No chain lemma takes a fragment premise, so the induction proves `SemJN₀` at every derivation;
`fundamentalN_of` reads `FundamentalN` off it, the fragment premise unused.

The small adapters, each a corollary of the chain's existing laws:
* `ret_compatN₀`, `ofRet_compatN₀`: `jdgC (.val A)` is `F A`;
* `topI_compatN₀`: `⊤` holds every term;
* `unitI_compatN₀`, `sumI₁_compatN₀`, `sumI₂_compatN₀`: Core's proofs, `erwp_val` and `erwp_bind`;
* `proj₁_compatN₀`, `proj₂_compatN₀`: `cN₀` at `&` is the pair of projections;
* `bangE_compatN₀`, `boxE_compatN₀`: the postcondition weakened (`erwp_mono`);
* `semJN_dead₀`: Core's `semC_dead`, for `effAwait` at a consumed context;
* `semJN_effOf_rc₀`: Core's `semC_effOf_rc`, for the handlers' marked rows.
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
open BoCa.Fig16.Tree.Wp.Goal791 (jdgC)
open BoCa.BoLo (Heap Kont Head eLoad eStore)

/-! ### Adapters -/

/-- **`return V : F A` at `SemJN₀`** (Core's `ret_compatC`): `jdgC (.val A)` is `F A`. -/
theorem ret_compatN₀ {Δ : LifeCtx} {Γ : Ctx VTy} {V : Expr} {A : VTy}
    (h : SemJN₀ (ℍ := ℍ) Δ Γ V (.val A)) : SemJN₀ (ℍ := ℍ) Δ Γ V (.comp (.ret A)) := h

/-- **A computation of `F A` is a value-judged expression at `A`** (`fundamentalC`'s `ofRet`). -/
theorem ofRet_compatN₀ {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {A : VTy}
    (h : SemJN₀ (ℍ := ℍ) Δ Γ e (.comp (.ret A))) : SemJN₀ (ℍ := ℍ) Δ Γ e (.val A) := h

/-- **`⟨⟩ : ⊤` at `SemJN₀`** (Core's `topI_compatC`). -/
theorem topI_compatN₀ {Δ : LifeCtx} {Γ : Ctx VTy} :
    SemJN₀ (ℍ := ℍ) Δ Γ (.val .unit) (.comp .top) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ => trivial

/-- **`() : 1` at `SemJN₀`** (Core's `unitI_compatC`). -/
theorem unitI_compatN₀ {Δ : LifeCtx} {Γ : Ctx VTy} (h : Ctx.DeadP Γ) :
    SemJN₀ (ℍ := ℍ) Δ Γ (.val .unit) (.val .unit) := by
  intro δ γ Θ c n ls ρ _ _ _ _ hg
  obtain rfl := gN_deadP₀ h hg
  rw [substAll_closed (v := Val.unit) rfl]
  exact erwp_val (v := Val.unit) ⟨rfl, rfl⟩

/-- **`inj₁ e : A ⊕ B` at `SemJN₀`** (Core's `sumI₁_compatC`). -/
theorem sumI₁_compatN₀ {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {A B : VTy}
    (h : SemJN₀ (ℍ := ℍ) Δ Γ e (.val A)) : SemJN₀ (ℍ := ℍ) Δ Γ (.inj₁ e) (.val (.sum A B)) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  refine erwp_bind (LocTy.view_down hΘ.1 c) (.inj₁ .hole) (fun _ => rfl) (fun _ => rfl)
    (fun _ _ _ _ h => by cases h) (fun k ls' v σ hv => ?_) n ls _ ρ
    (h δ γ Θ c n ls ρ hδ hΘ hc hlw hg)
  exact erwp_val (v := Val.inj₁ v) (Or.inl ⟨v, rfl, hv⟩)

/-- **`inj₂ e : A ⊕ B` at `SemJN₀`** (Core's `sumI₂_compatC`). -/
theorem sumI₂_compatN₀ {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {A B : VTy}
    (h : SemJN₀ (ℍ := ℍ) Δ Γ e (.val B)) : SemJN₀ (ℍ := ℍ) Δ Γ (.inj₂ e) (.val (.sum A B)) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  refine erwp_bind (LocTy.view_down hΘ.1 c) (.inj₂ .hole) (fun _ => rfl) (fun _ => rfl)
    (fun _ _ _ _ h => by cases h) (fun k ls' v σ hv => ?_) n ls _ ρ
    (h δ γ Θ c n ls ρ hδ hΘ hc hlw hg)
  exact erwp_val (v := Val.inj₂ v) (Or.inr ⟨v, rfl, hv⟩)

private theorem substAll_app_val (γ : List Val) (M : Expr) (w : Val)
    (hw : ∀ k, Expr.psub k γ w.val = w.val) :
    substAll γ (.app M (.val w)) = .app (substAll γ M) (.val w) := by
  show Expr.app (Expr.psub 0 γ M) (Expr.psub 0 γ w.val) = _
  rw [hw]; rfl

/-- **`π₁ M : C` at `SemJN₀`** (Core's `proj₁_compatC`). -/
theorem proj₁_compatN₀ {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {C D : CTy}
    (h : SemJN₀ (ℍ := ℍ) Δ Γ M (.comp (.amp C D))) :
    SemJN₀ (ℍ := ℍ) Δ Γ (.app M (.val (.inj₁ .unit))) (.comp C) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  show cN₀ (ℍ := ℍ) C δ Θ c n ls (substAll γ (.app M (.val (.inj₁ .unit)))) ρ
  rw [substAll_app_val γ M _ (fun k => by simp [Expr.psub])]
  exact (h δ γ Θ c n ls ρ hδ hΘ hc hlw hg).1

/-- **`π₂ M : D` at `SemJN₀`** (Core's `proj₂_compatC`). -/
theorem proj₂_compatN₀ {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {C D : CTy}
    (h : SemJN₀ (ℍ := ℍ) Δ Γ M (.comp (.amp C D))) :
    SemJN₀ (ℍ := ℍ) Δ Γ (.app M (.val (.inj₂ .unit))) (.comp D) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  show cN₀ (ℍ := ℍ) D δ Θ c n ls (substAll γ (.app M (.val (.inj₂ .unit)))) ρ
  rw [substAll_app_val γ M _ (fun k => by simp [Expr.psub])]
  exact (h δ γ Θ c n ls ρ hδ hΘ hc hlw hg).2

/-- **Dereliction at `SemJN₀`** (Core's `bangE_compatC`): a value of `!A` is one of `A`. -/
theorem bangE_compatN₀ {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {A : VTy}
    (h : SemJN₀ (ℍ := ℍ) Δ Γ e (.val (.bang A))) : SemJN₀ (ℍ := ℍ) Δ Γ e (.val A) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  exact erwp_mono (fun _ _ _ _ hv => hv.2) (opTableN_local _) n ls _ ρ
    (h δ γ Θ c n ls ρ hδ hΘ hc hlw hg)

/-- **`[]E` at `SemJN₀`** (Core's `boxE_compatC`): a value of `[@a] A` is one of `A`. -/
theorem boxE_compatN₀ {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {a : Lifetime.Life} {A : VTy}
    (h : SemJN₀ (ℍ := ℍ) Δ Γ e (.val (.box a A))) : SemJN₀ (ℍ := ℍ) Δ Γ e (.val A) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  exact erwp_mono (fun _ _ _ _ ⟨_, _, hv, _⟩ => hv) (opTableN_local _) n ls _ ρ
    (h δ γ Θ c n ls ρ hδ hΘ hc hlw hg)

/-- A consumed context relates only the empty resource. -/
theorem gN_dead₀ {δ : LSub} {Θ : LocTy} {n : Nat} : ∀ {Γ : Ctx VTy}, Ctx.Dead Γ →
    ∀ {γ : List Val} {ρ : WRes}, gN₀ (ℍ := ℍ) δ Θ Γ γ n ρ ↔ ρ = PMap.empty := by
  intro Γ hd
  induction hd with
  | nil => intro γ ρ; cases γ <;> rfl
  | cons _ ih =>
      intro γ ρ
      cases γ with
      | nil => rfl
      | cons v γ' => simpa [gN₀] using ih (γ := γ')

/-- A consumed context lives within every value list. -/
theorem liveWithin_dead_ctx : ∀ {Γ : Ctx VTy}, Ctx.Dead Γ → ∀ γ : List Val, Ctx.LiveWithin Γ γ := by
  intro Γ hd
  induction hd with
  | nil => intro γ; simp
  | cons _ ih => intro γ; cases γ with
    | nil => exact ⟨by simp, ih []⟩
    | cons v γ => exact ih γ

/-- **`SemJN₀` at a consumed context does not read the slots' types** (Core's `semC_dead`), at a
term no substitution moves. -/
theorem semJN_dead₀ {Δ : LifeCtx} {Γ₁ Γ₂ : Ctx VTy} {e : Expr} {j : Jdg} (h₁ : Ctx.Dead Γ₁)
    (h₂ : Ctx.Dead Γ₂) (he : ∀ γ γ' : List Val, substAll γ e = substAll γ' e)
    (h : SemJN₀ (ℍ := ℍ) Δ Γ₁ e j) : SemJN₀ (ℍ := ℍ) Δ Γ₂ e j := by
  intro δ γ Θ c n ls ρ hδ hΘ hc _ hg
  obtain rfl := (gN_dead₀ h₂).mp hg
  rw [he γ (List.replicate Γ₁.length Val.unit)]
  exact h δ _ Θ c n ls _ hδ hΘ hc (liveWithin_dead_ctx h₁ _) ((gN_dead₀ h₁).mpr rfl)

/-- `await_n` is closed. -/
theorem awaitE_closed {n : UInt32} : closedAt 0 (awaitE n) = true := rfl

/-- **A row's markers are not read by the relation** (Core's `semC_effOf_rc`). -/
theorem semJN_effOf_rc₀ {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {S S' : Row} {A : VTy}
    (h : S.map OpSig.unmark = S'.map OpSig.unmark)
    (hS : SemJN₀ (ℍ := ℍ) Δ Γ e (.comp (CTy.effOf S A))) :
    SemJN₀ (ℍ := ℍ) Δ Γ e (.comp (CTy.effOf S' A)) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  show cN₀ (ℍ := ℍ) (CTy.effOf S' A) δ Θ c n ls _ ρ
  rw [← cN_tyEq₀ (CTy.effOf S A) (CTyEq.effOf_unmark A δ h)]
  exact hS δ γ Θ c n ls ρ hδ hΘ hc hlw hg

/-- **`forget : ? ⊸ 1` at `SemJN₀`** (Core's `forgetUnk_compatX`): nothing to release. -/
theorem releaseUnk_compatN₀ {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.DeadP Γ) :
    SemJN₀ (ℍ := ℍ) Δ Γ forget (.val axForgetUnkTy) := by
  refine sem_constN₀ (v := Val.lam unit') hΓ rfl fun δ Θ n _ _ => ?_
  intro Θ' _ hΘ' _ _ ls' c'' k _ v σ τ hcomp hv hcon
  obtain rfl := eq_of_compS_empty_left hcomp
  obtain rfl := hv
  have hΦ := LocTy.view_down hΘ'.1 c''
  refine erwp_det hΦ (opTableN_down OpTabN.empty_down) (fun k _ v ρ h => vN_down₀ _ δ Θ' k v ρ h)
    (fun μ => step1Only_plug (Head.beta μ _ v) rfl .hole) ?_
  exact erwp_val (v := Val.unit) ⟨rfl, rfl⟩

/-- **`forget : !A ⊸ 1` at `SemJN₀`** (Core's `releaseBang_compatC`): nothing to release. -/
theorem releaseBang_compatN₀ {Δ : LifeCtx} {Γ : Ctx VTy} {A : VTy} (hΓ : Ctx.DeadP Γ) :
    SemJN₀ (ℍ := ℍ) Δ Γ forget (.val (.thunk (.arr (.bang A) (.ret .unit)))) := by
  refine sem_constN₀ (v := Val.lam unit') hΓ rfl fun δ Θ n _ _ => ?_
  intro Θ' _ hΘ' _ _ ls' c'' k _ v σ τ hcomp hv hcon
  obtain rfl := eq_of_compS_empty_left hcomp
  obtain ⟨rfl, -⟩ := hv
  have hΦ := LocTy.view_down hΘ'.1 c''
  refine erwp_det hΦ (opTableN_down OpTabN.empty_down) (fun k _ v ρ h => vN_down₀ _ δ Θ' k v ρ h)
    (fun μ => step1Only_plug (Head.beta μ _ v) rfl .hole) ?_
  exact erwp_val (v := Val.unit) ⟨rfl, rfl⟩

/-- **`copy : !A ⊸ !A ⊗ !A` at `SemJN₀`** (Core's `copyBang_compatC`): a value of `!A` holds `∅`. -/
theorem copyBang_compatN₀ {Δ : LifeCtx} {Γ : Ctx VTy} {A : VTy} (hΓ : Ctx.DeadP Γ) :
    SemJN₀ (ℍ := ℍ) Δ Γ copy (.val (.thunk (.arr (.bang A) (.ret (.tensor (.bang A) (.bang A)))))) := by
  refine sem_constN₀ (v := Val.lam (.pair BoCa.v0 BoCa.v0)) hΓ rfl fun δ Θ n _ _ => ?_
  intro Θ' _ hΘ' _ _ ls' c'' k _ v σ τ hcomp hv hcon
  obtain rfl := eq_of_compS_empty_left hcomp
  have hσ : τ = PMap.empty := hv.1
  subst hσ
  have hΦ := LocTy.view_down hΘ'.1 c''
  refine erwp_det hΦ (opTableN_down OpTabN.empty_down) (fun k _ v ρ h => vN_down₀ _ δ Θ' k v ρ h)
    (fun μ => step1Only_plug (Head.beta μ _ v) rfl .hole) ?_
  have hb : Kont.hole.plug (Expr.subst 0 v (.pair BoCa.v0 BoCa.v0)) = (Val.pair v v).1 := by
    simp [BoCa.v0, Expr.subst, Kont.plug]
  rw [hb]
  exact erwp_val (v := Val.pair v v)
    ⟨v, v, PMap.empty, PMap.empty, rfl, ResU.comp_empty_right _, hv, hv⟩

/-- **`alloc : A ⊸ Ref A` at `SemJN₀`** (Core's `alloc_compatX`, `[TR]` 6.141): the new cell
beside the argument's resource. -/
theorem alloc_compatN₀ {Δ : LifeCtx} {Γ : Ctx VTy} {A : VTy} (hΓ : Ctx.DeadP Γ) :
    SemJN₀ (ℍ := ℍ) Δ Γ (.val (.prim .alloc)) (.val (.lolli A (.ref A))) := by
  refine sem_constN₀ (v := Val.prim .alloc) hΓ rfl fun δ Θ n _ _ => ?_
  intro Θ' _ hΘ' _ _ ls' c'' k _ v σ τ hcomp hv hcon
  obtain rfl := eq_of_compS_empty_left hcomp
  have hΦ := LocTy.view_down hΘ'.1 c''
  refine erwp_alloc (Kc := .hole) hΦ (opTableN_local _) v fun l σ₁ σ₂ hcell hc => ?_
  have hσ : σ₁ = ResU.single l (CellU.ownOf v) := hcell
  subst hσ
  exact erwp_val (v := Val.loc l) ⟨l, v, τ, rfl, ResU.CompS.comm hc, vN_le₀ (Nat.sub_le k 1) hv⟩

/-- **`free : Ref A ⊸ A` at `SemJN₀`** (Core's `free_compatX`, `[TR]` 6.142): the cell freed, its
content's resource returned. -/
theorem free_compatN₀ {Δ : LifeCtx} {Γ : Ctx VTy} {A : VTy} (hΓ : Ctx.DeadP Γ) :
    SemJN₀ (ℍ := ℍ) Δ Γ (.val (.prim .free)) (.val (.lolli (.ref A) A)) := by
  refine sem_constN₀ (v := Val.prim .free) hΓ rfl fun δ Θ n _ _ => ?_
  intro Θ' _ hΘ' _ _ ls' c'' k _ v σ τ hcomp hv hcon
  obtain rfl := eq_of_compS_empty_left hcomp
  obtain ⟨l, u, σ', rfl, hcu, hu⟩ := hv
  have hΦ := LocTy.view_down hΘ'.1 c''
  exact erwp_free (Kc := .hole) hΦ (opTableN_local _) l u
    ⟨_, _, hcu, rfl, erwp_val (vN_le₀ (Nat.sub_le k 1) hu)⟩

/-- **`forget : Imm @a A ⊸ 1` at `SemJN₀`** (Core's `forgetImm_compatX`, `[TR]` 6.171): an
`imm` cell holds no `own` cell and is let go (`erwp_garbage`). -/
theorem releaseImm_compatN₀ {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {A : VTy}
    (hΓ : Ctx.DeadP Γ) : SemJN₀ (ℍ := ℍ) Δ Γ forget (.val (axForgetImmTy a A)) := by
  refine sem_constN₀ (v := Val.lam unit') hΓ rfl fun δ Θ n _ _ => ?_
  intro Θ' _ hΘ' _ _ ls' c'' k _ v σ τ hcomp hv hcon
  rw [eq_of_compS_empty_left hcomp]
  have hΦ := LocTy.view_down hΘ'.1 c''
  refine erwp_garbage (compS_empty_left σ) (noOwn_immN₀ hv) ?_
  refine erwp_det hΦ (opTableN_down OpTabN.empty_down) (fun k _ v ρ h => vN_down₀ _ δ Θ' k v ρ h)
    (fun μ => step1Only_plug (Head.beta μ _ v) rfl .hole) ?_
  exact erwp_val (v := Val.unit) ⟨rfl, rfl⟩

/-- **`forget : Mut @a A ⊸ 1` at `SemJN₀`** (Core's `forgetMut_compatX`, `[TR]` 6.171): a `mut`
leaf holds no `own` cell and is let go (`erwp_garbage`). -/
theorem releaseMut_compatN₀ {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {A : VTy}
    (hΓ : Ctx.DeadP Γ) : SemJN₀ (ℍ := ℍ) Δ Γ forget (.val (axForgetMutTy a A)) := by
  refine sem_constN₀ (v := Val.lam unit') hΓ rfl fun δ Θ n _ _ => ?_
  intro Θ' _ hΘ' _ _ ls' c'' k _ v σ τ hcomp hv hcon
  rw [eq_of_compS_empty_left hcomp]
  have hΦ := LocTy.view_down hΘ'.1 c''
  refine erwp_garbage (compS_empty_left σ) (noOwn_mutN₀ hv) ?_
  refine erwp_det hΦ (opTableN_down OpTabN.empty_down) (fun k _ v ρ h => vN_down₀ _ δ Θ' k v ρ h)
    (fun μ => step1Only_plug (Head.beta μ _ v) rfl .hole) ?_
  exact erwp_val (v := Val.unit) ⟨rfl, rfl⟩

/-- **`copy : Imm @a A ⊸ Imm @a A ⊗ Imm @a A` at `SemJN₀`** (Core's `copy_compatX`): the `imm`
cell composes with itself (`vN_imm_dupN₀`). -/
theorem copy_compatN₀ {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {A : VTy}
    (hΓ : Ctx.DeadP Γ) : SemJN₀ (ℍ := ℍ) Δ Γ copy (.val (axCopyTy a A)) := by
  refine sem_constN₀ (v := Val.lam (.pair BoCa.v0 BoCa.v0)) hΓ rfl fun δ Θ n _ _ => ?_
  intro Θ' _ hΘ' _ _ ls' c'' k _ v σ τ hcomp hv hcon
  obtain rfl := eq_of_compS_empty_left hcomp
  have hΦ := LocTy.view_down hΘ'.1 c''
  refine erwp_det hΦ (opTableN_down OpTabN.empty_down) (fun k _ v ρ h => vN_down₀ _ δ Θ' k v ρ h)
    (fun μ => step1Only_plug (Head.beta μ _ v) rfl .hole) ?_
  have hb : Kont.hole.plug (Expr.subst 0 v (.pair BoCa.v0 BoCa.v0)) = (Val.pair v v).1 := by
    simp [BoCa.v0, Expr.subst, Kont.plug]
  rw [hb]
  obtain ⟨τ₁, τ₂, hc, h₁, h₂⟩ := vN_imm_dupN₀ hv
  exact erwp_val (v := Val.pair v v) ⟨v, v, τ₁, τ₂, rfl, hc, h₁, h₂⟩

private theorem substAll_withPairN (γ : List Val) (M N : Expr) :
    substAll γ (withPair M N) =
      .val (.lam (.case (.var 0) (.seq (.var 0) (Expr.psub 2 γ M))
        (.seq (.var 0) (Expr.psub 2 γ N)))) := by
  show Expr.psub 0 γ (.lam _) = _
  simp [Expr.psub]

private theorem withBody_substN (γ : List Val) (M N : Expr) (s : Val) :
    (Expr.case (.var 0) (.seq (.var 0) (Expr.psub 2 γ M)) (.seq (.var 0) (Expr.psub 2 γ N))).subst 0 s
      = .case (.val s) (.seq (.var 0) (Expr.psub 1 (s :: γ) M))
          (.seq (.var 0) (Expr.psub 1 (s :: γ) N)) := by
  simp [Expr.subst, Expr.psub_cons 1 s γ]

private theorem seq_subst_unitN (e : Expr) :
    (Expr.seq (.var 0) e).subst 0 Val.unit = .seq (.val .unit) (e.subst 0 Val.unit) := by
  simp [Expr.subst]

/-- **`⟨M, N⟩ : C & D` at `SemJN₀`** (Core's `withI_compatC`): each projection runs three head
steps (β, `case`, `;`) to its branch, which gets the whole context resource. -/
theorem withI_compatN₀ {Δ : LifeCtx} {Γ : Ctx VTy} {M N : Expr} {C D : CTy}
    (hM : SemJN₀ (ℍ := ℍ) Δ (withCtx Γ) M (.comp C))
    (hN : SemJN₀ (ℍ := ℍ) Δ (withCtx Γ) N (.comp D)) :
    SemJN₀ (ℍ := ℍ) Δ Γ (withPair M N) (.comp (.amp C D)) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  show cN₀ (ℍ := ℍ) (.amp C D) δ Θ c n ls (substAll γ (withPair M N)) ρ
  rw [substAll_withPairN]
  refine ⟨?_, ?_⟩
  · refine cN_head₀ C δ Θ hΘ.1 c n ls ρ .hole _ _
      (fun μ => Head.beta μ _ (Val.inj₁ Val.unit)) rfl ?_
    simp only [Kont.plug]
    rw [withBody_substN]
    refine cN_head₀ C δ Θ hΘ.1 c n ls ρ .hole _ _ (fun μ => Head.case₁ μ Val.unit _ _) rfl ?_
    simp only [Kont.plug]
    rw [seq_subst_unitN]
    refine cN_head₀ C δ Θ hΘ.1 c n ls ρ .hole _ _ (fun μ => Head.seq μ _) rfl ?_
    simp only [Kont.plug]
    rw [← substAll_cons_psub]
    exact hM δ _ Θ c n ls ρ hδ hΘ hc hlw (gN_dead_cons₀ _ _ (gN_dead_cons₀ _ _ hg))
  · refine cN_head₀ D δ Θ hΘ.1 c n ls ρ .hole _ _
      (fun μ => Head.beta μ _ (Val.inj₂ Val.unit)) rfl ?_
    simp only [Kont.plug]
    rw [withBody_substN]
    refine cN_head₀ D δ Θ hΘ.1 c n ls ρ .hole _ _ (fun μ => Head.case₂ μ Val.unit _ _) rfl ?_
    simp only [Kont.plug]
    rw [seq_subst_unitN]
    refine cN_head₀ D δ Θ hΘ.1 c n ls ρ .hole _ _ (fun μ => Head.seq μ _) rfl ?_
    simp only [Kont.plug]
    rw [← substAll_cons_psub]
    exact hN δ _ Θ c n ls ρ hδ hΘ hc hlw (gN_dead_cons₀ _ _ (gN_dead_cons₀ _ _ hg))

/-- **`[let-poly]` at `SemJN₀`** (Core's `letPoly_compatC`): one β step to `N` with the closed
λ-value for its variable, read at a dead slot. -/
theorem letPoly_compatN₀ {Δ : LifeCtx} {Γ : Ctx VTy} {N : Expr} {C : CTy} (V : Val)
    (hV : closedAt 0 V.1 = true)
    (hN : SemJN₀ (ℍ := ℍ) Δ (⟨.unit, false⟩ :: Γ) ((N.subst 0 V).shift 1 0) (.comp C)) :
    SemJN₀ (ℍ := ℍ) Δ Γ (.app (.val (.lam N)) (.val V)) (.comp C) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  have h := hN δ (V :: γ) Θ c n ls ρ hδ hΘ hc hlw (gN_dead_cons₀ .unit V hg)
  have e₁ : substAll (V :: γ) ((N.subst 0 V).shift 1 0) = (Expr.psub 1 γ N).subst 0 V := by
    show Expr.psub 0 (V :: γ) _ = _
    rw [psub_fill hV γ N 0, Expr.psub_cons 0 V γ N, Val.shift_zero]
  rw [e₁] at h
  show cN₀ (ℍ := ℍ) C δ Θ c n ls (Expr.psub 0 γ (.app (.val (.lam N)) (.val V))) ρ
  simp only [Expr.psub]
  rw [psub_closedAt V.1 γ hV (Nat.zero_le 0)]
  exact cN_head₀ C δ Θ hΘ.1 c n ls ρ .hole _ _ (fun μ => Head.beta μ (Expr.psub 1 γ N) V) rfl h

/-- `swap` as a value. -/
def swapV : Val := ⟨swap, .lam⟩

/-- The body of `swap` at the source `ℓ`, after the first β step. -/
def swapAt (l : Loc) : Val :=
  Val.lam (elet (eLoad l) (.seq (.app (.app store' (.val (.loc l))) BoCa.v1)
    (.pair (.val (.loc l)) BoCa.v0)))

/-- **`swap : Ref A ⊸ B ⊸ Ref B ⊗ A` at `SemJN₀`** (Core's `swap_compatX`): the old payload
loaded, the new one stored, the cell handed back beside the old payload. -/
theorem swap_compatN₀ {Δ : LifeCtx} {Γ : Ctx VTy} {A B : VTy} (hΓ : Ctx.DeadP Γ) :
    SemJN₀ (ℍ := ℍ) Δ Γ swap (.val (axSwapTy A B)) := by
  intro δ γ Θ c n ls ρ _ _ _ _ hg
  obtain rfl := gN_deadP₀ hΓ hg
  show erwp (ℍ := ℍ) (Θ.view c) (opTableN OpTabN.empty) _ n ls (substAll γ swap) _
  rw [show substAll γ swap = swap from psub_closedAt _ γ (by decide) (Nat.zero_le 0)]
  refine erwp_val (v := swapV) ?_
  -- the source, at the world the constant's `U` reached
  intro Θ₁ _ hΘ₁ _ _ ls₁ c₂ k₁ _ v₁ τ₀ ρ₁ hcomp hv₁ _
  obtain rfl := eq_of_compS_empty_left hcomp
  obtain ⟨l, w, σw, rfl, hcw, hw⟩ := hv₁
  have hΦ₁ : (Θ₁.view c₂).Down := LocTy.view_down hΘ₁.1 c₂
  refine erwp_det hΦ₁ (opTableN_down OpTabN.empty_down) (fun k _ v ρ h => vN_down₀ _ δ Θ₁ k v ρ h)
    (fun μ => step1Only_plug (Head.beta μ _ (Val.loc l)) rfl .hole) ?_
  have e₁ : Kont.hole.plug (Expr.subst 0 (Val.loc l)
      (Expr.val (Val.lam (elet (.app load' BoCa.v1)
        (.seq (.app (.app store' BoCa.v2) BoCa.v1) (.pair BoCa.v2 BoCa.v0)))))) =
      (swapAt l).1 := by
    simp [Kont.plug, elet, eLoad, Expr.subst, Expr.shift, BoCa.v0, BoCa.v1, BoCa.v2, load', store',
      swapAt, Val.loc, Val.lam, Expr.val, Val.prim]
  rw [e₁]
  refine erwp_val (v := swapAt l) ?_
  -- the new payload, at the world the body's `U` reached; the old one arrives there along `ExtR`
  intro Θ₂ hE₂ hΘ₂ _ _ ls₂ c₄ k₂ hk₂ v₂ ρv τ₂ hc₂ hv₂ _
  have hΦ : (Θ₂.view c₄).Down := LocTy.view_down hΘ₂.1 c₄
  have hw₂ : vN₀ (ℍ := ℍ) A δ Θ₂ k₁ w σw := vN_extR₀ A δ k₁ w σw (hE₂.right hcw) hw
  refine erwp_det hΦ (opTableN_down OpTabN.empty_down) (fun k _ v ρ h => vN_down₀ _ δ Θ₂ k v ρ h)
    (fun μ => step1Only_plug (Head.beta μ _ v₂) rfl .hole) ?_
  have e₂ : Kont.hole.plug (Expr.subst 0 v₂ (elet (eLoad l)
      (.seq (.app (.app store' (.val (.loc l))) BoCa.v1) (.pair (.val (.loc l)) BoCa.v0)))) =
      (Kont.appR (.val (Val.lam (.seq (eStore l (v₂.shift 1 0)) (.pair (.val (.loc l)) BoCa.v0))))
        .hole).plug (eLoad l) := by
    simp [Kont.plug, elet, eLoad, eStore, Expr.subst, BoCa.v0, BoCa.v1, store', Val.loc, Expr.val,
      Val.prim, Val.lam]
  rw [e₂]
  -- `wp-load` of the old payload
  obtain ⟨rest, hrest, hXr⟩ := compS_reassoc hcw hc₂
  refine erwp_bindR hΦ (opTableN_local _) _ ?_
  refine rwp_load ls₂ l w _ ⟨_, rest, hXr, rfl, fun ρ₁' ρ₂' hpto hcomp' => ?_⟩
  obtain rfl := hpto
  obtain rfl : τ₂ = ρ₂' := ResU.CompS.functional hXr (ResU.CompS.comm hcomp')
  simp only [Kont.plug]
  refine erwp_det hΦ (opTableN_down OpTabN.empty_down) (fun k _ v ρ h => vN_down₀ _ δ Θ₂ k v ρ h)
    (fun μ => step1Only_plug (Head.beta μ _ w) rfl .hole) ?_
  have e₃ : Kont.hole.plug (Expr.subst 0 w
      (.seq (eStore l (v₂.shift 1 0)) (.pair (.val (.loc l)) BoCa.v0))) =
      (Kont.seq .hole (.pair (.val (.loc l)) (.val w))).plug
        (.app (.val (Val.storeV (Val.loc l))) (.val v₂)) := by
    simp [Kont.plug, eStore, Expr.subst, BoCa.v0, Val.storeV, Val.loc, Expr.val, Val.prim,
      Expr.subst_shift 0 0 0 w v₂.val (Nat.le_refl 0) (Nat.le_refl 0), Expr.shift_zero]
  rw [e₃]
  -- `wp-store` of the new payload, then the pair
  refine erwp_bindR hΦ (opTableN_local _) _ ?_
  refine rwp_store ls₂ l w v₂ _ ⟨_, rest, hXr, rfl, fun t₁ t hpto hct => ?_⟩
  obtain rfl := hpto
  simp only [Kont.plug]
  refine erwp_det hΦ (opTableN_down OpTabN.empty_down) (fun k _ v ρ h => vN_down₀ _ δ Θ₂ k v ρ h)
    (fun μ => step1Only_plug (Head.seq μ _) rfl .hole) ?_
  refine erwp_val (v := Val.pair (Val.loc l) w) ?_
  obtain ⟨cv, hcv, hct'⟩ := compS_reassoc' (ResU.CompS.comm hrest) (ResU.CompS.comm hct)
  exact ⟨Val.loc l, w, cv, σw, rfl, hct',
    ⟨l, v₂, ρv, rfl, hcv, vN_le₀ (by omega) hv₂⟩, vN_le₀ (by omega) hw₂⟩

/-- **The self-reference** (Core's `fixSelf_valid`): with the step a value at `Θ₀` and the index
`n₀`, the self-reference at every budget is a value of `1 ⊕ !U(A ⊸ C)` at every world and every
index up to `n₀`; by induction on the budget. -/
theorem fixSelfN_valid₀ {A : VTy} {C : CTy} {δ : LSub} {Θ₀ : LocTy} {n₀ : Nat} (s : Val)
    (hs : vN₀ (ℍ := ℍ) (fixStepTy A C) δ Θ₀ n₀ s PMap.empty) :
    ∀ (m : Nat) (k : UInt32), k.toNat = m → ∀ (Θ : LocTy) (n : Nat), n ≤ n₀ →
      vN₀ (ℍ := ℍ) (fixSelfTy A C) δ Θ n (fixSelf s k) PMap.empty := by
  intro m
  induction m with
  | zero =>
      intro k hk Θ n _
      have hk0 : k = 0 := UInt32.toNat_inj.mp (by simpa using hk)
      unfold fixSelf
      rw [if_pos hk0]
      exact Or.inl ⟨Val.unit, rfl, rfl, rfl⟩
  | succ j ih =>
      intro k hk Θ n hn
      have hk0 : k ≠ 0 := fun h => by subst h; simp at hk
      have hkj : (k - 1).toNat = j := by
        have : (k - 1).toNat = k.toNat - 1 := by
          rw [UInt32.toNat_sub_of_le]
          · rfl
          · rw [UInt32.le_iff_toNat_le]; simp; omega
        omega
      unfold fixSelf
      rw [if_neg hk0]
      refine Or.inr ⟨_, rfl, rfl, fun Θ' _ hΘ' _ _ ls' c' k' hk' x ρx ρ' hc hx hcon => ?_⟩
      obtain rfl := eq_of_compS_empty_left hc
      refine cN_head₀ C δ Θ' hΘ'.1 c' k' ls' ρ' .hole _ _ (fun μ => Head.beta μ _ x) rfl ?_
      simp only [Kont.plug]
      rw [fixSelf_body_subst]
      refine cN_head₀ C δ Θ' hΘ'.1 c' k' ls' ρ' .hole _ _
        (fun μ => Head.boundedFix μ s (k - 1) x) rfl ?_
      exact hs.2 Θ' (LocTy.extR_empty Θ₀ Θ') hΘ' c' (consistentX_empty c') ls' c' k' (by omega)
        (Val.pair (fixSelf s (k - 1)) x) ρ' ρ' (compS_empty_left ρ')
        ⟨fixSelf s (k - 1), x, PMap.empty, ρ', rfl, compS_empty_left ρ',
          ih (k - 1) hkj Θ' k' (by omega), hx⟩ hcon

/-- **`bounded_fix` at `SemJN₀`** (Core's `boundedFix_compatX`): one `boundedFix` step to the step
on its self-reference (`fixSelfN_valid₀`) and the argument. -/
theorem boundedFix_compatN₀ {Δ : LifeCtx} {Γ : Ctx VTy} {A : VTy} {C : CTy} (hΓ : Ctx.DeadP Γ) :
    SemJN₀ (ℍ := ℍ) Δ Γ (.val (.prim .boundedFix)) (.val (boundedFixTy A C)) := by
  refine sem_constN₀ (v := Val.prim .boundedFix) hΓ rfl fun δ Θ n _ _ => ⟨rfl, ?_⟩
  intro Θ' _ hΘ' _ _ ls' c'' k _ v σ τ hcomp hv hcon
  obtain rfl := eq_of_compS_empty_left hcomp
  obtain ⟨s, v₂, σ₁, σ₂, rfl, hc, hs, h₂⟩ := hv
  have e₁ : σ₁ = PMap.empty := hs.1
  subst e₁
  obtain rfl := eq_of_compS_empty_left hc
  obtain ⟨vk, a, ρk, ρa, rfl, hc₂, ⟨⟨kk, rfl⟩, rfl⟩, ha⟩ := h₂
  obtain rfl := eq_of_compS_empty_left hc₂
  refine cN_head₀ C δ Θ' hΘ'.1 c'' k ls' τ .hole _ _ (fun μ => Head.boundedFix μ s kk a) rfl ?_
  exact hs.2 Θ' (LocTy.extR_refl _ _) hΘ' c'' (consistentX_empty c'') ls' c'' k le_rfl
    (Val.pair (fixSelf s kk) a) τ τ (compS_empty_left τ)
    ⟨fixSelf s kk, a, PMap.empty, τ, rfl, compS_empty_left τ,
      fixSelfN_valid₀ s hs _ kk rfl Θ' k le_rfl, ha⟩ hcon

/-! ### The three rules with no chain lemma -/

/-- `reify_res` (Core's `reify_compatX`). -/
def ReifyN : Prop :=
  ∀ {Δ : LifeCtx} {Γ : Ctx VTy} {S : Row} {B R : VTy} {res : Val},
    (∀ o ∈ S, o.n ≠ divEff) → closedAt 0 res.1 = true →
    SemJN₀ (ℍ := ℍ) Δ [] (.val res) (.val (resTy S B R)) → Ctx.DeadP Γ →
    SemJN₀ (ℍ := ℍ) Δ Γ (.val (reifyV res)) (.val (reifyTy S B R))

/-- `[handle]` at a value form (Core's `handleV_compatC`). -/
def HandleVN : Prop :=
  ∀ {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {H e : Expr} {S : Row} {E : List (Qual × VTy × VTy)}
    {fs : Nat → CTy} {n : UInt32} {A R : VTy},
    Ctx.SplitP Γ Γ₁ Γ₂ → Ctx.DeadP Γ₁ → H.ValFormIn Γ₁ →
    SemJN₀ (ℍ := ℍ) Δ Γ₁ H (.val (.tensor (retTy S A R) (clausesTy S R E fs))) →
    n ≠ 0 → (∀ o ∈ S, o.n ≠ n) → E.length ≤ 2 ^ 32 →
    Row.divB (Row.ofEff n E 0 fs ++ S) = false →
    SemJN₀ (ℍ := ℍ) Δ Γ₂ e (.comp (CTy.effOf (Row.ofEff n E 0 fs ++ S) A)) →
    SemJN₀ (ℍ := ℍ) Δ Γ (hndExpr n (E.map Prod.fst) H e) (.comp (CTy.effOf S R))

/-- BOXED-κ `[handle]` (Core's `handleV_compatCB`). -/
def HandleVBN : Prop :=
  ∀ {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {H e : Expr} {S : Row} {E : List (Qual × VTy × VTy)}
    {fs : Nat → CTy} {n : UInt32} {A R : VTy} {d : Lifetime.Life},
    Ctx.SplitP Γ Γ₁ Γ₂ → Ctx.DeadP Γ₁ → H.ValFormIn Γ₁ →
    SemJN₀ (ℍ := ℍ) Δ Γ₁ H (.val (.tensor (retTy S A R) (clausesTyB S R d E fs))) →
    n ≠ 0 → (∀ o ∈ S, o.n ≠ n) → E.length ≤ 2 ^ 32 →
    Row.divB (Row.ofEff n E 0 fs ++ S) = false →
    SemJN₀ (ℍ := ℍ) Δ Γ₂ e (.comp (CTy.effOf (Row.ofEff n E 0 fs ++ S) A)) →
    CtxOutlives Δ Γ₂ d → Row.AnsOutlives Δ d (Row.ofEff n E 0 fs ++ S) →
    SemJN₀ (ℍ := ℍ) Δ Γ (hndExpr n (E.map Prod.fst) H e) (.comp (CTy.effOf S R))

/-- **The rules the chain has no lemma for**, each as its `*_compatN` would be. -/
def MissingN : Prop :=
  HandleVN (ℍ := ℍ) ∧ HandleVBN (ℍ := ℍ) ∧ ReifyN (ℍ := ℍ)

/-! ### The induction -/

/-- **Every derivation is sound at `SemJN₀`**, from `MissingN`: Core's `fundamentalC`, case by
case. -/
theorem fundamentalN_all (hm : MissingN (ℍ := ℍ)) {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr}
    {j : Jdg} (h : CDerives Δ Γ e j) : SemJN₀ (ℍ := ℍ) Δ Γ e j := by
  obtain ⟨hHV, hHVB, hReify⟩ := hm
  induction h with
  | var h => exact var_compatN₀ h
  | unitI h => exact unitI_compatN₀ h
  | tensorI hs _ _ ih₁ ih₂ => exact tensorI_compatN₀ hs ih₁ ih₂
  | sumI₁ _ ih => exact sumI₁_compatN₀ ih
  | sumI₂ _ ih => exact sumI₂_compatN₀ ih
  | thunkF _ ih => exact thunkF_compatN₀ ih
  | thunkV hC _ ih => exact thunkV_compatN₀ hC ih
  | ret _ ih => exact ret_compatN₀ ih
  | bind hs _ _ ihM ihN => exact bind_compatN₀ hs ihM ihN
  | force h => exact force_compatN₀ h
  | lam _ ih => exact lam_compatN₀ ih
  | lamDead _ ih => exact lamDead_compatN₀ ih
  | app hs _ hx ih => exact app_compatN₀ hs ih hx
  | withI _ _ ihM ihN => exact withI_compatN₀ ihM ihN
  | proj₁ _ ih => exact proj₁_compatN₀ ih
  | proj₂ _ ih => exact proj₂_compatN₀ ih
  | topI => exact topI_compatN₀
  | unitE hs _ _ ihV ihM => exact unitE_compatN₀ hs ihV ihM
  | tensorE hs _ _ ihV ihM => exact tensorE_compatN₀ hs ihV ihM
  | sumE hs _ _ _ ihV ih₁ ih₂ => exact sumE_compatN₀ hs ihV ih₁ ih₂
  | zeroE hs _ ihV => exact zeroE_compatN₀ hs ihV
  | allI hbx hΔx hΓx _ ih => exact allI_compatN₀ hbx hΔx hΓx ih
  | allE _ hlt ih => exact allE_compatN₀ ih hlt
  | bangThunkF hp _ ih => exact bangThunkF_compatN₀ hp ih
  | bangThunkV hp hC _ ih => exact bangThunkV_compatN₀ hp hC ih
  | bangE _ ih => exact bangE_compatN₀ ih
  | copyBang hΓ => exact copyBang_compatN₀ hΓ
  | releaseBang hΓ => exact releaseBang_compatN₀ hΓ
  | boxI _ hΓ ih => exact boxI_compatN₀ ih hΓ
  | boxE _ ih => exact boxE_compatN₀ ih
  | immSub _ hle ih => exact immSub_compatN₀ ih hle
  | mutSub _ hle ih => exact mutSub_compatN₀ ih hle
  | alloc hΓ => exact alloc_compatN₀ hΓ
  | free hΓ => exact free_compatN₀ hΓ
  | tokMint hΓ => exact tokMint_compatN₀ hΓ
  | tokBurn hΓ => exact tokBurn_compatN₀ hΓ
  | swap hΓ => exact swap_compatN₀ hΓ
  | copy hΓ => exact copy_compatN₀ hΓ
  | releaseImm hΓ => exact releaseImm_compatN₀ hΓ
  | releaseMut hΓ => exact releaseMut_compatN₀ hΓ
  | releaseUnk hΓ => exact releaseUnk_compatN₀ hΓ
  | lit c hΓ => exact lit_compatN₀ c hΓ
  | hostOp op hΓ => exact hostOp_compatN₀ op hΓ
  | arrNew _ hΓ => exact arrNew_compatN hΓ
  | arrFree _ hΓ => exact arrFree_compatN₀ hΓ
  | arrSize _ hΓ => exact arrSize_compatN₀ hΓ
  | arrReplace _ hΓ => exact arrReplace_compatN₀ hΓ
  | arrLen _ _ hΓ => exact arrLen_compatN₀ hΓ
  | arrGet _ _ hΓ => exact arrGet_compatN₀ hΓ
  | arrCopy _ _ hΓ => exact arrCopy_compatN₀ hΓ
  | arrRelease _ _ hΓ => exact arrRelease_compatN₀ hΓ
  | countFold _ hΓ => exact countFold_compatN hΓ
  | countTry _ _ hΓ => exact countTry_compatN hΓ
  | boundedFix _ _ hΓ => exact boundedFix_compatN₀ hΓ
  | iterate _ _ _ _ hS hΓ => exact iterate_compatN₀ hS hΓ
  | divFuel _ _ hS hΓ => exact divFuel_compatN hS hΓ
  | reify _ _ _ _ hS hcl _ hΓ ihres => exact hReify hS hcl ihres hΓ
  | sliceBorrowM x hΓ hA hB hf₁ hf₂ => exact sliceBorrowM_compatN x hΓ hA hB hf₁ hf₂
  | sliceBorrowI x hΓ hsc hA hB hf₁ hf₂ => exact sliceBorrowI_compatN x hΓ hsc hA hB hf₁ hf₂
  | sliceGetM _ _ hΓ => exact sliceGetM_compatN₀ hΓ
  | sliceLenM _ _ hΓ => exact sliceLenM_compatN₀ hΓ
  | sliceSplitI _ _ hΓ => exact sliceSplitI_compatN₀ hΓ
  | sliceSplitM _ _ hΓ => exact sliceSplitM_compatN₀ hΓ
  | sliceEmptyI _ _ hΓ => exact sliceEmptyI_compatN₀ hΓ
  | sliceEmptyM _ _ hΓ => exact sliceEmptyM_compatN₀ hΓ
  | arrEmpty _ hΓ => exact arrEmpty_compatN₀ hΓ
  | sliceReplaceM _ _ hΓ => exact sliceReplaceM_compatN hΓ
  | sliceSwapM _ _ hΓ => exact sliceSwapM_compatN hΓ
  | withbor1 x hΓ _ hsc₁ hf₁ hf₂ => exact withbor1_compatN x hΓ hsc₁ hf₁ hf₂
  | withbor2 x hΓ _ hside hf₁ hf₂ => exact withbor2_compatN x hΓ hside hf₁ hf₂
  | withbor3 x hΓ _ hf₁ hf₂ => exact withbor3_compatN x hΓ hf₁ hf₂
  | withload x hΓ _ hf₁ hf₂ => exact withload_compatN x hΓ hf₁ hf₂
  | withswap hΓ => exact withswap_compatN hΓ
  | withbor1U x hΓ _ hsc₁ hf₁ hf₂ hS hdc _ ihd =>
      exact withbor1U_compatN x hΓ hsc₁ hf₁ hf₂ hS hdc ihd
  | withbor2U x hΓ _ hside hf₁ hf₂ hS hdc _ ihd =>
      exact withbor2U_compatN x hΓ hside hf₁ hf₂ hS hdc ihd
  | withbor3U x hΓ _ hf₁ hf₂ hS hdc _ ihd => exact withbor3U_compatN x hΓ hf₁ hf₂ hS hdc ihd
  | withloadU x hΓ _ hf₁ hf₂ hS => exact withloadU_compatN x hΓ hf₁ hf₂ hS
  | sliceBorrowMU x hΓ hA hB hf₁ hf₂ hS hdc _ ihd =>
      exact sliceBorrowMU_compatN x hΓ hA hB hf₁ hf₂ hS hdc ihd
  | sliceBorrowIU x hΓ hsc hA hB hf₁ hf₂ hS hdc _ ihd =>
      exact sliceBorrowIU_compatN x hΓ hsc hA hB hf₁ hf₂ hS hdc ihd
  | lolliE hs _ _ iha ihf => exact lolliE_compatN₀ hs iha ihf
  | allEV _ hlt ih => exact allEV_compatN₀ ih hlt
  | ofRet _ ih => exact ofRet_compatN₀ ih
  | roll hA hc _ ih => exact roll_compatN hA hc ih
  | unroll _ ih => exact unroll_compatN ih
  | foldImm F y c R hΓ hF hG hyM hyR hR => exact foldImm_compatN F hF hG y c R hΓ hyM hyR hR
  | foldOwn F R hΓ hF hG => exact foldOwn_compatN F hF hG R hΓ
  | foldReuse F R hΓ hF hG => exact foldReuse_compatN F hF hG R hΓ
  | foldOwnG B₀ Rs hΓ hB => exact foldOwnG_compatN B₀ hB Rs hΓ
  | nuIn hC _ ih => exact nuIn_compatN hC ih
  | nuOut hC _ ih => exact nuOut_compatN hC ih
  | unfoldN C S hC hS hΓ => exact unfoldN_compatN hC S hS hΓ
  | effSub hle _ ih => exact sub_compatN₀ hle ih
  | effPerform hf hna _ _ ih => exact perform_compatN₀ hf hna ih
  | effAwait hΓ hfa ha haA hfc hc =>
      exact semJN_dead₀ .nil hΓ (fun γ γ' => by
          rw [show substAll γ (awaitE _) = _ from psub_closedAt _ γ awaitE_closed le_rfl,
            show substAll γ' (awaitE _) = _ from psub_closedAt _ γ' awaitE_closed le_rfl])
        (await_compatN₀ hfa ha haA hfc hc)
  | effRaise hf ha _ hd _ ih =>
      exact raise_compatN₀ hf ha (fun _ _ _ _ _ h => vN_noOwn_of_ownFree₀ hd h) ih
  | effLet hs hW hU _ _ ihM ihN => exact let_compatN₀ hs hW hU ihM ihN
  | effThen hs hNZ _ hU hMS hDS hfin hP _ _ _ _ ihM ihN ihD =>
      exact then_compatN₀ hs hNZ hU hMS hDS
        (fun n i o o' h₁ h₂ hc => hfin n i o o' h₁ h₂ (OpSig.finRead_of_capB hc)) hP ihM ihN ihD
  | @effThenDiv _ _ _ _ _ _ _ _ _ _ SM SD hs hNZ _ hU hMS hDS hfin hP hcap _ _ _ ihM ihN ihD =>
      cases hSD : Row.divB SD
      · exact then_compatN₀ hs hNZ hU hMS hDS
          (fun n i o o' h₁ h₂ hc => hfin n i o o' h₁ h₂ (OpSig.finRead_of_capB hc)) hP ihM ihN ihD
      · exact thenDiv_compatN₀ hs hNZ hU hMS hDS hP hcap ihM ihN ihD
  | effHandleV hs hd hH _ hn0 hnS hlen hdv _ ihc ihe =>
      exact hHV hs hd hH ihc hn0 hnS hlen (by rwa [Row.divB_ofEff_rc] at hdv)
        (semJN_effOf_rc₀ (Row.unmark_ofEff_append _ _ _ _ _ _) ihe)
  | effHandleVB hs hd hH _ hn0 hnS hlen hdv _ hΓd hSd ihc ihe =>
      exact hHVB hs hd hH ihc hn0 hnS hlen (by rwa [Row.divB_ofEff_rc] at hdv)
        (semJN_effOf_rc₀ (Row.unmark_ofEff_append _ _ _ _ _ _) ihe) hΓd
        (Row.ansOutlives_ofEff_rc hSd)
  | effHandleT hs hd hHr hHc _ hn0 hnd hnS hlen hSN hLin _ ihc ihe =>
      exact handleT_compatN hs hd hHr hHc ihc hnS hlen hSN hLin ihe
  | effHandleL hs hd hHr hHw hHn _ hn0 hnd hnS hlen hNZ hCancel hSW hSu hFin _ ihc ihe =>
      exact handleL_compatN hs hd hHr hHw hHn ihc hnS hlen hNZ hCancel hSW hSu hFin ihe
  | letPoly b hcl _ _ _ ihN => exact letPoly_compatN₀ (Val.lam b) hcl ihN
  | alpha _ hα ih => exact alpha_compatN₀ hα ih

/-- **`FundamentalN` from `MissingN`**: `fundamentalN_all`, the fragment premise unused. -/
theorem fundamentalN_of (h : MissingN (ℍ := ℍ)) : FundamentalN (ℍ := ℍ) :=
  fun _ _ _ _ hder _ => fundamentalN_all h hder

/-- **#791's end goal from `MissingN`**: `goal791Sched_of_fundamental` at `fundamentalN_of`. -/
theorem goal791SchedN_of_missing (h : MissingN (ℍ := ℍ)) : Goal791SchedN (ℍ := ℍ) :=
  goal791Sched_of_fundamental (fundamentalN_of h)

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
