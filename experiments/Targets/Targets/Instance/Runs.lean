import Targets.Instance.Checks
import Targets.Instance.ContUse
import Targets.Instance.J1

/-!
# The Instance — quiet runs, complete runs along a chain, and closed programs at `J₁`

The run facts the unary laws and the theories read (`Targets/Instance/UnaryLaws.lean`,
`Targets/Instance/Theories.lean`), at Core σ=[]:

* **quiet runs** (`Quiet`): a term reaches another by head steps that keep every memory,
  allocate nothing and are no finaliser's.  Quiet runs compose (`Quiet.trans`), go under every
  evaluation context (`Quiet.plug`), and two terms with a common quiet reduct run alike in every
  evaluation context (`runsAlike_of_quiet`, from `runsAlike_of_join`);
* the quiet runs of the forms our instance encodes A's formers by: `M V` (`quiet_appE`),
  `resume κ w` (`quiet_resumeE`), resuming a continuation (`quiet_kappa_resume`), and an operation a
  handler of values catches (`quiet_hop`);
* **the complete runs along a chain to a value**: every complete run is the chain's path
  (`complete_chain_eq`), so its trace is the chain's (`obsFrom_chain_trace`); the chain's own run
  is complete (`obsFrom_of_chain`); a chain with one finaliser step shows that step's event only
  (`obs_chainPath_one`);
* **a closed program Core types at `F A` is typed at our instance by `J₁`** (`der_J₁_ret`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets.Inst
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont performE raiseE opPayload hndE ubindE hndVal kappa
  clauseAt)
open BoCa.Lifetime (LifeCtx)
open Targets (RowForm EffCtx orowRF orowAlg HeadChain lookRun lookEnd lookRun_sound)

/-! ### Quiet runs -/

/-- **`e` reaches `e'` quietly**: by head steps that keep every memory, allocate nothing and are
no finaliser's, so that each shows no event. -/
def Quiet (e e' : Expr) : Prop :=
  ∃ q, HeadChain (ℍ := ℍ) e q e' ∧ ∀ x ∈ q, finHead x.2.1 = false

theorem Quiet.refl (e : Expr) : Quiet (ℍ := ℍ) e e := ⟨[], .nil, fun _ h => absurd h List.not_mem_nil⟩

theorem Quiet.trans {e e' e'' : Expr} (h₁ : Quiet (ℍ := ℍ) e e') (h₂ : Quiet (ℍ := ℍ) e' e'') :
    Quiet (ℍ := ℍ) e e'' := by
  obtain ⟨q₁, hc₁, hf₁⟩ := h₁
  obtain ⟨q₂, hc₂, hf₂⟩ := h₂
  refine ⟨q₁ ++ q₂, Targets.HeadChain.append hc₁ hc₂, fun x hx => ?_⟩
  rcases List.mem_append.1 hx with hx | hx
  · exact hf₁ x hx
  · exact hf₂ x hx

/-- A quiet run is quiet in every evaluation context. -/
theorem Quiet.plug (K₀ : Kont) {e e' : Expr} (h : Quiet (ℍ := ℍ) e e') :
    Quiet (ℍ := ℍ) (K₀.plug e) (K₀.plug e') := by
  obtain ⟨q, hc, hf⟩ := h
  refine ⟨_, hc.plug K₀, fun x hx => ?_⟩
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
  exact hf y hy

/-- One head step that keeps every memory, allocates nothing and is no finaliser's. -/
theorem Quiet.head (K : Kont) {a a' : Expr} (hh : ∀ μ, Head (ℍ := ℍ) μ a μ a')
    (hn : a.allocs = false) (hf : finHead a = false) :
    Quiet (ℍ := ℍ) (K.plug a) (K.plug a') :=
  ⟨[(K, a, a')], .cons hh hn .nil, fun x hx => by
    rw [List.mem_singleton.1 hx]; exact hf⟩

/-- A β-step, in a context. -/
theorem quiet_beta (K : Kont) (b : Expr) (v : Val) :
    Quiet (ℍ := ℍ) (K.plug (.app (.val (.lam b)) (.val v))) (K.plug (b.subst 0 v)) :=
  Quiet.head K (fun μ => Head.beta μ b v) rfl rfl

/-- A `letpair` step, in a context. -/
theorem quiet_letpair (K : Kont) (v₁ v₂ : Val) (e : Expr) :
    Quiet (ℍ := ℍ) (K.plug (.letpair (.val (.pair v₁ v₂)) e))
      (K.plug ((e.subst 0 (v₂.shift 1 0)).subst 0 v₁)) :=
  Quiet.head K (fun μ => Head.letpair μ v₁ v₂ e) rfl rfl

/-- **Two terms with a common quiet reduct run alike in every evaluation context.** -/
theorem runsAlike_of_quiet {RF : RowForm} {Ξ : EffCtx} {J : OurTyping RF} {t₁ t₂ t : Expr}
    (h₁ : Quiet (ℍ := ℍ) t₁ t) (h₂ : Quiet (ℍ := ℍ) t₂ t) :
    (ourInst (ℍ := ℍ) RF Ξ J).RunsAlike t₁ t₂ := by
  obtain ⟨q₁, hc₁, hf₁⟩ := h₁
  obtain ⟨q₂, hc₂, hf₂⟩ := h₂
  refine runsAlike_of_join hc₁ hc₂ (fun x hx => ?_) (fun x hx => ?_)
  · rw [labelOf_tau_of (hf₁ x hx)]; rfl
  · rw [labelOf_tau_of (hf₂ x hx)]; rfl

/-! ### The quiet runs of A's formers at our instance -/

/-- `M V` at our instance, `V to x. M x`, reaches `M V` by its β-step. -/
theorem quiet_appE (K : Kont) (M : Expr) (V : Val) :
    Quiet (ℍ := ℍ) (K.plug (appE M V.1)) (K.plug (.app M V.1)) := by
  have h := quiet_beta (ℍ := ℍ) K (.app (M.shift 1 0) (.var 0)) V
  rwa [appE_subst] at h

/-- `resume k w` at our instance, `w to y. k (inj₁ ()) y`, reaches `k (inj₁ ()) w`. -/
theorem quiet_resumeE (K : Kont) (k : Expr) (w : Val) :
    Quiet (ℍ := ℍ) (K.plug (resumeE k w.1)) (K.plug (.app (.app k (.inj₁ .unit)) w.1)) := by
  have h := quiet_beta (ℍ := ℍ) K (.app (.app (k.shift 1 0) (.inj₁ .unit)) (.var 0)) w
  rwa [resumeE_subst] at h

/-- **Resuming `κ` at `w` reaches `hnd H K[w]`**, quietly: `kappa_resume_steps`'s four head
steps. -/
theorem quiet_kappa_resume (K₀ : Kont) (n : UInt32) (H : Val) (K : Kont) (w : Val) :
    Quiet (ℍ := ℍ) (K₀.plug (.app (.app (kappa n H K) (.val (Val.inj₁ .unit))) (.val w)))
      (K₀.plug (hndE H (K.plug (.val w)))) := by
  have e₀ : K₀.plug (.app (.app (kappa n H K) (.val (Val.inj₁ .unit))) (.val w)) =
      (K₀.comp (.appL .hole w)).plug (.app (kappa n H K) (.val (Val.inj₁ .unit))) := by
    rw [Kont.plug_comp]; rfl
  rw [e₀]
  refine (Quiet.head (K₀.comp (.appL .hole w)) (fun μ => Head.beta μ _ _) rfl rfl).trans ?_
  refine (Quiet.head (K₀.comp (.appL .hole w)) (fun μ => Head.case₁ μ Val.unit _ _) rfl rfl).trans ?_
  refine (Quiet.head (K₀.comp (.appL .hole w)) (fun μ => Head.seq μ _) rfl rfl).trans ?_
  have e : ∀ (s u : Val), Expr.subst 0 w (Expr.subst 1 u (Expr.subst 2 s
      (hndE (Val.shift 3 0 H) ((Kont.shift 3 0 K).plug (Expr.var 0))))) =
      hndE H (K.plug (.val w)) := by
    intro s u
    simp only [hndE, Expr.subst, Expr.val, Val.val_shift]
    rw [Expr.subst_shift 2 0 2 s H.1 (by omega) (by omega),
      Expr.subst_shift 1 0 1 u H.1 (by omega) (by omega),
      Expr.subst_shift 0 0 0 w H.1 (by omega) (by omega), Expr.shift_zero,
      plug_shift_subst 2 K 0 2 s _ (by omega) (by omega),
      plug_shift_subst 1 K 0 1 u _ (by omega) (by omega),
      plug_shift_subst 0 K 0 0 w _ (by omega) (by omega), Kont.shift_zero]
    simp [Expr.subst]
  rw [Kont.plug_comp]
  have hb := quiet_beta (ℍ := ℍ) K₀
    (Expr.subst 1 Val.unit (Expr.subst 2 (Val.inj₁ Val.unit)
      (hndE (Val.shift 3 0 H) ((Kont.shift 3 0 K).plug (Expr.var 0))))) w
  rw [e] at hb
  exact hb

/-- **An operation a handler of values catches**: `hnd H K[perform (n, (i, v))] ↦ h_i (v, κ)`,
quietly. -/
theorem quiet_hop (K₀ : Kont) (n i : UInt32) (hr hs c v : Val) (K : Kont)
    (hc : clauseAt hs.1 i.toNat = some c) (hK : K.HasHnd n = false) :
    Quiet (ℍ := ℍ) (K₀.plug (hndE (hndVal n hr hs) (K.plug (performE (.val (opPayload n i v))))))
      (K₀.plug (.app (.val c) (.pair (.val v) (kappa n (hndVal n hr hs) K)))) :=
  Quiet.head K₀ (fun μ => Head.hop μ n i hr hs c v K hc hK) rfl rfl

/-! ### Complete runs along a chain to a value -/

section Complete
variable {RF : RowForm} {Ξ : EffCtx} {J : OurTyping RF}

/-- **Every complete run from the start of a chain of head steps that ends at a value is the
chain's path**: each step of the chain is the only step of its configuration (`rstep_det`). -/
theorem complete_chain_eq (R : (ourInst (ℍ := ℍ) RF Ξ J).Runner) {μ : Heap} {s : R.St} :
    ∀ {e e' : Expr} {q₀ : List (Kont × Expr × Expr)}, HeadChain (ℍ := ℍ) e q₀ e' → IsVal e' →
      ∀ q, (ourInst (ℍ := ℍ) RF Ξ J).CompleteFrom R ((μ, e), s) q → q = chainPath R μ s q₀
  | _, _, _, .nil, hv, q, ⟨hp, _⟩ => by
      cases hp with
      | nil => rfl
      | cons hst _ => exact (no_rstep_val R ⟨_, hv⟩ hst).elim
  | _, _, _, @HeadChain.cons _ _ K a a' e' q₀ hh hn hq, hv, q, ⟨hp, hlast⟩ => by
      cases hp with
      | nil => exact absurd (hlast.2 _ _ (OStep.mach (hh μ))) (fun h => h)
      | @cons _ ev c₁ q' hst hp' =>
          obtain ⟨rfl, rfl⟩ := rstep_det (hh μ) hn hst
          have := complete_chain_eq R hq hv q' ⟨hp', by
            rw [← A.EffectSystem.lastC_cons (S := ourInst (ℍ := ℍ) RF Ξ J) _ _ (labelOf RF Ξ a)]
            exact hlast⟩
          rw [this]
          rfl

/-- The chain's own run is complete: its answer is the chain's end, its trace the chain's. -/
theorem obsFrom_of_chain (R : (ourInst (ℍ := ℍ) RF Ξ J).Runner) {μ : Heap} {s : R.St}
    {e e' : Expr} {q : List (Kont × Expr × Expr)} (hc : HeadChain (ℍ := ℍ) e q e') (hv : IsVal e') :
    (ourInst (ℍ := ℍ) RF Ξ J).ObsFrom R ((μ, e), s) ⟨e', isOVal_of_isVal hv⟩
      ((ourInst (ℍ := ℍ) RF Ξ J).obs (chainPath R μ s q)) := by
  have hl := lastC_chainPath (J := J) R (μ := μ) (s := s) hc
  refine ⟨chainPath R μ s q, ⟨rpath_chainPath R hc, ?_⟩, ?_, rfl⟩
  · rw [hl]; exact isVal_val μ ⟨e', hv⟩
  · rw [hl]; rfl

/-- **The trace of every complete run from the start of a chain to a value is the chain's.** -/
theorem obsFrom_chain_trace (R : (ourInst (ℍ := ℍ) RF Ξ J).Runner) {μ : Heap} {s : R.St}
    {e e' : Expr} {q : List (Kont × Expr × Expr)} (hc : HeadChain (ℍ := ℍ) e q e') (hv : IsVal e')
    {v : OVal} {tr : List (ourInst (ℍ := ℍ) RF Ξ J).Event}
    (h : (ourInst (ℍ := ℍ) RF Ξ J).ObsFrom R ((μ, e), s) v tr) :
    tr = (ourInst (ℍ := ℍ) RF Ξ J).obs (chainPath R μ s q) := by
  obtain ⟨q', hq', -, rfl⟩ := h
  rw [complete_chain_eq R hc hv q' hq']

/-- The observable events of a chain whose only finaliser step is `x`: `x`'s event. -/
theorem obs_chainPath_one (R : (ourInst (ℍ := ℍ) RF Ξ J).Runner) (μ : Heap) (s : R.St)
    (q₀ : List (Kont × Expr × Expr)) (x : Kont × Expr × Expr) (q₁ : List (Kont × Expr × Expr))
    (h₀ : q₀.all (fun x => finHead x.2.1 == false) = true)
    (h₁ : q₁.all (fun x => finHead x.2.1 == false) = true) :
    (ourInst (ℍ := ℍ) RF Ξ J).obs (chainPath R μ s (q₀ ++ x :: q₁)) =
      [labelOf RF Ξ x.2.1].filter Targets.A.Ev.Obs := by
  have e₀ := obs_chainPath (J := J) R μ s q₀ h₀
  have e₁ := obs_chainPath (J := J) R μ s q₁ h₁
  unfold A.EffectSystem.obs chainPath at e₀ e₁ ⊢
  rw [List.map_append, List.map_append, List.filter_append, e₀, List.nil_append, List.map_cons,
    List.map_cons, List.filter_cons, List.filter_cons, List.filter_nil, e₁]
  rfl

end Complete

/-! ### Closed programs at `J₁` -/

/-- **A closed program Core types at `F A` is typed at our instance by `J₁`**, at the pure row:
`J₁` closes no slot of the empty context, and the pure row is tied to every effect context. -/
theorem der_J₁_ret {Ξ : EffCtx} {e : Expr} {A : VTy} (hcl : closedAt 0 e = true)
    (h : CDerives LifeCtx.empty [] e (.comp (.ret A))) :
    (ourInst (ℍ := ℍ) orowRF Ξ J₁).der [] e
      ((ourInst (ℍ := ℍ) orowRF Ξ J₁).F (orowAlg Ξ).unit (OVTy.ofV A)) := by
  refine ⟨tiedAt_unit J₁ _, .inl ⟨[], by simp, ?_⟩⟩
  refine ⟨fun _ h => absurd h List.not_mem_nil, OVTy.rFree_ofV A, fun η _ σ _ => ?_⟩
  show CDerives LifeCtx.empty [] (fillS σ 0 e)
    (.comp (CTy.effOf ([] ++ []) (OVTy.den η (OVTy.ofV A))))
  rw [fillS_closed σ e 0 hcl, OVTy.den_ofV]
  exact h

end Targets.Inst

end
