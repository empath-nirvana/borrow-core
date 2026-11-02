import DtorUnwind.TreeWp.Eff
import DtorUnwind.SI.CaptureAdequacy
import DtorUnwind.Tree.Port.Split

/-!
# The scheduler-wide invariant over the tree world

`SI/CactusInv.lean`'s `CactusInv`, at a world `w`: the branches (the running computation, the
stored continuations, the spawned closures) are resources at `w`'s tree, the world is their
composition, and the world invariant holds. The records proper and their ownership go with the
records (`TreeWp/Rel.lean`).

The operations, each proved to keep the invariant:

* **step** (`cactusT_step`): the running branch at `twp` under the frame of the others ends at a
  world extending the start, the others **re-read** there (in `SI/` they were untouched; the
  tree grew under them);
* **grow** (`cactusT_extend`): a fresh child or a graft extends the world, every branch re-read
  (`CompAllT.reread`);
* **capture / move** (`cactusT_move`): a part leaves one branch for another (a continuation's
  share stored by the scheduler, a borrow handed to a joiner); world and memory unchanged;
* **unwind** is a step of the cancelled branch's `fin` obligation at `twp`, so it is
  `cactusT_step`.

**Adequacy is derived from the invariant** (`cerwpT_adequacy`): the initial configuration is the
invariant at one empty branch; `cactusT_step` carries it to any final configuration; there the
branch's postcondition gives an empty resource, so the world is empty, so the memory is.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.Tree.Wp
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.DtorUnwind.SI
open BoCa.BoLo (Heap Step1 Steps Head Kont freeE)

/-- The composition of a list of resources. -/
inductive CompAllT {K : WCactus} : List (TRes K) → TRes K → Prop
  | nil : CompAllT [] PMap.empty
  | cons {ρ W W' : TRes K} {ρs : List (TRes K)} : CompAllT ρs W' → ResUT.CompS ρ W' W →
      CompAllT (ρ :: ρs) W

/-- **The scheduler-wide invariant over the tree world.** -/
def CactusInvT (w : TWd) (bs : List (TRes w.K)) (W : TRes w.K) (μ : Heap) : Prop :=
  CompAllT bs W ∧ WInv w W μ

theorem compAllT_functional {K : WCactus} {ρs : List (TRes K)} {W W' : TRes K}
    (h : CompAllT ρs W) (h' : CompAllT ρs W') : W = W' := by
  induction h generalizing W' with
  | nil => cases h'; rfl
  | cons hr hc ih =>
      cases h' with
      | cons hr' hc' =>
          cases ih hr'
          exact ResUT.CompS.functional hc hc'

/-- **The re-reading of the world is the branches' re-readings composed.** -/
theorem CompAllT.reread {w w' : TWd} (hE : w.Ext w') (hM : MonoΘ w'.Θ) {bs : List (TRes w.K)}
    {W : TRes w.K} (h : CompAllT bs W) (hc : CovR w.Θ w.K W) {W' : TRes w'.K}
    (hr : RRw (w := w) (w' := w') W W') :
    ∃ bs' : List (TRes w'.K), List.Forall₂ (fun a b => RRw (w := w) (w' := w') a b) bs bs' ∧
      CompAllT bs' W' := by
  induction h generalizing W' with
  | nil =>
      refine ⟨[], .nil, ?_⟩
      obtain rfl := RR.of_empty hr
      exact .nil
  | @cons ρ W₀ W₁ ρs hr₁ hc₁ ih =>
      obtain ⟨a', b', ha, hb, hab⟩ := RR.split hE.1 hM hc₁ (hc.mono hE.2) hr
      obtain ⟨bs', h₂, h₃⟩ := ih (CovR.of_compS_right hc₁ hc) hb
      exact ⟨a' :: bs', .cons ha h₂, .cons h₃ hab⟩

/-- **The running branch and its frame.** -/
theorem cactusT_frame {w : TWd} {ρ : TRes w.K} {rest : List (TRes w.K)} {W : TRes w.K}
    {μ : Heap} (h : CactusInvT w (ρ :: rest) W μ) :
    ∃ ρf, CompAllT rest ρf ∧ ResUT.Hash ρf ρ ∧ ResUT.CompS ρf ρ W ∧ WInv w W μ := by
  obtain ⟨hC, hI⟩ := h
  cases hC with
  | cons hr hc =>
  rename_i ρf
  exact ⟨ρf, hr, hash_of_inv (ResUT.CompS.comm hc) hI, ResUT.CompS.comm hc, hI⟩

/-- **A run keeps the invariant**: the running branch at `twp`, under the frame of the others,
ends at a world extending the start where the invariant holds with its new resource and the
others re-read. -/
theorem cactusT_step {F : TFrame} {Q : TPost} {n : Nat} {w : TWd} {e : Expr} {ρ : TRes w.K}
    {rest : List (TRes w.K)} {W : TRes w.K} {μ : Heap}
    (h : twp (ℍ := ℍ) F Q n w e ρ) (hI : CactusInvT w (ρ :: rest) W μ)
    (hF : ∀ ρf, CompAllT rest ρf → F w ρf) (hfd : FinDom μ)
    {j : Nat} {μ' : Heap} {e' : Expr} (hj : j < n) (hrun : StepsN (ℍ := ℍ) j μ e μ' e')
    (hfin : Final (ℍ := ℍ) μ' e') :
    ∃ (w' : TWd) (ρ' W' : TRes w'.K) (rest' : List (TRes w'.K)), w.Ext w' ∧
      List.Forall₂ (fun a b => RRw (w := w) (w' := w') a b) rest rest' ∧
      CactusInvT w' (ρ' :: rest') W' μ' ∧ Q (n - j) w' e' ρ' := by
  obtain ⟨ρf, hr, hf, hc, hI'⟩ := cactusT_frame hI
  have hcov : CovR w.Θ w.K ρ := cov_of_comp hc hI'
  obtain ⟨w', ρf', ρ', fρ', g₀, g₁, g₂, g₃, g₄, g₅⟩ :=
    h w ρ ρf W μ (TWd.Ext.refl _) (RR.refl hcov) (hF ρf hr) hf hc hI' hfd j μ' e' hj hrun hfin
  obtain ⟨rest', h₁, h₂⟩ := CompAllT.reread g₀ g₄.2.1.monoΘ hr (covf_of_comp hc hI') g₁
  exact ⟨w', ρ', fρ', rest', g₀, h₁, ⟨.cons h₂ (ResUT.CompS.comm g₃), g₄⟩, g₅⟩

/-- **The tree grows under every branch**: a fresh child or a graft, the world re-read, every
branch re-read. -/
theorem cactusT_extend {w w' : TWd} (hE : w.Ext w') (hM : MonoUp w'.Θ) {bs : List (TRes w.K)}
    {W : TRes w.K} {μ : Heap} (h : CactusInvT w bs W μ) :
    ∃ (bs' : List (TRes w'.K)) (W' : TRes w'.K),
      List.Forall₂ (fun a b => RRw (w := w) (w' := w') a b) bs bs' ∧ CactusInvT w' bs' W' μ := by
  obtain ⟨W', hr, hI'⟩ := h.2.reread hE hM
  obtain ⟨bs', h₁, h₂⟩ := CompAllT.reread hE hM.monoΘ h.1 h.2.1 hr
  exact ⟨bs', W', h₁, h₂, hI'⟩

/-- **The scheduler moves a part between branches**: `σ` leaves the first branch for the second;
the world and the memory are unchanged. -/
theorem cactusT_move {w : TWd} {ρ₁ ρ₂ σ ρ₁' ρ₂' : TRes w.K} {rest : List (TRes w.K)}
    {W : TRes w.K} {μ : Heap} (h₁ : ResUT.CompS ρ₁' σ ρ₁) (h₂ : ResUT.CompS ρ₂ σ ρ₂')
    (hI : CactusInvT w (ρ₁ :: ρ₂ :: rest) W μ) : CactusInvT w (ρ₁' :: ρ₂' :: rest) W μ := by
  obtain ⟨hC, hI'⟩ := hI
  cases hC with
  | cons hr hc =>
  cases hr with
  | cons hr' hc' =>
  rename_i W₁ W₂
  obtain ⟨x, hx, hW⟩ := (ResUT.CompS.assoc ρ₁' σ W₁ W).mpr ⟨ρ₁, h₁, hc⟩
  obtain ⟨y, hy, hyx⟩ := (ResUT.CompS.assoc σ ρ₂ W₂ x).mp ⟨W₁, hc', hx⟩
  obtain rfl := ResUT.CompS.functional hy (ResUT.CompS.comm h₂)
  exact ⟨.cons (.cons hr' hyx) hW, hI'⟩

/-! ### Adequacy -/

/-- `⟦∅⟧` is the empty memory. -/
theorem lower_emptyT {K : WCactus} :
    ResUT.Lower (PMap.empty : TRes K) (fun _ => none) :=
  ⟨PMap.empty, ⟨PMap.empty, PMap.empty, exW_empty, agW_empty, G.comp_empty_right _⟩,
    fun _ => by simp⟩

/-- The empty world at any tree and the empty store typing. -/
theorem winv_empty (P : ParentFn) :
    WInv ⟨P, fun _ => none⟩ (PMap.empty : TRes (WCactus.ofParent P)) (fun _ => none) :=
  ⟨fun _ _ e => by simp at e, fun _ _ e => by simp at e, lower_emptyT⟩

/-- Nothing stops at the empty table. -/
def OpTabT.empty : OpTabT := fun _ _ => none

theorem opTableT_empty_false {F : TFrame} {k : Nat} {w : TWd} {t : Expr} {Ψ : ContT}
    {ρ : TRes w.K} (h : opTableT OpTabT.empty F k w t Ψ ρ) : False := by
  obtain ⟨_, _, _, _, _, _, _, h, _⟩ := h
  simp [OpTabT.empty] at h

/-- **Adequacy at `cerwpT`, from the invariant**: a closed program at the empty table, from the
empty world at a tree `P`, under the frame condition "the frame is empty", whose result holds
nothing, is safe or diverges, a value only at the empty memory, every `free` finding its cell. -/
theorem cerwpT_adequacy (P : ParentFn) {Q : TPostV} {P₀ : Expr}
    (hQ : ∀ k w v ρ, Q k w v ρ → ρ = PMap.empty)
    (hall : ∀ n, cerwpT (ℍ := ℍ) (opTableT OpTabT.empty) Q (fun _ ρf => ρf = PMap.empty) n
      ⟨P, fun _ => none⟩ P₀ (PMap.empty : TRes (WCactus.ofParent P))) :
    BoCa.Fig16.LogRel.Core.DtorUnwind.LoopAwait.OrDiverges (ℍ := ℍ) P₀ := by
  intro μ e hs
  obtain ⟨j, hrun⟩ := stepsN_of_steps hs
  have hI₀ : CactusInvT ⟨P, fun _ => none⟩ [PMap.empty] PMap.empty (fun _ => none) :=
    ⟨.cons .nil (ResUT.compS_empty_right _), winv_empty P⟩
  have hend : Final (ℍ := ℍ) μ e → ∃ v : Val, e = v.1 ∧ μ = fun _ => none := by
    intro hfin
    have h := hall (j + 1)
    rw [cerwpT_eq] at h
    obtain ⟨w', ρ', W', rest', -, hrest, ⟨hC, hI'⟩, hq⟩ :=
      cactusT_step h hI₀ (fun ρf hr => by cases hr; rfl) fd_empty (by omega) hrun hfin
    cases hrest
    rcases hq with ⟨v, rfl, hq⟩ | ht
    · obtain rfl := hQ _ _ _ _ hq
      cases hC with
      | cons hr hc =>
          cases hr
          obtain rfl := ResUT.CompS.functional hc (ResUT.compS_empty_right _)
          exact ⟨v, rfl, ResUT.Lower.functional hI'.2.2 lower_emptyT⟩
    · exact (opTableT_empty_false ht).elim
  have hp : IsVal e ∨ ∃ μ' e', Step1 (ℍ := ℍ) μ e μ' e' := by
    by_cases hst : ∃ μ' e', Step1 (ℍ := ℍ) μ e μ' e'
    · exact .inr hst
    · have hfin : Final (ℍ := ℍ) μ e := fun μ' e' h => hst ⟨μ', e', h⟩
      obtain ⟨v, rfl, -⟩ := hend hfin
      exact .inl v.2
  refine ⟨hp, fun hv => ?_, fun K ℓ he => ?_⟩
  · have hfin : Final (ℍ := ℍ) μ e := fun μ' e' h => BoLo.no_step_val (w := ⟨e, hv⟩) h
    obtain ⟨-, -, hμ⟩ := hend hfin
    exact hμ
  · subst he
    rcases hp with hv | ⟨μ', e', hst⟩
    · have := K.isVal_of_plug hv
      simp [freeE, Expr.val, Val.prim] at this
    · obtain ⟨u, hu, -, -⟩ := (step1_free_iff K ℓ).1 hst
      exact ⟨u, hu⟩

end BoCa.Fig16.Tree.Wp

end
