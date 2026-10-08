import ProbeD1.R1Thaw

/-!
# ProbeD1 — `binder0`'s monotonicity at `vRLM` (`R1MONO.md` §2)

* **The record half, by construction** (`monoExtME0`, `monoExtM0`): a value at `binder0` moves
  along an extension of the list that keeps the tags, at every type, under an environment
  (`EnvExt`). At `U` the clause's quantifier over extensions of the instantiated list absorbs the
  step: an extension of `ι.recs ls'` keeping the tags is one of `ι.recs ls` (`extInstT`). At `μ` by
  the fixed point's own induction, as the thaw.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace ProbeD1
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open GhostEnd (LEnt LStack LKind extS vwE vwS vis stratS ReLend TabAtS jdgCty innerView)
open BoCa.BoLo (Step1N Head Heap Kont Alloc AHead AStep1 ARun)

/-! ### Extensions keeping the tags -/

theorem KeepsT.trans {ls ls' ls'' : List SRec} {ρ : WRes} (h₁ : KeepsT ls ls' ρ)
    (h₂ : KeepsT ls' ls'' ρ) : KeepsT ls ls'' ρ :=
  fun x hx hr => h₂ x (h₁ x hx hr) hr

/-- **`ExtInstT`**: an extension keeping the tags is one between the instantiated lists, at a
resource above the outermost lend. A relevant record is kept by `KeepsT`, so its image is in the
instantiated extension; a record longer-lived than a cell of the resource is above the outermost
lend, fixed by the instantiation (`mem_recs_iff_of_lt`). -/
theorem extInstT : ExtInstT := by
  intro ls ls' ρ αs ι hat hz he hkt
  have hkt' : KeepsT (ι.recs ls) (ι.recs ls') ρ := by
    intro x hx hr
    obtain ⟨y, hy, rfl⟩ := Inst.mem_recs.mp hx
    exact Inst.mem_recs.mpr ⟨y, hkt y hy ((rel_rec1 ι y ρ).mp hr), rfl⟩
  refine ⟨⟨fun r hr hrel => ?_, fun b hb x hx => ?_⟩, hkt'⟩
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
    exact List.mem_map_of_mem (hkt' x hx hrel)
  · have hlast : ∀ o ∈ αs.getLast?, o < x.2 := fun o ho => lt_trans (lt_of_cellIn hz hb ho) hx
    exact (mem_recs_iff_of_lt hat hlast).trans
      ((he.2 b hb x hx).trans (mem_recs_iff_of_lt hat hlast).symm)

/-- W's view of one entry along `Ext`: GhostEnd's `vwE_local`, the exactness unchanged. -/
theorem vwEW_local {s : LSub} {e : LEnt} {d : Bool} {α : Life} {ls ls' : List SRec} {ρ : WRes}
    (hk : Ext ls ls' ρ) (h : vwEW s e d α ls ρ) : vwEW s e d α ls' ρ :=
  ⟨GhostEnd.vwE_local hk h.1, h.2⟩

/-- W's views of a stack along `Ext`. -/
theorem vwSW_local {s : LSub} : ∀ {seen : List BoCa.Loc} {σ : LStack} {ds : List Bool}
    {αs : List Life} {ls ls' : List SRec} {ρ : WRes}, Ext ls ls' ρ → vwSW s seen σ ds αs ls ρ →
      vwSW s seen σ ds αs ls' ρ
  | _, [], [], [], _, _, _, _, h => h
  | _, _ :: _, _ :: _, _ :: _, _, _, _, hk, ⟨a, b, hc, ha, hb⟩ =>
      ⟨a, b, hc, vwEW_local (hk.left hc) ha, vwSW_local (hk.right hc) hb⟩
  | _, [], [], _ :: _, _, _, _, _, h => h.elim
  | _, [], _ :: _, [], _, _, _, _, h => h.elim
  | _, [], _ :: _, _ :: _, _, _, _, _, h => h.elim
  | _, _ :: _, [], [], _, _, _, _, h => h.elim
  | _, _ :: _, [], _ :: _, _, _, _, _, h => h.elim
  | _, _ :: _, _ :: _, [], _, _, _, _, h => h.elim

/-! ### The record half at `U` -/

/-- **A `U` value moves along an extension keeping the tags**, at `binder0`: the retained part's
extensions of the instantiated list compose through `extInstT`; the dropped views' records are kept
by `KeepsT`; the views are read at the new list (`vwSW_local`), the guard's at the new list given by
the clause's own guard. -/
theorem vRLM_thunk_ext {C : CTy} {η η' : Option (Nat → WEnt)} {σ : LStack} {δ : LSub}
    {αs : List Life} {ls ls' : List SRec} {f : Val} {ρ : WRes} (he : Ext ls ls' ρ)
    (hkt : KeepsT ls ls' ρ) (ht : TabAtS σ αs ρ) (hpv : PlaceViewsL (extS δ σ αs) σ αs ls ρ)
    (h : vRLM (ℍ := ℍ) .binder0 η σ δ (.thunk C) αs ls f ρ) :
    vRLM (ℍ := ℍ) .binder0 η' σ δ (.thunk C) αs ls' f ρ := by
  rw [vRLM_thunk0] at h ⊢
  intro _ hpv'
  obtain ⟨ds, ρz, ρn, hc, ⟨hn, -⟩, hz, H⟩ := h ht hpv
  refine ⟨ds, ρz, ρn, hc, ⟨vwSW_local (he.right hc) hn, placeViewsL_right hc hpv'⟩, hz,
    fun ι hat ls₂ he₂ hkt₂ hks₂ hro₂ ρv τ hv hcv => ?_⟩
  obtain ⟨heI, hktI⟩ := extInstT ls ls' ρz αs ι hat hz (he.left hc) (hkt.left hc)
  refine H ι hat ls₂ (heI.trans he₂) (hktI.trans hkt₂) (fun x hx hr => ?_) hro₂ ρv τ hv hcv
  obtain ⟨y, hy, rfl⟩ := Inst.mem_recs.mp hx
  have hy' : y ∈ ls' := KeepsT.right hc hkt y hy ((rel_rec1 ι y ρn).mp hr)
  exact hks₂ (ι.rec1 y) (Inst.mem_recs.mpr ⟨y, hy', rfl⟩) hr

/-! ### The record half at every type, under an environment -/

/-- **`MonoExtME binder0`, by induction on the type**: `U` by `vRLM_thunk_ext`; the leaves by
`vC_local`, `CohS` and `RetainedPay` reading no list; a variable by `EnvExt`; `[L]` element by
element (`sepRange_mono_down`, the hypotheses kept at parts); `μ` by the fixed point at the
candidate "a `μ` value that moves", closed by the induction hypothesis at the body under the
extended environments. -/
theorem monoExtME_go : ∀ (A : VTy) (η η' : Option (Nat → WEnt)) (σ : LStack) (δ : LSub)
    (αs : List Life) (ls ls' : List SRec) (v : Val) (ρ : WRes),
    EnvExt η η' σ δ αs ls ls' → StackOK σ αs → OuterBelowTop αs → RecsOutside αs ls →
    RecsOutside αs ls' → Ext ls ls' ρ → KeepsT ls ls' ρ → TabAtS σ αs ρ →
    PlaceViewsL (extS δ σ αs) σ αs ls ρ →
    vRLM (ℍ := ℍ) .binder0 η σ δ A αs ls v ρ → vRLM (ℍ := ℍ) .binder0 η' σ δ A αs ls' v ρ := by
  intro A
  induction A using VTy.recV with
  | thunk C =>
      intro η η' σ δ αs ls ls' v ρ _ _ _ _ _ he hkt ht hpv h
      exact vRLM_thunk_ext he hkt ht hpv h
  | tensor A B ihA ihB =>
      intro η η' σ δ αs ls ls' v ρ hE hok hob hro hro' he hkt ht hpv h
      obtain ⟨v₁, v₂, hsep⟩ := h
      obtain ⟨rfl, ρ₁, ρ₂, hc, h₁, h₂⟩ := pure_sep_iff.mp hsep
      exact ⟨v₁, v₂, pure_sep_mk rfl ⟨ρ₁, ρ₂, hc,
        ihA η η' σ δ αs ls ls' v₁ ρ₁ hE hok hob hro hro' (he.left hc) (hkt.left hc)
          (tabAtS_left hc ht) (placeViewsL_left hc hpv) h₁,
        ihB η η' σ δ αs ls ls' v₂ ρ₂ hE hok hob hro hro' (he.right hc) (hkt.right hc)
          (tabAtS_right hc ht) (placeViewsL_right hc hpv) h₂⟩⟩
  | sum A B ihA ihB =>
      intro η η' σ δ αs ls ls' v ρ hE hok hob hro hro' he hkt ht hpv h
      rcases h with ⟨v₁, hsep⟩ | ⟨v₂, hsep⟩
      · obtain ⟨rfl, h₁⟩ := pure_sep_iff.mp hsep
        exact Or.inl ⟨v₁, pure_sep_mk rfl
          (ihA η η' σ δ αs ls ls' v₁ ρ hE hok hob hro hro' he hkt ht hpv h₁)⟩
      · obtain ⟨rfl, h₂⟩ := pure_sep_iff.mp hsep
        exact Or.inr ⟨v₂, pure_sep_mk rfl
          (ihB η η' σ δ αs ls ls' v₂ ρ hE hok hob hro hro' he hkt ht hpv h₂)⟩
  | bang A ih =>
      intro η η' σ δ αs ls ls' v ρ hE hok hob hro hro' he hkt ht hpv h
      exact ⟨h.1, ih η η' σ δ αs ls ls' v ρ hE hok hob hro hro' he hkt ht hpv h.2⟩
  | box a A ih =>
      intro η η' σ δ αs ls ls' v ρ hE hok hob hro hro' he hkt ht hpv h
      obtain ⟨α, hα, hv, hout⟩ := h
      exact ⟨α, hα, ih η η' σ δ αs ls ls' v ρ hE hok hob hro hro' he hkt ht hpv hv, hout⟩
  | ref A ih =>
      intro η η' σ δ αs ls ls' v ρ hE hok hob hro hro' he hkt ht hpv h
      obtain ⟨ℓ, v', hsep⟩ := h
      obtain ⟨rfl, ρo, ρa, hc, hown, ha⟩ := pure_sep_iff.mp hsep
      exact ⟨ℓ, v', pure_sep_mk rfl ⟨ρo, ρa, hc, hown,
        ih η η' σ δ αs ls ls' v' ρa hE hok hob hro hro' (he.right hc) (hkt.right hc)
          (tabAtS_right hc ht) (placeViewsL_right hc hpv) ha⟩⟩
  | «mut» a T _ =>
      intro η η' σ δ αs ls ls' v ρ hE _ _ _ _ he _ _ _ h
      rw [vRLM_mut_eq, vRLJ_mut_eq] at h ⊢
      rw [wClose_congr hE.1]
      exact ⟨vC_local true _ he h.1, h.2.1, h.2.2⟩
  | imm a T _ =>
      intro η η' σ δ αs ls ls' v ρ hE _ _ _ _ he _ _ _ h
      rw [vRLM_imm_eq, vRLJ_imm_eq] at h ⊢
      rw [wClose_congr hE.1]
      exact ⟨vC_local true _ he h.1, h.2.1, h.2.2⟩
  | unit =>
      intro η η' σ δ αs ls ls' v ρ _ _ _ _ _ he _ _ _ h
      exact vC_local true .unit he h
  | int w =>
      intro η η' σ δ αs ls ls' v ρ _ _ _ _ _ he _ _ _ h
      exact vC_local true (.int w) he h
  | opq k =>
      intro η η' σ δ αs ls ls' v ρ _ _ _ _ _ he _ _ _ h
      exact vC_local true (.opq k) he h
  | unk =>
      intro η η' σ δ αs ls ls' v ρ _ _ _ _ _ he _ _ _ h
      exact vC_local true .unk he h
  | zero =>
      intro η η' σ δ αs ls ls' v ρ _ _ _ _ _ _ _ _ _ h
      exact h.elim
  | tvar n =>
      intro η η' σ δ αs ls ls' v ρ hE _ _ _ _ he hkt ht hpv h
      exact hE.2 n v ρ he hkt ht hpv h
  | fam L ih =>
      intro η η' σ δ αs ls ls' v ρ hE hok hob hro hro' he hkt ht hpv h
      obtain ⟨ℓ, c, hsep⟩ := h
      obtain ⟨⟨rfl, hcn⟩, hs⟩ := pure_sep_iff.mp hsep
      refine ⟨ℓ, c, pure_sep_mk ⟨rfl, hcn⟩ ?_⟩
      refine sepRange_mono_down
        (R := fun τ => Ext ls ls' τ ∧ KeepsT ls ls' τ ∧ TabAtS σ αs τ ∧
          PlaceViewsL (extS δ σ αs) σ αs ls τ)
        (fun a₁ a₂ a hc hR => ⟨⟨hR.1.left hc, hR.2.1.left hc, tabAtS_left hc hR.2.2.1,
          placeViewsL_left hc hR.2.2.2⟩, ⟨hR.1.right hc, hR.2.1.right hc,
          tabAtS_right hc hR.2.2.1, placeViewsL_right hc hR.2.2.2⟩⟩)
        (fun m τ hR hm => ih η η' σ δ αs ls ls' (.loc m) τ hE hok hob hro hro' hR.1 hR.2.1
          hR.2.2.1 hR.2.2.2 hm) ⟨he, hkt, ht, hpv⟩ hs
  | mu A ih =>
      intro η η' σ δ αs ls ls' v ρ hE hok hob hro hro' he hkt ht hpv h
      obtain ⟨hnm, hcl, hlfp⟩ := h
      let P' : Val → WProp := fun v ρ => vRLM (ℍ := ℍ) .binder0 η σ δ (.mu A) αs ls v ρ ∧
        (Ext ls ls' ρ → KeepsT ls ls' ρ → TabAtS σ αs ρ → PlaceViewsL (extS δ σ αs) σ αs ls ρ →
          vRLM (ℍ := ℍ) .binder0 η' σ δ (.mu A) αs ls' v ρ)
      have hE₁ : EnvExt (some (VTy.scons ⟨wClose η (.mu A), P'⟩ (wEnv η)))
          (some (VTy.scons ⟨wClose η' (.mu A), vRLM (ℍ := ℍ) .binder0 η' σ δ (.mu A) αs ls'⟩
            (wEnv η'))) σ δ αs ls ls' := by
        refine ⟨fun n => ?_, fun n v'' ρ'' he'' hkt'' ht'' hpv'' hP => ?_⟩
        · cases n with
          | zero => exact wClose_congr hE.1 _
          | succ n => exact hE.1 n
        · cases n with
          | zero => exact hP.2 he'' hkt'' ht'' hpv''
          | succ n =>
              have hP' : wEnvP η n v'' ρ'' := by rw [wEnvP_eq]; exact hP
              have := hE.2 n v'' ρ'' he'' hkt'' ht'' hpv'' hP'
              rw [wEnvP_eq] at this
              exact this
      have hclosed : ∀ v' ρ', vRLM (ℍ := ℍ) .binder0
          (some (VTy.scons ⟨wClose η (.mu A), P'⟩ (wEnv η))) σ δ A αs ls v' ρ' → P' v' ρ' := by
        intro v' ρ' h'
        refine ⟨?_, fun he' hkt' ht' hpv' => ?_⟩
        · refine vRLM_roll hnm hcl ?_
          refine vRLM_mono_at .binder0 A 0 (VTy.scons ⟨wClose η (.mu A), P'⟩ (wEnv η))
            (VTy.scons ⟨wClose η (.mu A), vRLM (ℍ := ℍ) .binder0 η σ δ (.mu A) αs ls⟩ (wEnv η)) hnm
            (fun n => by cases n <;> rfl) (fun n hn => ?_)
            (fun v'' ρ'' (hv : P' v'' ρ'') => hv.1) σ δ αs ls v' ρ' h'
          cases n with
          | zero => exact absurd rfl hn
          | succ n => rfl
        · refine vRLM_roll hnm (by rw [wClose_congr hE.1]; exact hcl) ?_
          exact ih _ _ σ δ αs ls ls' v' ρ' hE₁ hok hob hro hro' he' hkt' ht' hpv' h'
      exact (hlfp P' hclosed).2 he hkt ht hpv

/-- **`MonoExtME binder0`.** -/
theorem monoExtME0 : MonoExtME (ℍ := ℍ) .binder0 := monoExtME_go

/-- **`EnvExtNone`**: at `none` both types are `.tvar n` and `wEnvP none` is `False`. -/
theorem envExtNone : EnvExtNone :=
  fun _ _ _ _ _ => ⟨fun _ => rfl, fun _ _ _ _ _ _ _ h => absurd h id⟩

/-- **`MonoExtMOfE`.** -/
theorem monoExtMOfE : MonoExtMOfE (ℍ := ℍ) :=
  fun _ hE σ δ A αs ls ls' v ρ hok hob hro hro' he hkt ht hpv h =>
    hE A none none σ δ αs ls ls' v ρ (envExtNone σ δ αs ls ls') hok hob hro hro' he hkt ht hpv h

/-- **`MonoExtM binder0`**: every value at `binder0` moves along an extension keeping the tags. -/
theorem monoExtM0 : MonoExtM (ℍ := ℍ) .binder0 := monoExtMOfE .binder0 monoExtME0


/-! ### Across the own push, at a value reaching no `U`

A leaf's `CohS` at the pushed stack reads the old entries at the pushed reading, which binds the
pushed variable over the old one. `TyEq` of the leaf's payload type and an old entry's then needs
the pushed variable free in neither. The leaf's type is the slot's (`CtxFresh`); the entry's is
not in `MonoOwnUFreeME`'s hypotheses. It is `StackPayAvoids`, added here; every index `SemSM`
reads gives it (`stackPayAvoids_of_stackJ`). -/

/-- **The pushed variable is free in no payload type of the stack's entries.** -/
def StackPayAvoids (x : LifeVar) (σ : LStack) : Prop := ∀ e' ∈ σ, ¬ VFree x e'.T

/-- **`StackPayAvoids` at every index `SemSM` reads**: `StackJ` reads an entry's payload type at
`Δ`'s variables and the stack's, and the own lend's variable is new to both. -/
theorem stackPayAvoids_of_stackJ {σ : LStack} {αs : List Life} {δ : LSub} {Δ : LifeCtx}
    {Γ : Ctx VTy} {C : CTy} {x : LifeVar} (hJ : StackJ σ αs δ Δ Γ C) (hΔ : Δ.find? x = none)
    (hσ : x ∉ σ.map LEnt.x) : StackPayAvoids x σ := by
  intro e' he' hx
  rcases hJ.2.1 e' he' x hx with ⟨u, hu⟩ | hm
  · rw [hΔ] at hu; exact absurd hu (by simp)
  · exact hσ hm

/-- `MonoOwnUFreeME` with `StackPayAvoids`. -/
def MonoOwnUFreeMEA (p : Placement) : Prop :=
  ∀ (A : VTy) (η η' : Option (Nat → WEnt)) (σ : LStack) (δ : LSub) (αs : List Life)
    (ls : List SRec) (v : Val) (ρ : WRes) (C : CTy) (e : LEnt) (a : Life),
    StackPayAvoids e.x σ →
    UFreeM A → EnvPush η η' σ δ αs ls e a → StackOK σ αs → OuterBelowTop αs →
    RecsOutside αs ls → SubOutside σ αs δ → OwnPushI δ C ρ (σ, αs) e a → δ.find? e.x = none →
    ¬ VFree e.x A → e.x ∉ VTy.binders A → RecsOutside (a :: αs) ls → SubFresh δ a →
    TabAtS σ αs ρ → PlaceViewsL (extS δ σ αs) σ αs ls ρ →
    vRLM (ℍ := ℍ) p η σ δ A αs ls v ρ → vRLM (ℍ := ℍ) p η' (e :: σ) δ A (a :: αs) ls v ρ

/-- `MonoOwnGUFreeM` with `StackPayAvoids`. -/
def MonoOwnGUFreeMA (p : Placement) : Prop :=
  ∀ (σ : LStack) (δ : LSub) (Γ : Ctx VTy) (γ : List Val) (αs : List Life) (ls : List SRec)
    (ρ : WRes) (C : CTy) (e : LEnt) (a : Life),
    StackPayAvoids e.x σ →
    (∀ s ∈ Γ, s.live = true → UFreeM s.ty) →
    StackOK σ αs → OuterBelowTop αs → RecsOutside αs ls → SubOutside σ αs δ →
    OwnPushI δ C ρ (σ, αs) e a → δ.find? e.x = none → CtxFresh e.x Γ →
    RecsOutside (a :: αs) ls → SubFresh δ a →
    TabAtS σ αs ρ → PlaceViewsL (extS δ σ αs) σ αs ls ρ →
    gRLM (ℍ := ℍ) p σ δ αs ls Γ γ ρ → gRLM (ℍ := ℍ) p (e :: σ) δ (a :: αs) ls Γ γ ρ

/-- **`RetainedPay` across a lend pushed fresh below the reading** (`RetainedPayPush`). Onto a
non-empty stack the cut is the same and the reading agrees off the pushed variable; onto the empty
stack the cut appears just above the pushed lend, and every value of the reading is above it
(`SubFresh`). -/
theorem retainedPayPush : RetainedPayPush := by
  intro σ αs δ e a T v hok _ hsf hx _ h l' hv hi
  rw [innerAt_cons] at hi
  have hne : e.l ≠ l' := fun he => by rw [if_pos he] at hi; exact absurd hi (by simp)
  rw [if_neg hne] at hi
  intro y hy m hm hint
  have hyx : e.x ≠ y := fun he => hx (he ▸ hy)
  rw [extS_push_find δ e σ a αs hyx] at hm
  cases σ with
  | nil =>
      have hαs : αs = [] := List.length_eq_zero_iff.mp (by simpa using hok.1)
      subst hαs
      have hmem : (y, m) ∈ δ.entries := assocFind_mem hm
      have hlt : a < OrderDual.toDual m := hsf (y, m) hmem
      obtain ⟨c, hc, hlt'⟩ := hint
      have hc' : c = OrderDual.toDual (OrderDual.ofDual a - 1) := by
        simpa [cutOf] using hc.symm
      subst hc'
      exact absurd hlt' (not_lt.mpr (cut_le_of_lt hlt))
  | cons e₀ σ₀ =>
      obtain ⟨α₀, αs₀, rfl⟩ : ∃ α₀ αs₀, αs = α₀ :: αs₀ := by
        cases αs with
        | nil => exact absurd hok.1 (by simp)
        | cons α₀ αs₀ => exact ⟨α₀, αs₀, rfl⟩
      refine h l' hv hi y hy m hm ?_
      obtain ⟨c, hc, hlt'⟩ := hint
      refine ⟨c, ?_, hlt'⟩
      have : (a :: α₀ :: αs₀).getLast? = (α₀ :: αs₀).getLast? := List.getLast?_cons_cons
      simp only [cutOf, this] at hc ⊢
      exact hc

/-- `TyEq` across one variable bound on both sides, free in neither type. -/
theorem tyEq_extend_both {S S' : VTy} {δ δ' : LSub} {x : LifeVar} (hx : ¬ VFree x S)
    (hx' : ¬ VFree x S') (β : Life) (h : TyEq S δ S' δ') :
    TyEq S (δ.extend x β) S' (δ'.extend x β) :=
  (TyEq.extend_left hx' β (TyEq.extend_left hx β h).symm).symm

/-- **`CohS` across the own push** at a leaf away from the pushed place: the innermost entry lending
the leaf's place is the old one, read at the pushed reading. -/
theorem cohS_push {σ : LStack} {αs : List Life} {s : LSub} {e : LEnt} {a : Life} {A : VTy}
    {l : BoCa.Loc} {ρ : WRes} (hne : e.l ≠ l)
    (hA : ∀ (b : Lifetime.Life) (T : VTy), (A = .mut b T ∨ A = .imm b T) → ¬ VFree e.x T)
    (hσ : StackPayAvoids e.x σ) (h : CohS σ αs s A (.loc l) ρ) :
    CohS (e :: σ) (a :: αs) (s.extend e.x a) A (.loc l) ρ := by
  intro l' e' α' hl' hi
  cases hl'
  rw [innerAt_cons, if_neg hne] at hi
  obtain ⟨hk, hat⟩ := h l e' α' rfl hi
  have he' : e' ∈ σ := (List.of_mem_zip (innerAt_mem hi).1).1
  refine ⟨?_, hat⟩
  cases A with
  | «mut» b T =>
      exact ⟨hk.1, tyEq_extend_both (hA b T (Or.inl rfl)) (hσ e' he') a hk.2⟩
  | imm b T =>
      exact ⟨hk.1, tyEq_extend_both (hA b T (Or.inr rfl)) (hσ e' he') a hk.2⟩
  | unit | zero | unk | int _ | opq _ | tvar _ | tensor _ _ | sum _ _ | thunk _ | bang _
  | box _ _ | ref _ | mu _ | fam _ => exact hk.elim

/-- A closed type reads the pushed variable when its type or the environment's do. -/
theorem not_vFree_wClose {η : Option (Nat → WEnt)} {x : LifeVar} {T : VTy} (hT : ¬ VFree x T)
    (hη : ∀ n, ¬ VFree x (wEnv η n).ty) : ¬ VFree x (wClose η T) := by
  rw [wClose_eq]
  intro h
  rcases vFree_subst T _ h with h | ⟨n, hn⟩
  · exact hT h
  · exact hη n hn

/-- **The leaf at the pushed stack**: Core's leaf at the pushed reading (`vC_congr`), `CohS` by
`cohS_push`, `RetainedPay` by `retainedPayPush`. -/
theorem vRLJ_leaf_push {p : Placement} {σ : LStack} {δ : LSub} {αs : List Life} {ls : List SRec}
    {e : LEnt} {a : Life} {A : VTy} {v : Val} {ρ : WRes}
    (hA : (∃ b T, A = .mut b T) ∨ (∃ b T, A = .imm b T)) (hx : ¬ VFree e.x A)
    (hok : StackOK σ αs) (hch : List.IsChain (· < ·) (a :: αs)) (hsf : SubFresh δ a)
    (hpf : ∀ ψ, ¬ DeepAt ρ e.l ψ) (hσ : StackPayAvoids e.x σ)
    (h : vRLJ (ℍ := ℍ) p σ δ A αs ls v ρ) : vRLJ (ℍ := ℍ) p (e :: σ) δ A (a :: αs) ls v ρ := by
  have hagree : ∀ y, VFree y A → (extS δ (e :: σ) (a :: αs)).find? y = (extS δ σ αs).find? y :=
    fun y hy => extS_push_find δ e σ a αs (fun he => hx (he ▸ hy))
  rcases hA with ⟨b, T, rfl⟩ | ⟨b, T, rfl⟩
  · rw [vRLJ_mut_eq] at h ⊢
    obtain ⟨hvc, hcoh, hpay⟩ := h
    obtain ⟨α, -, ℓ, hsep⟩ := id hvc
    obtain ⟨rfl, b', u, σ', hσ', Q, hw, ls₀, -, hρ, -⟩ := pure_sep_iff.mp hsep
    have hne : e.l ≠ ℓ := fun he =>
      hpf (CellU.mutOf b' u σ' hσ' Q hw) (DeepAt.top (by rw [he, hρ]; simp))
    have hxT : ¬ VFree e.x T := fun h' => hx (Or.inr h')
    refine ⟨by rw [vC_congr _ hagree]; exact hvc, ?_, retainedPayPush σ αs δ e a T _ hok hch hsf
      hxT (fun l hl => by cases hl; exact Ne.symm hne) hpay⟩
    exact cohS_push hne (fun b'' T'' hb => by
      rcases hb with hb | hb <;> cases hb; exact hxT) hσ hcoh
  · rw [vRLJ_imm_eq] at h ⊢
    obtain ⟨hvc, hcoh, hpay⟩ := h
    obtain ⟨α, -, ℓ, hsep⟩ := id hvc
    obtain ⟨⟨rfl, -⟩, S, u, χ, hχ, ls₀, hρ, -⟩ := pure_sep_iff.mp hsep
    have hne : e.l ≠ ℓ := fun he =>
      hpf (CellU.immOf S u χ hχ) (DeepAt.top (by rw [he, hρ]; simp))
    have hxT : ¬ VFree e.x T := fun h' => hx (Or.inr h')
    refine ⟨by rw [vC_congr _ hagree]; exact hvc, ?_, retainedPayPush σ αs δ e a T _ hok hch hsf
      hxT (fun l hl => by cases hl; exact Ne.symm hne) hpay⟩
    exact cohS_push hne (fun b'' T'' hb => by
      rcases hb with hb | hb <;> cases hb; exact hxT) hσ hcoh


/-- The own lend's facts at a resource hold at its parts. -/
theorem pushFacts_left {σ : LStack} {αs : List Life} {s : LSub} {ls : List SRec} {e : LEnt}
    {a : Life} {ρ₁ ρ₂ ρ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ)
    (h : TabAtS σ αs ρ ∧ PlaceViewsL s σ αs ls ρ ∧ (∀ ψ, ¬ DeepAt ρ e.l ψ) ∧ ρ.InStratum a) :
    TabAtS σ αs ρ₁ ∧ PlaceViewsL s σ αs ls ρ₁ ∧ (∀ ψ, ¬ DeepAt ρ₁ e.l ψ) ∧ ρ₁.InStratum a :=
  ⟨tabAtS_left hc h.1, placeViewsL_left hc h.2.1, fun ψ hd => by
    obtain ⟨ψ', hd', -⟩ := DeepAt.of_compS_left hc hd
    exact h.2.2.1 ψ' hd', ((outlives_comp hc a).mp h.2.2.2).1⟩

theorem pushFacts_right {σ : LStack} {αs : List Life} {s : LSub} {ls : List SRec} {e : LEnt}
    {a : Life} {ρ₁ ρ₂ ρ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ)
    (h : TabAtS σ αs ρ ∧ PlaceViewsL s σ αs ls ρ ∧ (∀ ψ, ¬ DeepAt ρ e.l ψ) ∧ ρ.InStratum a) :
    TabAtS σ αs ρ₂ ∧ PlaceViewsL s σ αs ls ρ₂ ∧ (∀ ψ, ¬ DeepAt ρ₂ e.l ψ) ∧ ρ₂.InStratum a :=
  pushFacts_left (ResU.CompS.comm hc) h

/-- **A value reaching no `U`, carried across the own push**, under an environment
(`MonoOwnUFreeMEA`'s induction): the leaves by `vRLJ_leaf_push`, a box's bound read off the old
reading (the pushed variable is not in it), a variable by `EnvPush`, `[L]` element by element, `μ`
by the fixed point at the candidate "a `μ` value that crosses the push under the guard". -/
theorem monoOwnUFree_go (p : Placement) (e : LEnt) (a : Life) : ∀ (A : VTy)
    (η η' : Option (Nat → WEnt)) (σ : LStack) (δ : LSub) (αs : List Life) (ls : List SRec)
    (v : Val) (ρ : WRes),
    UFreeM A → EnvPush η η' σ δ αs ls e a → StackOK σ αs → List.IsChain (· < ·) (a :: αs) →
    SubFresh δ a → StackPayAvoids e.x σ → ¬ VFree e.x A →
    (TabAtS σ αs ρ ∧ PlaceViewsL (extS δ σ αs) σ αs ls ρ ∧ (∀ ψ, ¬ DeepAt ρ e.l ψ) ∧
      ρ.InStratum a) →
    vRLM (ℍ := ℍ) p η σ δ A αs ls v ρ → vRLM (ℍ := ℍ) p η' (e :: σ) δ A (a :: αs) ls v ρ := by
  intro A
  induction A using VTy.recV with
  | thunk C => intro _ _ _ _ _ _ _ _ hu; exact hu.elim
  | tensor A B ihA ihB =>
      intro η η' σ δ αs ls v ρ hu hE hok hch hsf hσ hx hF h
      obtain ⟨v₁, v₂, hsep⟩ := h
      obtain ⟨rfl, ρ₁, ρ₂, hc, h₁, h₂⟩ := pure_sep_iff.mp hsep
      exact ⟨v₁, v₂, pure_sep_mk rfl ⟨ρ₁, ρ₂, hc,
        ihA η η' σ δ αs ls v₁ ρ₁ hu.1 hE hok hch hsf hσ (fun h' => hx (Or.inl h'))
          (pushFacts_left hc hF) h₁,
        ihB η η' σ δ αs ls v₂ ρ₂ hu.2 hE hok hch hsf hσ (fun h' => hx (Or.inr h'))
          (pushFacts_right hc hF) h₂⟩⟩
  | sum A B ihA ihB =>
      intro η η' σ δ αs ls v ρ hu hE hok hch hsf hσ hx hF h
      rcases h with ⟨v₁, hsep⟩ | ⟨v₂, hsep⟩
      · obtain ⟨rfl, h₁⟩ := pure_sep_iff.mp hsep
        exact Or.inl ⟨v₁, pure_sep_mk rfl
          (ihA η η' σ δ αs ls v₁ ρ hu.1 hE hok hch hsf hσ (fun h' => hx (Or.inl h')) hF h₁)⟩
      · obtain ⟨rfl, h₂⟩ := pure_sep_iff.mp hsep
        exact Or.inr ⟨v₂, pure_sep_mk rfl
          (ihB η η' σ δ αs ls v₂ ρ hu.2 hE hok hch hsf hσ (fun h' => hx (Or.inr h')) hF h₂)⟩
  | bang A ih =>
      intro η η' σ δ αs ls v ρ hu hE hok hch hsf hσ hx hF h
      exact ⟨h.1, ih η η' σ δ αs ls v ρ hu hE hok hch hsf hσ hx hF h.2⟩
  | box b A ih =>
      intro η η' σ δ αs ls v ρ hu hE hok hch hsf hσ hx hF h
      obtain ⟨α, hα, hv, hout⟩ := h
      have hb : b.mentions e.x = false := by
        cases hm : b.mentions e.x
        · rfl
        · exact absurd (Or.inl hm) hx
      refine ⟨α, ?_, ih η η' σ δ αs ls v ρ hu hE hok hch hsf hσ (fun h' => hx (Or.inr h')) hF hv,
        hout⟩
      show b.interp ((extS δ σ αs).extend e.x a) = some α
      rw [interp_extend_of_not_mentions hb]; exact hα
  | ref A ih =>
      intro η η' σ δ αs ls v ρ hu hE hok hch hsf hσ hx hF h
      obtain ⟨ℓ, v', hsep⟩ := h
      obtain ⟨rfl, ρo, ρa, hc, hown, ha⟩ := pure_sep_iff.mp hsep
      exact ⟨ℓ, v', pure_sep_mk rfl ⟨ρo, ρa, hc, hown,
        ih η η' σ δ αs ls v' ρa hu hE hok hch hsf hσ hx (pushFacts_right hc hF) ha⟩⟩
  | «mut» b T _ =>
      intro η η' σ δ αs ls v ρ _ hE hok hch hsf hσ hx hF h
      rw [vRLM_mut_eq] at h ⊢
      rw [wClose_congr hE.1]
      refine vRLJ_leaf_push (Or.inl ⟨b, _, rfl⟩) ?_ hok hch hsf hF.2.2.1 hσ h
      rintro (hm | hT)
      · exact hx (Or.inl hm)
      · exact not_vFree_wClose (fun h' => hx (Or.inr h')) hE.2.1 hT
  | imm b T _ =>
      intro η η' σ δ αs ls v ρ _ hE hok hch hsf hσ hx hF h
      rw [vRLM_imm_eq] at h ⊢
      rw [wClose_congr hE.1]
      refine vRLJ_leaf_push (Or.inr ⟨b, _, rfl⟩) ?_ hok hch hsf hF.2.2.1 hσ h
      rintro (hm | hT)
      · exact hx (Or.inl hm)
      · exact not_vFree_wClose (fun h' => hx (Or.inr h')) hE.2.1 hT
  | unit =>
      intro η η' σ δ αs ls v ρ _ _ _ _ _ _ _ _ h
      show vC true .unit ls (extS δ (e :: σ) (a :: αs)) v ρ
      rw [vC_congr .unit (δ₂ := extS δ σ αs) (fun y hy => hy.elim)]; exact h
  | int w =>
      intro η η' σ δ αs ls v ρ _ _ _ _ _ _ _ _ h
      show vC true (.int w) ls (extS δ (e :: σ) (a :: αs)) v ρ
      rw [vC_congr (.int w) (δ₂ := extS δ σ αs) (fun y hy => hy.elim)]; exact h
  | opq k =>
      intro η η' σ δ αs ls v ρ _ _ _ _ _ _ _ _ h
      show vC true (.opq k) ls (extS δ (e :: σ) (a :: αs)) v ρ
      rw [vC_congr (.opq k) (δ₂ := extS δ σ αs) (fun y hy => hy.elim)]; exact h
  | unk =>
      intro η η' σ δ αs ls v ρ _ _ _ _ _ _ _ _ h
      show vC true .unk ls (extS δ (e :: σ) (a :: αs)) v ρ
      rw [vC_congr .unk (δ₂ := extS δ σ αs) (fun y hy => hy.elim)]; exact h
  | zero => intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h; exact h.elim
  | tvar n =>
      intro η η' σ δ αs ls v ρ _ hE _ _ _ _ _ hF h
      exact hE.2.2 n v ρ hF.1 hF.2.1 hF.2.2.1 hF.2.2.2 h
  | fam L ih =>
      intro η η' σ δ αs ls v ρ hu hE hok hch hsf hσ hx hF h
      obtain ⟨ℓ, c, hsep⟩ := h
      obtain ⟨⟨rfl, hcn⟩, hs⟩ := pure_sep_iff.mp hsep
      refine ⟨ℓ, c, pure_sep_mk ⟨rfl, hcn⟩ ?_⟩
      exact sepRange_mono_down
        (R := fun τ => TabAtS σ αs τ ∧ PlaceViewsL (extS δ σ αs) σ αs ls τ ∧
          (∀ ψ, ¬ DeepAt τ e.l ψ) ∧ τ.InStratum a)
        (fun a₁ a₂ a' hc hR => ⟨pushFacts_left hc hR, pushFacts_right hc hR⟩)
        (fun m τ hR hm => ih η η' σ δ αs ls (.loc m) τ hu hE hok hch hsf hσ hx hR hm) hF hs
  | mu A ih =>
      intro η η' σ δ αs ls v ρ hu hE hok hch hsf hσ hx hF h
      obtain ⟨hnm, hcl, hlfp⟩ := h
      let P' : Val → WProp := fun v ρ => vRLM (ℍ := ℍ) p η σ δ (.mu A) αs ls v ρ ∧
        (TabAtS σ αs ρ → PlaceViewsL (extS δ σ αs) σ αs ls ρ → (∀ ψ, ¬ DeepAt ρ e.l ψ) →
          ρ.InStratum a → vRLM (ℍ := ℍ) p η' (e :: σ) δ (.mu A) (a :: αs) ls v ρ)
      have hxM : ¬ VFree e.x (wClose η (.mu A)) := not_vFree_wClose hx hE.2.1
      have hE₁ : EnvPush (some (VTy.scons ⟨wClose η (.mu A), P'⟩ (wEnv η)))
          (some (VTy.scons ⟨wClose η' (.mu A),
            vRLM (ℍ := ℍ) p η' (e :: σ) δ (.mu A) (a :: αs) ls⟩ (wEnv η'))) σ δ αs ls e a := by
        refine ⟨fun n => ?_, fun n => ?_, fun n v'' ρ'' ht'' hpv'' hpf'' hin'' hP => ?_⟩
        · cases n with
          | zero => exact wClose_congr hE.1 _
          | succ n => exact hE.1 n
        · cases n with
          | zero => exact hxM
          | succ n => exact hE.2.1 n
        · cases n with
          | zero => exact hP.2 ht'' hpv'' hpf'' hin''
          | succ n =>
              have hP' : wEnvP η n v'' ρ'' := by rw [wEnvP_eq]; exact hP
              have := hE.2.2 n v'' ρ'' ht'' hpv'' hpf'' hin'' hP'
              rw [wEnvP_eq] at this
              exact this
      have hclosed : ∀ v' ρ', vRLM (ℍ := ℍ) p
          (some (VTy.scons ⟨wClose η (.mu A), P'⟩ (wEnv η))) σ δ A αs ls v' ρ' → P' v' ρ' := by
        intro v' ρ' h'
        refine ⟨?_, fun ht' hpv' hpf' hin' => ?_⟩
        · refine vRLM_roll hnm hcl ?_
          refine vRLM_mono_at p A 0 (VTy.scons ⟨wClose η (.mu A), P'⟩ (wEnv η))
            (VTy.scons ⟨wClose η (.mu A), vRLM (ℍ := ℍ) p η σ δ (.mu A) αs ls⟩ (wEnv η)) hnm
            (fun n => by cases n <;> rfl) (fun n hn => ?_)
            (fun v'' ρ'' (hv : P' v'' ρ'') => hv.1) σ δ αs ls v' ρ' h'
          cases n with
          | zero => exact absurd rfl hn
          | succ n => rfl
        · refine vRLM_roll hnm (by rw [wClose_congr hE.1]; exact hcl) ?_
          exact ih _ _ σ δ αs ls v' ρ' hu hE₁ hok hch hsf hσ hx ⟨ht', hpv', hpf', hin'⟩ h'
      exact (hlfp P' hclosed).2 hF.1 hF.2.1 hF.2.2.1 hF.2.2.2

/-- **`MonoOwnUFreeMEA`, at every placement.** -/
theorem monoOwnUFreeMEA (p : Placement) : MonoOwnUFreeMEA (ℍ := ℍ) p := by
  intro A η η' σ δ αs ls v ρ C e a hσ hu hE hok _ _ _ hpush _ hx _ _ hsf ht hpv h
  obtain ⟨_, _, _, _, _, _, hoi, _, _⟩ := hpush
  exact monoOwnUFree_go p e a A η η' σ δ αs ls v ρ hu hE hok hoi.chain hsf hσ hx
    ⟨ht, hpv, hoi.placeFree, hoi.below⟩ h

/-- **`EnvPushNone`.** -/
theorem envPushNone : EnvPushNone :=
  fun _ _ _ _ _ _ => ⟨fun _ => rfl, fun _ h => h, fun _ _ _ _ _ _ _ h => absurd h id⟩

/-- **`MonoOwnGUFreeMA`, slot by slot**: `monoOwnUFreeMEA` at `none` at each live slot, the own
lend's facts at the slot's part. -/
theorem monoOwnGUFreeMA (p : Placement) : MonoOwnGUFreeMA (ℍ := ℍ) p := by
  intro σ δ Γ γ αs ls ρ C e a hσ hU hok _ _ _ hpush _ hfr _ hsf ht hpv hg
  obtain ⟨_, _, _, _, _, _, hoi, _, _⟩ := hpush
  obtain ⟨hlw, hgs⟩ := pure_sep_iff.mp hg
  refine pure_sep_mk hlw ?_
  have key : ∀ (Γ : Ctx VTy) (γ : List Val) (ρ : WRes),
      (∀ s ∈ Γ, s.live = true → UFreeM s.ty) → CtxFresh e.x Γ →
      (TabAtS σ αs ρ ∧ PlaceViewsL (extS δ σ αs) σ αs ls ρ ∧ (∀ ψ, ¬ DeepAt ρ e.l ψ) ∧
        ρ.InStratum a) →
      gSepRLM (ℍ := ℍ) p σ δ αs ls Γ γ ρ → gSepRLM (ℍ := ℍ) p (e :: σ) δ (a :: αs) ls Γ γ ρ := by
    intro Γ
    induction Γ with
    | nil => intro γ ρ _ _ _ h; cases γ <;> exact h
    | cons s Γ ih =>
        intro γ ρ hU' hfr' hF h
        cases γ with
        | nil => exact h
        | cons v γ =>
            have hU'' : ∀ s' ∈ Γ, s'.live = true → UFreeM s'.ty :=
              fun s' hs' hl => hU' s' (List.mem_cons_of_mem _ hs') hl
            have hfr'' : CtxFresh e.x Γ := fun s' hs' hl => hfr' s' (List.mem_cons_of_mem _ hs') hl
            by_cases hl : s.live = true
            · simp only [gSepRLM, hl, if_true] at h ⊢
              obtain ⟨ρ₁, ρ₂, hc, h₁, h₂⟩ := h
              exact ⟨ρ₁, ρ₂, hc,
                monoOwnUFree_go p e a s.ty none none σ δ αs ls v ρ₁ (hU' s List.mem_cons_self hl)
                  (envPushNone σ δ αs ls e a) hok hoi.chain hsf hσ
                  (hfr' s List.mem_cons_self hl).1 (pushFacts_left hc hF) h₁,
                ih γ ρ₂ hU'' hfr'' (pushFacts_right hc hF) h₂⟩
            · simp only [gSepRLM, hl] at h ⊢
              exact ih γ ρ hU'' hfr'' hF h
  exact key Γ γ ρ hU hfr ⟨ht, hpv, hoi.placeFree, hoi.below⟩ hgs


/-! ### The revised futures at a part, and the instance lemmas -/

/-- One revised step at a resource is one at each part: `FutOK.below` at a part as at W₀, and
`FutOKI.placesFree` since a cell of a part at any depth is one of the whole
(`DeepAt.of_compS_left`). -/
theorem FutStepI.part {δ : LSub} {ρz ρn ρ : WRes} (hc : ResU.CompS ρz ρn ρ) {s s' : Stk}
    (h : FutStepI δ ρ s s') : FutStepI δ ρz s s' := by
  obtain ⟨k, τ, αt, N, hok, h₁, h₂⟩ := h
  refine ⟨k, τ, αt, N, ⟨{ hok.toFutOK with
    below := fun a ha => ResU.CompS.inStratum_left hc (hok.below a ha) }, fun e he ψ hd => ?_⟩,
    h₁, h₂⟩
  obtain ⟨ψ', hd', -⟩ := DeepAt.of_compS_left hc hd
  exact hok.placesFree e he ψ' hd'

/-- **`FutPartI`.** -/
theorem futPartI : FutPartI := fun _ _ _ _ _ _ hc h =>
  Relation.ReflTransGen.mono (fun _ _ h' => FutStepI.part hc h') _ _ h

/-- **The revised own push is a one-step revised future**: `ownPush_futStep` with `placeFree`. -/
theorem ownPushI_futStepI {δ : LSub} {C : CTy} {ρ : WRes} {σ : LStack} {αs : List Life}
    {e : LEnt} {a : Life} (hpush : OwnPushI δ C ρ (σ, αs) e a) (hδ : δ.find? e.x = none) :
    FutStepI δ ρ (σ, αs) (e :: σ, a :: αs) := by
  obtain ⟨x, c, C', -, -, -, hown, -, -⟩ := hpush
  refine ⟨0, [e], [a], none, ⟨?_, fun e' he' ψ => ?_⟩, ?_, ?_⟩
  · exact
      { len := rfl
        depth_le := Nat.zero_le _
        chain := by simpa [futL] using hown.chain
        below := fun b hb => by rw [List.mem_singleton.mp hb]; exact hown.below
        vars_stack := fun e' he' => by rw [List.mem_singleton.mp he']; exact hown.var
        vars_sub := fun e' he' => by
          rw [List.mem_singleton.mp he']
          rw [extS_find_not_mem δ σ αs e.x hown.var]; exact hδ
        nodup := List.nodup_singleton _
        places := fun e' he' => by rw [List.mem_singleton.mp he']; exact hown.place
        pay := fun e' he' y hy => by
          rw [List.mem_singleton.mp he'] at hy
          simpa [futL] using hown.pay y hy }
  · rw [List.mem_singleton.mp he']; exact hown.placeFree ψ
  · show e :: σ = σ.take 0 ++ [e] ++ σ.drop 0
    simp
  · show a :: αs = futL 0 [a] αs
    simp [futL]

/-- **`MonoOwnGMOfMonoGM`**: the own push is a one-step revised future at the list itself, its one
inserted lifetime fresh by the `∀` clause's own-lend conjunct. -/
theorem monoOwnGMOfMonoGM : MonoOwnGMOfMonoGM (ℍ := ℍ) := by
  intro p hG σ δ Γ γ αs ls ρ C e a hok hob hro hso hpush hδ hfr hro' hsf ht hpv hg
  refine hG σ δ Γ γ αs ls ls ρ (e :: σ) (a :: αs) hok hob hro hso (Ext.refl ls ρ)
    (keepsT_refl ls ρ) (Relation.ReflTransGen.single (ownPushI_futStepI hpush hδ))
    ⟨hro', fun a' ha' hn => ?_⟩ ?_ ht hpv hg
  · rcases List.mem_cons.mp ha' with rfl | ha'
    · exact hsf
    · exact absurd ha' hn
  · intro s hs hl e' he' hx
    rcases List.mem_cons.mp he' with rfl | he'
    · exact hfr s hs hl
    · exact absurd (List.mem_map_of_mem he') hx

/-- The separating part of a context follows its values, slot by slot, at `vRLM`. -/
theorem gSepRLM_mono (p : Placement) (hV : MonoVM (ℍ := ℍ) p) {σ σ' : LStack} {δ : LSub}
    {αs αs' : List Life} {ls ls' : List SRec} (hok : StackOK σ αs) (hob : OuterBelowTop αs)
    (hro : RecsOutside αs ls) (hso : SubOutside σ αs δ) (hif : InsertedFresh δ ls' αs αs') :
    ∀ (Γ : Ctx VTy) (γ : List Val) (ρ : WRes), (∀ s ∈ Γ, s.live = true → FutAvoidsV s.ty σ σ') →
      Ext ls ls' ρ → KeepsT ls ls' ρ → FutI δ ρ (σ, αs) (σ', αs') → TabAtS σ αs ρ →
      PlaceViewsL (extS δ σ αs) σ αs ls ρ →
      gSepRLM (ℍ := ℍ) p σ δ αs ls Γ γ ρ → gSepRLM (ℍ := ℍ) p σ' δ αs' ls' Γ γ ρ
  | [], _, _, _, _, _, _, _, _, h => h
  | _ :: _, [], _, _, _, _, _, _, _, h => h
  | s :: Γ, v :: γ, ρ, hav, he, hkt, hf, ht, hpv, h => by
      have hav' : ∀ s' ∈ Γ, s'.live = true → FutAvoidsV s'.ty σ σ' :=
        fun s' hs' hl => hav s' (List.mem_cons_of_mem _ hs') hl
      by_cases hl : s.live = true
      · simp only [gSepRLM, hl, if_true] at h ⊢
        obtain ⟨ρ₁, ρ₂, hc, h₁, h₂⟩ := h
        exact ⟨ρ₁, ρ₂, hc,
          hV σ δ s.ty αs ls ls' v ρ₁ σ' αs' hok hob hro hso (he.left hc) (hkt.left hc)
            (futPartI δ ρ₁ ρ₂ ρ _ _ hc hf) hif (hav s List.mem_cons_self hl) (tabAtS_left hc ht)
            (placeViewsL_left hc hpv) h₁,
          gSepRLM_mono p hV hok hob hro hso hif Γ γ ρ₂ hav' (he.right hc) (hkt.right hc)
            (futPartI δ ρ₂ ρ₁ ρ _ _ (ResU.CompS.comm hc) hf) (tabAtS_right hc ht)
            (placeViewsL_right hc hpv) h₂⟩
      · simp only [gSepRLM, hl] at h ⊢
        exact gSepRLM_mono p hV hok hob hro hso hif Γ γ ρ hav' he hkt hf ht hpv h

/-- **`MonoGMOfMonoVM`.** -/
theorem monoGMOfMonoVM : MonoGMOfMonoVM (ℍ := ℍ) := by
  intro p hV σ δ Γ γ αs ls ls' ρ σ' αs' hok hob hro hso he hkt hf hif hav ht hpv hg
  obtain ⟨hlw, hgs⟩ := pure_sep_iff.mp hg
  exact pure_sep_mk hlw (gSepRLM_mono p hV hok hob hro hso hif Γ γ ρ hav he hkt hf ht hpv hgs)


/-! ### The configuration `gd`: the index -/

/-- The stack's reading at `gd`: `'0 ↦ 2` (the stack), then `gdδ`'s `'1 ↦ 3`, `'0 ↦ 2`. -/
theorem gdS_find (y : LifeVar) : (extS gdδ gdσ gdαs).find? y =
    if y = 0 then some 2 else if y = 1 then some 3 else none := by
  show BoCa.Lifetime.assocFind y [(0, 2), (1, 3), (0, 2)] = _
  by_cases h0 : y = 0
  · subst h0; rfl
  · by_cases h1 : y = 1
    · subst h1; rfl
    · simp [BoCa.Lifetime.assocFind, Ne.symm h0, Ne.symm h1, h0, h1]

theorem gdΔ_find (y : LifeVar) : gdΔ.find? y =
    if y = 1 then some (.var 0) else if y = 0 then some .top else none := by
  by_cases h1 : y = 1
  · subst h1; rfl
  · by_cases h0 : y = 0
    · subst h0; rfl
    · simp [LifeCtx.find?, LifeCtx.extend, LifeCtx.empty, BoCa.Lifetime.assocFind, h0, h1,
        Ne.symm h0, Ne.symm h1]

theorem gd_ownOKI : OwnOKI gdδ gdσ gdαs gdY (lifeN 4) PMap.empty :=
  ⟨⟨by decide, ResU.inStratum_empty _, by decide, by decide, fun y hy => by
      simp [VFree] at hy⟩, fun _ hd => not_deepAt_empty hd⟩

theorem gd_ownPushI : OwnPushI gdδ gdCy PMap.empty (gdσ, gdαs) gdY (lifeN 4) := by
  refine ⟨2, .var 1, .arr (.imm (.var 2) .unit) (.ret .unit), rfl, rfl,
    by simp [CTy.binders, VTy.binders], gd_ownOKI,
    ⟨3, ?_, show OrderDual.toDual (4 : ℕ) < OrderDual.toDual 3 from by decide⟩, fun A D h => ?_⟩
  · show (extS gdδ gdσ gdαs).find? 1 = some 3
    rw [gdS_find]; rfl
  · obtain ⟨rfl, rfl⟩ : A = .imm (.var 2) .unit ∧ D = .ret .unit := by
      simpa using h.symm
    exact ⟨rfl, trivial, rfl⟩

/-- **`GdIndex`**: the configuration meets `MonoOwnGM`'s hypotheses and `SemSM`'s index at the
judgement `gdΔ; gdΓ ⊢ _ : gdCy`. -/
theorem gdIndex : GdIndex := by
  refine ⟨⟨rfl, List.isChain_singleton _, List.nodup_singleton _⟩, fun o ho => ?_,
    fun a ha x hx hlt => ?_, fun e a he p hp => ?_, gd_ownPushI, rfl, fun s hs hl => ?_,
    fun a ha x hx hlt => ?_, fun p hp => ?_, ⟨fun a _ => ResU.inStratum_empty _,
      fun a _ k ψ _ h => by simp at h⟩, placeViewsL_empty, ⟨fun x hx => ?_, fun s hs hl x hx => ?_⟩,
    ⟨fun y hy => ?_, fun s hs hl y hy => ?_⟩, ⟨List.nodup_singleton _, fun e he y hy => ?_,
      fun e he => ?_⟩, fun y hy => ?_, fun x u hx => ?_⟩
  · obtain rfl : o = lifeN 2 := (Option.some.inj ho).symm
    show (0 : ℕ) < 2
    decide
  · obtain rfl : a = lifeN 2 := List.mem_singleton.mp ha
    obtain rfl : x = (gdRec, lifeN 4) := List.mem_singleton.mp hx
    exact absurd hlt (by decide)
  · obtain ⟨rfl, rfl⟩ : e = gdX ∧ a = lifeN 2 := by simpa using he
    simp [boundBefore] at hp
  · obtain rfl : s = ⟨gdTy, true⟩ := List.mem_singleton.mp hs
    refine ⟨fun h => ?_, by simp [VTy.binders, CTy.binders]⟩
    simp [VFree, CFree, Lifetime.Life.mentions] at h
  · obtain rfl : x = (gdRec, lifeN 4) := List.mem_singleton.mp hx
    rcases List.mem_cons.mp ha with rfl | ha
    · exact absurd hlt (lt_irrefl _)
    · obtain rfl : a = lifeN 2 := List.mem_singleton.mp ha
      exact absurd hlt (by decide)
  · rcases List.mem_cons.mp hp with rfl | hp
    · decide
    · obtain rfl := List.mem_singleton.mp hp
      decide
  · simp [CTy.binders, VTy.binders] at hx
    subst hx
    unfold NsVar nsBase
    norm_num
  · obtain rfl : s = ⟨gdTy, true⟩ := List.mem_singleton.mp hs
    simp [VTy.binders, CTy.binders] at hx
  · simp only [CFree, VFree, Lifetime.Life.mentions, beq_iff_eq] at hy
    rcases hy with rfl | ⟨hne, (h | h) | h⟩
    · exact ⟨.var 0, rfl⟩
    · exact absurd h hne
    · exact h.elim
    · exact h.elim
  · obtain rfl : s = ⟨gdTy, true⟩ := List.mem_singleton.mp hs
    simp only [VFree, CFree, Lifetime.Life.mentions, beq_iff_eq] at hy
    rcases hy with h | rfl | h
    · exact h.elim
    · exact ⟨.var 0, rfl⟩
    · exact h.elim
  · obtain rfl : e = gdX := List.mem_singleton.mp he
    exact hy.elim
  · obtain rfl : e = gdX := List.mem_singleton.mp he
    exact Or.inl ⟨.top, rfl⟩
  · by_cases h1 : y = 1
    · subst h1; exact ⟨.var 0, rfl⟩
    · by_cases h0 : y = 0
      · subst h0; exact ⟨.top, rfl⟩
      · exact absurd (by simp [LSub.find?, BoCa.Lifetime.assocFind, Ne.symm h0, Ne.symm h1]) hy
  · rw [gdΔ_find] at hx
    by_cases h1 : x = 1
    · subst h1
      obtain rfl : u = .var 0 := by simpa using hx.symm
      refine ⟨3, 2, by rw [gdS_find]; rfl, by
        show (extS gdδ gdσ gdαs).find? 0 = some 2
        rw [gdS_find]; rfl, show (2 : ℕ) < 3 from by decide⟩
    · rw [if_neg h1] at hx
      by_cases h0 : x = 0
      · subst h0
        obtain rfl : u = .top := by simpa using hx.symm
        exact ⟨2, 0, by rw [gdS_find]; rfl, rfl, show (0 : ℕ) < 2 from by decide⟩
      · rw [if_neg h0] at hx; exact absurd hx (by simp)


/-! ### The configuration `gd`: the closure is W's at `gdσ` -/

/-- A lifetime strictly below `x` is at or below `↓x`. -/
theorem le_down_of_lt {x y : Life} (h : y < x) : y ≤ ↓x := by
  show OrderDual.ofDual x + 1 ≤ OrderDual.ofDual y
  have : OrderDual.ofDual x < OrderDual.ofDual y := h
  omega

/-- **`λg. return g` at `gdC`, at every instantiation of `gdσ`**: an argument under the guard
lies at or above the instantiated lend `ι 2`, so above `ι 3 ≤ ↓(ι 2)`, which is `'1`'s reading
there; returning it boxed at `'1` meets the box. -/
theorem gd_body (ι : Inst) (ls' : List SRec) :
    cRLM (ℍ := ℍ) .binder0 gdσ (ι.sub gdδ) gdC (ι.life gdαs) ls' (forceE gdC (.val gdF))
      PMap.empty := by
  intro ls'' σ' αs' hE hF _ v ρa τ ha hc
  have hE' : ls'' = ls' := by simpa [ExtQ, Placement.bindFut] using hE
  have hF' : σ' = gdσ ∧ αs' = ι.life gdαs := by simpa [FutQI, Placement.bindFut] using hF
  obtain ⟨rfl, rfl⟩ := hF'
  subst hE'
  rw [eq_of_compS_empty_left hc] at *
  intro ht _
  show wpTS ls'' (.app (.val (Val.lam (.var 0))) (.val v)) _ ρa
  refine wpTS_lolli ls'' (.var 0) v _ ρa ?_
  refine wpTS_val ls'' v _ ρa ?_
  have hlt : ι.life1 (lifeN 3) < ι.life1 (lifeN 2) := ι.life1_lt_iff.mpr (by decide)
  refine ⟨ι.life1 (lifeN 3), ?_, ha, ?_⟩
  · rw [extS_inst, Inst.interp_sub]
    show ((extS gdδ gdσ gdαs).find? 1).map _ = _
    rw [gdS_find]; rfl
  · exact ResU.InStratum.mono (le_down_of_lt hlt) (ht.1 _ rfl)

/-- **`GdRelated`**: the closure is a `binder0` value at `gdσ`. Its resource is empty, so the
split drops no view and retains nothing; at each instantiation the body is `gd_body`. -/
theorem gdRelated : GdRelated (ℍ := ℍ) := by
  refine pure_sep_mk trivial ⟨PMap.empty, PMap.empty, ResU.comp_empty_right _, ?_, ⟨rfl, trivial⟩⟩
  rw [vRLM_thunk0]
  intro _ _
  refine ⟨gdσ.map fun _ => false, PMap.empty, PMap.empty, ResU.comp_empty_right _,
    ⟨vwSW_false rfl, placeViewsL_empty⟩, stratS_empty _, fun ι _ ls' _ _ _ _ ρv τ hv hcv => ?_⟩
  rw [vwSW_false_inv hv.1] at hcv
  rw [eq_empty_of_compS_empty hcv]
  exact gd_body ι ls'


/-! ### The runs at `gd` -/

/-- **A β-redex whose body substitutes to a value runs only to it**, the memory unchanged
(`AStep1.deterministic` through `ARun.rest`). -/
theorem run_beta_val {A : Alloc} {k k' : Nat} {μ μ' : Heap} {b : Expr} {w u v : Val}
    (hb : b.subst 0 w = .val u)
    (h : ARun (ℍ := ℍ) A k μ (.app (.val (.lam b)) (.val w)) k' μ' (.val v)) :
    v = u ∧ μ' = μ := by
  have hs : AStep1 (ℍ := ℍ) A k μ (.app (.val (.lam b)) (.val w)) k μ (.val u) :=
    ⟨.hole, _, _, rfl, by rw [← hb]; rfl, AHead.det (Head.beta μ b w) rfl⟩
  have h' := ARun.rest (ARun.more hs (ARun.refl _ _ _)) h
  generalize hE : (Expr.val u) = E at h'
  cases h' with
  | refl => exact ⟨Subtype.ext hE.symm, rfl⟩
  | more s _ => subst hE; exact (AStep1.not_val s).elim

/-- **`load ℓ` takes no step at a memory without `ℓ`.** -/
theorem load_no_step {A : Alloc} {k k' : Nat} {μ μ' : Heap} {e' : Expr} {l : BoCa.Loc}
    (hl : μ l = none)
    (h : AStep1 (ℍ := ℍ) A k μ (.app (.val (.prim .load)) (.val (.loc l))) k' μ' e') : False := by
  have h₀ : Head (ℍ := ℍ) (Heap.upd μ l Val.unit) (.app (.val (.prim .load)) (.val (.loc l)))
      (Heap.upd μ l Val.unit) (.val Val.unit) :=
    Head.load _ l .unit (BoCa.BoLo.Heap.upd_same _ _ _)
  obtain ⟨K', a, a', hE, -, hh⟩ := h
  have hE' : Kont.hole.plug (.app (.val (.prim .load)) (.val (.loc l))) = K'.plug a := hE
  obtain ⟨hb, -⟩ := plug_decomp hh.toHead _ K' h₀ hE'
  have hh' := hh.toHead
  generalize hx : a = x at hh'
  cases hh' <;> simp [Expr.val, Val.prim, Val.loc, ← hb, BoLo.hndE, BoLo.ubindE, BoLo.ccatchE,
    BoLo.cfinE] at hx
  case load ℓ v hv =>
    obtain rfl := hx
    rw [hl] at hv
    cases hv

/-- **`load ℓ` runs to no value at a memory without `ℓ`.** -/
theorem load_no_run {A : Alloc} {k k' : Nat} {μ μ' : Heap} {v : Val} {l : BoCa.Loc}
    (hl : μ l = none)
    (h : ARun (ℍ := ℍ) A k μ (.app (.val (.prim .load)) (.val (.loc l))) k' μ' (.val v)) :
    False := by
  generalize hE : Expr.app (.val (.prim .load)) (.val (.loc l)) = E at h
  cases h with
  | refl =>
      have : IsVal (Expr.app (.val (.prim .load)) (.val (.loc l))) := hE ▸ v.2
      cases this
  | more s _ =>
      subst hE
      exact load_no_step hl s

/-- **`gdG`'s body runs to no value at a memory without `ℓ₁₁`.** -/
theorem gdG_no_run {A : Alloc} {k k' : Nat} {μ μ' : Heap} {v : Val} (hl : μ 11 = none)
    (h : ARun (ℍ := ℍ) A k μ (.app (.val gdG) (.val .unit)) k' μ' (.val v)) : False := by
  have hs : AStep1 (ℍ := ℍ) A k μ (.app (.val gdG) (.val .unit)) k μ
      (.app (.val (.prim .load)) (.val (.loc 11))) :=
    ⟨.hole, _, _, rfl, rfl, AHead.det (Head.beta μ _ .unit) rfl⟩
  exact load_no_run hl (ARun.rest (ARun.more hs (ARun.refl _ _ _)) h)


/-- **`gdG`'s body at a view of `ℓ₁₁` holding `()`**: it loads through the cell ([TR] 6.144,
`wpTS_load_I`) and forgets it (6.149, `wpTS_I_forget`), answering `()` over nothing. -/
theorem gdG_body_wp {ls : List SRec} {Q : List SRec → Val → WProp} {S : LSet} {χ : WRes}
    {h : χ.InStratum S.join} (hχ : χ = PMap.empty) (hQ : Q ls .unit PMap.empty) :
    wpTS (ℍ := ℍ) ls (.app (.val gdG) (.val .unit)) Q
      (ResU.single 11 (CellU.immOf S .unit χ h)) := by
  refine wpTS_lolli ls _ .unit Q _ ?_
  show wpTS ls (Kont.hole.plug (.app (.val (.prim .load)) (.val (.loc 11)))) Q _
  refine wpTS_bind .hole _ ls Q _ ?_
  refine wpTS_load_I ls 11 S.meet (fun v => pure (v = Val.unit)) _ _
    ⟨_, PMap.empty, ResU.comp_empty_right _, ⟨S, .unit, χ, h, rfl, ⟨hχ, rfl⟩, le_rfl⟩,
      fun w ρ₁ ρ₂ hc hcomp => ?_⟩
  obtain ⟨S', v', χ', h', rfl, ⟨χ₁, χ₂, hcχ, ⟨hχ₁, hwv⟩, ⟨hχ₂, hw⟩⟩, hα⟩ := hc
  subst hwv
  rw [eq_of_compS_empty_left hcomp]
  show wpTS ls (.val w) Q _
  refine wpTS_I_forget ls 11 S.meet (fun v => pure (v = Val.unit)) (.val w) Q _
    ⟨_, PMap.empty, ResU.comp_empty_right _, ⟨S', w, χ', h', rfl, ?_, hα⟩,
      wpTS_val ls w Q _ (hw ▸ hQ)⟩
  subst hχ₁ hχ₂
  rw [eq_empty_of_compS_empty hcχ]
  exact ⟨rfl, hw⟩


/-! ### The configuration `gd` after the own lend's push -/

/-- The pushed stack. -/
abbrev gdσY : LStack := gdY :: gdσ

abbrev gdαY : List Life := lifeN 4 :: gdαs

/-- The pushed lend's view: `ℓ₁₁ ↦ imm({4}, (), ∅)`. -/
abbrev gdCell : CellU BoCa.Loc Val :=
  CellU.immOf (LSet.singleton (lifeN 4)) .unit PMap.empty (ResU.inStratum_empty _)

abbrev gdView : WRes := ResU.single 11 gdCell

theorem flat_gdView : ResU.Flat gdView gdView := by
  refine ⟨PMap.empty, gdView, ExW.empty_of_all_imm (fun l ψ h => ?_),
    AgW.single_imm ⟨PMap.empty, PMap.empty, BoLo.agW_empty, BoLo.exW_empty,
      ResU.comp_empty_right _⟩ (ResU.comp_empty_right _), compS_empty_left _⟩
  obtain ⟨-, rfl⟩ := ResU.single_get_eq_some h
  rfl

theorem gdRec_not_desc (d : FrameRec) : ¬ Desc gdRec d := by
  rintro ⟨p, hp, hlin⟩
  cases hlin with
  | nil => exact hp rfl
  | cons hsub _ =>
      obtain ⟨-, -, ζ, hζ, -⟩ := hsub
      rw [PMap.empty_get] at hζ; exact absurd hζ (by simp)

theorem gdRec_descR {d : FrameRec} (h : DescR gdRec d) : d = gdRec := by
  obtain ⟨p, hlin⟩ := h
  cases hlin with
  | nil => rfl
  | cons hsub _ =>
      obtain ⟨-, -, ζ, hζ, -⟩ := hsub
      rw [PMap.empty_get] at hζ; exact absurd hζ (by simp)

/-- **`gdView`'s world**: `ℓ₁₁` allocated holding `()`, then a 6.64 frame at `4`, the type `1`. -/
theorem gd_tw : TW gdView [gdRec] [gdRec] := by
  have h₁ : TW (ResU.single 11 (CellU.ownOf .unit) : WRes) [] [] :=
    TW.alloc TW.empty lower_empty rfl (compS_empty_left _) (ResU.valid_single_own _ _)
  have := TW.immFrame (W := ResU.single 11 (CellU.ownOf .unit))
    (X := ResU.single 11 (CellU.ownOf .unit)) (Z := PMap.empty) (R := PMap.empty)
    (W' := gdView) (ps := []) (rs := []) (ds := []) (l := 11) (v := .unit)
    (α := lifeN 4) .unit ⟨[]⟩ (ResU.inStratum_empty _) h₁ (fun _ hx => hx.elim)
    (ResU.comp_empty_right _) (ResU.comp_empty_right _) ⟨rfl, rfl⟩ (ResU.comp_empty_right _)
    ⟨_, flat_gdView⟩ (fun d => ⟨fun h => by simp at h, fun h => (gdRec_not_desc d h).elim⟩)
  simpa using this

theorem gd_tagged : Tagged gdView [gdRec] gdls := by
  intro x hx
  rw [List.mem_singleton] at hx
  subst hx
  refine ⟨gdRec, List.mem_singleton_self _, ⟨[], LinPath.nil _⟩, fun a ha ζ t hζ ht y hy => ?_,
    fun a _ m hm => ?_⟩
  · have hag : AgW gdView gdView := AgW.single_imm ⟨PMap.empty, PMap.empty, BoLo.agW_empty,
      BoLo.exW_empty, ResU.comp_empty_right _⟩ (ResU.comp_empty_right _)
    rw [AgW.functional ha hag] at hζ
    obtain ⟨-, rfl⟩ := ResU.single_get_eq_some hζ
    simp only [CellU.lsOf, CellU.immOf, Option.some.injEq] at ht
    subst ht
    exact hy
  · obtain ⟨d, hd, ζ, hζ, -⟩ := hm
    rw [gdRec_descR hd, PMap.empty_get] at hζ
    exact absurd hζ (by simp)

theorem gdView_hash : ResU.Hash (PMap.empty : WRes) gdView :=
  ⟨(compS_empty_left _).1, _, compS_empty_left _, ⟨_, flat_gdView⟩⟩

/-- A cell of `gdView` at any depth is its one cell. -/
theorem deepAt_gdView {l : BoCa.Loc} {ψ : CellU BoCa.Loc Val} (h : DeepAt gdView l ψ) :
    l = 11 ∧ ψ = gdCell := by
  cases h with
  | top e => exact ResU.single_get_eq_some e
  | wit e d =>
      obtain ⟨-, rfl⟩ := ResU.single_get_eq_some e
      rw [CellU.wit_immOf] at d
      exact absurd d not_deepAt_empty

/-- **`gdY`'s view at `4`**, at every reading and list: an `imm` cell exactly at `4` holding `()`. -/
theorem vwEW_gdView (s : LSub) (ls : List SRec) : vwEW s gdY true (lifeN 4) ls gdView := by
  refine ⟨⟨LSet.singleton (lifeN 4), .unit, PMap.empty, ResU.inStratum_empty _,
    ls.filter (fun x => decide (lifeN 4 < x.2)), rfl, ⟨rfl, rfl⟩, le_rfl, fun x => ?_⟩,
    fun ψ hψ => ?_⟩
  · simp only [List.mem_filter, and_congr_right_iff]
    exact fun _ => decide_eq_true_iff
  · obtain ⟨-, rfl⟩ := ResU.single_get_eq_some hψ
    exact ⟨rfl, fun t ht y hy => by
      simp only [CellU.lsOf, CellU.immOf, Option.some.injEq] at ht
      subst ht; exact hy⟩

theorem gdσY_innerAt : innerAt gdσY gdαY 11 = some (gdY, lifeN 4) := by simp [innerAt]

/-- **The guard's views at `gdView`.** -/
theorem pvl_gdView (s : LSub) (ls : List SRec) : PlaceViewsL s gdσY gdαY ls gdView := by
  refine ⟨fun l ψ hx _ e α hi => ?_, fun l ψ hd _ _ => ?_⟩
  · obtain ⟨rfl, rfl⟩ := deepAt_gdView hx.toDeepAt
    rw [gdσY_innerAt] at hi
    obtain ⟨rfl, rfl⟩ : gdY = e ∧ lifeN 4 = α := by simpa using hi
    exact vwEW_gdView s ls
  · obtain ⟨rfl, rfl⟩ := deepAt_gdView hd
    exact ⟨gdY, lifeN 4, List.mem_cons_self, rfl, vwEW_gdView s ls⟩

/-- **The table at `gdView`**: its cell is at the pushed lend's own place, at `4`. -/
theorem tab_gdView : TabAtS gdσY gdαY gdView := by
  refine ⟨fun a ha => ?_, fun a _ k ψ hk e => ?_⟩
  · obtain rfl : a = lifeN 4 := (Option.some.inj ha).symm
    refine ResU.inStratum_single 11 (CellU.inStratum_of_lt_at ?_)
    exact GhostEnd.down_lt _
  · obtain ⟨rfl, -⟩ := ResU.single_get_eq_some e
    exact absurd (by simp) hk

/-- **W's views of the pushed stack at `gdView`**: the pushed entry's view, the outer entry's
off. -/
theorem vwSL_gdView (s : LSub) (ls : List SRec) :
    vwSL s gdσY [true, false] gdαY ls gdView :=
  ⟨⟨gdView, PMap.empty, ResU.comp_empty_right _, vwEW_gdView s ls, vwSW_false rfl⟩,
    pvl_gdView s ls⟩

/-- **`gdG` is a `binder0` value at the pushed stack over `gdView`**: at every instantiation the
handed view is an `imm` cell holding `()`, and the body loads through it and forgets it
(`gdG_body_wp`). -/
theorem gdG_pushed (ls : List SRec) :
    vRLM (ℍ := ℍ) .binder0 none gdσY gdδ gdArg gdαY ls gdG gdView := by
  rw [vRLM_thunk0]
  intro _ _
  refine ⟨[true, false], PMap.empty, gdView, compS_empty_left _, vwSL_gdView _ ls,
    stratS_empty _, fun ι _ ls' _ _ _ _ ρv τ hv hcv => ?_⟩
  rw [eq_of_compS_empty_left hcv]
  obtain ⟨a, r, hc, ha, hr⟩ := hv.1
  rw [vwSW_false_inv hr] at hc
  obtain rfl : ρv = a := ResU.CompS.functional hc (ResU.comp_empty_right a)
  have hvis : vis [] gdY true = true := rfl
  rw [hvis] at ha
  obtain ⟨⟨S, u, χ, hχ, ls₀, hρ, ⟨hχ0, hu⟩, -, -⟩, -⟩ := ha
  subst hρ hu
  exact gdG_body_wp hχ0 ⟨rfl, rfl⟩


/-! ### `GdNotPushed`: the closure is no W value after the push -/

/-- Views at the empty resource hold at every list: every visible flag is off. -/
theorem vwSW_empty_any {s : LSub} : ∀ {seen : List BoCa.Loc} {σ : LStack} {ds : List Bool}
    {αs : List Life} {ls ls' : List SRec}, vwSW s seen σ ds αs ls PMap.empty →
      vwSW s seen σ ds αs ls' PMap.empty
  | _, [], [], [], _, _, h => h
  | seen, e :: σ, d :: ds, α :: αs, ls, ls', ⟨a, r, hc, ha, hr⟩ => by
      have ha0 := eq_empty_of_compS_left hc
      have hr0 := eq_empty_of_compS_right hc
      subst ha0 hr0
      refine ⟨PMap.empty, PMap.empty, hc, ?_, vwSW_empty_any hr⟩
      cases hvis : vis seen e d
      · exact vwEW_off s e α ls'
      · rw [hvis] at ha
        obtain ⟨ψ, hψ, -⟩ := vwE_single ha.1
        have := congrArg (fun r => PMap.get r e.l) hψ
        simp at this
  | _, [], [], _ :: _, _, _, h => h.elim
  | _, [], _ :: _, [], _, _, h => h.elim
  | _, [], _ :: _, _ :: _, _, _, h => h.elim
  | _, _ :: _, [], [], _, _, h => h.elim
  | _, _ :: _, [], _ :: _, _, _, h => h.elim
  | _, _ :: _, _ :: _, [], _, _, h => h.elim

theorem not_rel_empty {r : FrameRec} : ¬ Core.Rel r (PMap.empty : WRes) := by
  rintro ⟨m, ψ, hg, -⟩
  rw [PMap.empty_get] at hg; exact absurd hg (by simp)

theorem not_cellIn_empty {b : Life} : ¬ CellIn (PMap.empty : WRes) b := by
  rintro ⟨m, ψ, hg, -⟩
  rw [PMap.empty_get] at hg; exact absurd hg (by simp)

/-- **The clause at the empty resource, at the identity and any list**: nothing is retained or
dropped, so every list extends the list there, and the views handed are empty. -/
theorem relendJ_empty_at {δ : LSub} {σ : LStack} {P : LSub → List Life → List SRec → WProp}
    {αs : List Life} {ls : List SRec} (ls' : List SRec) (hro : RecsOutside αs ls')
    (h : RelendJ δ σ P αs ls PMap.empty) : P δ αs ls' PMap.empty := by
  obtain ⟨ds, ρz, ρn, hc, hn, -, H⟩ := h
  have hz0 := eq_empty_of_compS_left hc
  have hn0 := eq_empty_of_compS_right hc
  subst hz0 hn0
  have hl : Inst.life none αs = αs := Inst.life_none αs
  have := H none (fun c θ h => by cases h) ls'
    ⟨fun r _ hrel => absurd hrel not_rel_empty, fun b hb => absurd hb not_cellIn_empty⟩
    (fun x _ hr => absurd hr not_rel_empty) (fun x _ hr => absurd hr not_rel_empty)
    (by rw [hl]; exact hro) PMap.empty PMap.empty
    (by rw [hl]; exact ⟨vwSW_empty_any hn.1, placeViewsL_empty⟩) (ResU.comp_empty_right _)
  rwa [hl] at this

theorem tab_empty (σ : LStack) (αs : List Life) : TabAtS σ αs PMap.empty :=
  ⟨fun _ _ => ResU.inStratum_empty _, fun _ _ k ψ _ h => by simp at h⟩

theorem hash_empty_empty : ResU.Hash (PMap.empty : WRes) PMap.empty :=
  ⟨(compS_empty_left _).1, _, compS_empty_left _, ⟨_, Core.flat_empty⟩⟩

/-- **`gdG` is no `binder0` value at the pushed stack over nothing**: at the identity and the
empty list, from the empty world, its body's `load ℓ₁₁` has no step. -/
theorem gdG_not_U_empty (ls : List SRec) :
    ¬ vRLM (ℍ := ℍ) .binder0 none gdσY gdδ gdArg gdαY ls gdG PMap.empty := by
  intro h
  rw [vRLM_thunk0] at h
  have hB := relendJ_empty_at [] (fun _ _ x hx => absurd hx List.not_mem_nil)
    (h (tab_empty _ _) placeViewsL_empty)
  obtain ⟨_, _, _, _, _, v, μ, μ', _, _, -, -, -, hμ, -, -, ⟨j, hrun⟩, -⟩ :=
    hB PMap.empty PMap.empty [] hash_empty_empty (compS_empty_left _) TW.empty
      (fun x hx => absurd hx List.not_mem_nil) Alloc.leastFree 0
  obtain ⟨τ, hτ, hval⟩ := hμ
  obtain rfl : τ = PMap.empty := ResU.Flat.functional hτ Core.flat_empty
  exact gdG_no_run (by rw [hval 11]; simp) hrun

/-- **No run of `λg. return g` at `gdG` over the view meets a postcondition that boxes the answer at
`3` and is never met over nothing**: the memory does not change in a β step, so the answer's
resource holds no cell away from `ℓ₁₁`. At `ℓ₁₁` an `own` cell is excluded by `↭` (the
flattening's cell there is `imm`), and a borrow cell is the pushed view exactly at `4`
(`pvlUpdN`), which a box at `3` excludes. With no cell at `ℓ₁₁` the answer's resource is empty. -/
theorem gd_run_fails_of {Q : List SRec → Val → WProp}
    (hQ : ∀ ls₃ ρ', Q ls₃ gdG ρ' → ρ'.InStratum (lifeN 3) ∧ (ρ' = PMap.empty → False)) :
    ¬ wpTS (ℍ := ℍ) gdls (.app (.val gdF) (.val gdG)) Q gdView := by
  intro hwp
  obtain ⟨ρ', ρp, fρ', fρ'p, π, v, μ, μ', ps', ls', -, h₂, -, h₅, h₆, h₇, ⟨k', hrun⟩, h₉, hU,
    -, -, -, -, -, hQ'⟩ :=
    hwp PMap.empty gdView [gdRec] gdView_hash (compS_empty_left _) gd_tw gd_tagged
      Alloc.leastFree 0
  obtain ⟨rfl, rfl⟩ := run_beta_val (b := .var 0) (w := gdG) (u := gdG) rfl hrun
  rw [eq_of_compS_empty_left h₂] at h₆
  obtain ⟨hout, hne⟩ := hQ ls' ρ' hQ'
  -- every cell of the answer's resource is at `ℓ₁₁`
  have hat11 : ∀ m ψ, ρ'.get m = some ψ → m = 11 := by
    intro m ψ hψ
    obtain ⟨ψ', hψ', -⟩ := compS_get_left' h₆ hψ
    have hμm := lower_get h₇ hψ'
    obtain ⟨τ, hτ, hval⟩ := h₅
    obtain rfl : τ = gdView := ResU.Flat.functional hτ flat_gdView
    by_contra hm
    rw [hval m, ResU.single_get_ne _ hm] at hμm
    exact absurd hμm (by simp)
  cases h11 : ρ'.get 11 with
  | none =>
      refine hne (PMap.ext fun m => ?_)
      rw [PMap.empty_get]
      cases hm : ρ'.get m with
      | none => rfl
      | some ψ =>
          obtain rfl := hat11 m ψ hm
          rw [h11] at hm; exact absurd hm (by simp)
  | some ψ =>
      by_cases hk : ψ.kind = Kind.own
      · obtain ⟨ψπ, hψπ, hkπ, -⟩ := compS_get_left' h₉ h11
        obtain ⟨σπ, hσπ, hget⟩ :=
          (hU.1.1 11 _ _ _ _).mp ⟨gdView, flat_gdView, ResU.single_get_self _ _⟩
        obtain ⟨χ, hχ, hkχ, -⟩ := ResU.Flat.get hσπ hψπ
        rw [hget] at hχ
        obtain rfl := Option.some.inj hχ
        rw [hkπ, hk] at hkχ
        exact absurd hkχ (by simp [CellU.kind_immOf])
      · have hpv := placeViewsL_left h₉ (pvlUpdN (extS gdδ gdσY gdαY) gdσY gdαY gdls gdView π
          ⟨rfl, by decide, by decide⟩ (by decide) (pvl_gdView _ _) hU)
        have hat := ((hpv.1 11 ψ (ExAt.top h11) hk gdY (lifeN 4) gdσY_innerAt).2 ψ
          (ResU.single_get_self _ _)).1
        have hlt := lt_at_of_inStratum (hout 11 ψ h11) hk
        rw [hat] at hlt
        exact absurd hlt (by decide)

/-- **At W's relation**: the box at `'1 ↦ 3`, and `gdG` no `U` value over nothing
(`gdG_not_U_empty`). -/
theorem gd_box_run_fails :
    ¬ wpTS (ℍ := ℍ) gdls (.app (.val gdF) (.val gdG))
      (fun ls₃ v => vRLM (ℍ := ℍ) .binder0 none gdσY gdδ (.box (.var 1) gdArg) gdαY ls₃ v)
      gdView := by
  refine gd_run_fails_of fun ls₃ ρ' hQ => ?_
  obtain ⟨α, hα, hUv, hout⟩ := hQ
  have hα3 : α = lifeN 3 := by
    have : (Lifetime.Life.var 1).interp (extS gdδ gdσY gdαY) = some 3 := rfl
    rw [this] at hα
    exact (Option.some.inj hα).symm
  subst hα3
  exact ⟨hout, fun h => by subst h; exact gdG_not_U_empty ls₃ hUv⟩

/-- **`GdNotPushed`**: after the own lend pushes `gdY`, the closure is no `binder0` value. Its `U`
clause at the empty resource is asked at the identity; the `⊸` clause there at `gdG` over the
pushed view (`gdG_pushed`), under the guard (`tab_gdView`, `pvl_gdView`), owes the run
`gd_box_run_fails` excludes. -/
theorem gdNotPushed : GdNotPushed (ℍ := ℍ) := by
  intro hg
  obtain ⟨-, hgs⟩ := pure_sep_iff.mp hg
  obtain ⟨ρ₁, ρ₂, hc, h₁, -⟩ := hgs
  have hρ₁ : ρ₁ = PMap.empty := eq_empty_of_compS_left hc
  subst hρ₁
  rw [vRLM_thunk0] at h₁
  have hB := relendJ_empty_at gdls (fun a ha x hx hlt => by
      obtain rfl : x = (gdRec, lifeN 4) := List.mem_singleton.mp hx
      rcases List.mem_cons.mp ha with rfl | ha
      · exact absurd hlt (lt_irrefl _)
      · obtain rfl : a = lifeN 2 := List.mem_singleton.mp ha
        exact absurd hlt (by decide))
    (h₁ (tab_empty _ _) placeViewsL_empty)
  have hW := hB gdls gdσY gdαY (extQ_refl _ _ _) (by simp [FutQI, Placement.bindFut])
    (futAvoids_self _ _) gdG gdView gdView (gdG_pushed gdls) (compS_empty_left _)
    tab_gdView (pvl_gdView _ _)
  exact gd_box_run_fails hW


/-! ### The unrestricted monotonicity statements at `gd`: a scope pin -/

/-- **`NotMonoOwnGM0`**: `MonoOwnGM binder0` is refuted at `gd` (`gdIndex`, `gdRelated`,
`gdNotPushed`). A refutation of ProbeD1's draft statement at a configuration not shown to arise;
its index is outside the arising set's record invariant (`gdNotRecsInsideOwn`), and its closure is
no Core value (`gdNotCore`). It pins the scope of the restriction `MonoOwnGMC` adds; it does not
refute the lemma's consumer `AllIRowM binder0`. -/
theorem notMonoOwnGM0 : NotMonoOwnGM0 (ℍ := ℍ) := by
  intro h
  obtain ⟨hok, hob, hro, hso, hpush, hδ, hfr, hro', hsf, ht, hpv, -⟩ := gdIndex
  exact gdNotPushed (h gdσ gdδ gdΓ gdγ gdαs gdls PMap.empty gdCy gdY (lifeN 4) hok hob hro hso
    hpush hδ hfr hro' hsf ht hpv gdRelated)

/-- `MonoGM binder0` is refuted with it, through the instance lemma. -/
theorem notMonoGM0 : ¬ MonoGM (ℍ := ℍ) .binder0 :=
  fun h => notMonoOwnGM0 (monoOwnGMOfMonoGM .binder0 h)

/-- `MonoVM binder0` is refuted with it, through the instance lemma. -/
theorem notMonoVM0 : ¬ MonoVM (ℍ := ℍ) .binder0 :=
  fun h => notMonoGM0 (monoGMOfMonoVM .binder0 h)

/-- **`MonoUnrestrictedRefuted0`**: the three unrestricted statements' negation, a fact about
these statements of ProbeD1 at a configuration not shown to arise; not `binder0`'s status. -/
theorem monoUnrestrictedRefuted0 : MonoUnrestrictedRefuted0 (ℍ := ℍ) :=
  ⟨notMonoOwnGM0, notMonoGM0, notMonoVM0⟩

/-- **`GdNotRecsInsideOwn`**: `gdRec` sits at `4`, at or below the outermost lend `2`, and `gdσ`'s
one entry is a 6.65 entry. -/
theorem gdNotRecsInsideOwn : GdNotRecsInsideOwn := by
  intro h
  obtain ⟨e, he, u, hk, -⟩ := h (gdRec, lifeN 4) (List.mem_singleton_self _)
    ⟨lifeN 2, rfl, by decide⟩
  obtain rfl : e = gdX := List.mem_singleton.mp he
  exact absurd hk (by simp)

/-- **`GdIdxNotArisesOf`**: once the record invariant arises, no configuration of the set has
`gd`'s index. -/
theorem gdIdxNotArisesOf : GdIdxNotArisesOf (ℍ := ℍ) := by
  rintro hR ⟨c, hc, hσ, hαs, hls⟩
  have := hR c hc
  rw [hσ, hαs, hls] at this
  exact gdNotRecsInsideOwn this

/-! ### The row at `gd` -/

/-- **`GdRowRefutation`**: `gd`'s index meets the hypotheses of the row's conclusion at
`gdΔ; gdΓ ⊢ Λ. M : gdCy`, so a body refuting the conclusion there refutes the row. -/
theorem gdRowRefutation : GdRowRefutation (ℍ := ℍ) := by
  rintro ⟨hok, hob, hro, hso, -, -, -, -, -, ht, hpv, hBL, hSc, hJ, hSD, hMod⟩ hrel
    ⟨S, M, hM, hn⟩ hrow
  have hc := hrow gdΔ gdΓ 2 (.var 1) M S gdCyBody rfl (fun y u hy => ?_) (fun s hs _ h => ?_)
    rfl (fun s hs _ h => ?_) hM hBL hSc gdδ gdσ gdαs gdls gdγ PMap.empty hok hob hJ hSD hMod
    hro hso ht hpv hrel
  · exact hn hc
  · rw [gdΔ_find] at hy
    by_cases h1 : y = 1
    · subst h1
      obtain rfl : u = .var 0 := by simpa using hy.symm
      rfl
    · rw [if_neg h1] at hy
      by_cases h0 : y = 0
      · subst h0
        obtain rfl : u = .top := by simpa using hy.symm
        rfl
      · rw [if_neg h0] at hy; exact absurd hy (by simp)
  · obtain rfl : s = ⟨gdTy, true⟩ := List.mem_singleton.mp hs
    simp [VFree, CFree, Lifetime.Life.mentions] at h
  · obtain rfl : s = ⟨gdTy, true⟩ := List.mem_singleton.mp hs
    simp [VTy.binders, CTy.binders] at h


/-! ### `gd` against Core's relation: the restriction excludes it -/

/-- **`gdG` is no Core value at `U(F 1)` over nothing**: Core's `U` clause at the empty list, from the
empty world, runs `load ℓ₁₁` with no step. -/
theorem gdG_not_core_empty (ls : List SRec) (s : LSub) :
    ¬ vC true gdArg ls s gdG PMap.empty := by
  intro h
  have hB := h [] ⟨fun r _ hrel => absurd hrel not_rel_empty, fun b hb => absurd hb not_cellIn_empty⟩
  obtain ⟨_, _, _, _, _, v, μ, μ', _, _, -, -, -, hμ, -, -, ⟨j, hrun⟩, -⟩ :=
    hB PMap.empty PMap.empty [] hash_empty_empty (compS_empty_left _) TW.empty
      (fun x hx => absurd hx List.not_mem_nil) Alloc.leastFree 0
  obtain ⟨τ, hτ, hval⟩ := hμ
  obtain rfl : τ = PMap.empty := ResU.Flat.functional hτ Core.flat_empty
  exact gdG_no_run (by rw [hval 11]; simp) hrun

/-- **`gdG` is a Core value at the view**, at every reading: at every extension of the list the body
loads through the cell and forgets it. -/
theorem gdG_core (s : LSub) (ls : List SRec) : vC true gdArg ls s gdG gdView := by
  intro ls' _
  show wpTS ls' (.app (.val gdG) (.val .unit)) _ gdView
  exact gdG_body_wp rfl ⟨rfl, rfl⟩

/-- **`GdNotCore`**: the closure is no Core value at `gdδ` over nothing, at any list. At `gdls`
Core's `⊸` clause asks the run at `gdG` over the view, which `gd_run_fails_of` excludes: `'1 ↦ 3`
in the box, and `gdG` no Core value over nothing. -/
theorem gdNotCore : GdNotCore (ℍ := ℍ) := by
  intro ls h
  have hB := h gdls
    ⟨fun r _ hrel => absurd hrel not_rel_empty, fun b hb => absurd hb not_cellIn_empty⟩
  have hW := hB gdG gdView gdView (gdG_core gdδ gdls) (compS_empty_left _)
  refine gd_run_fails_of (fun ls₃ ρ' hQ => ?_) hW
  obtain ⟨α, hα, hUv, hout⟩ := hQ
  have hα3 : α = lifeN 3 := by
    have : (Lifetime.Life.var 1).interp gdδ = some 3 := rfl
    rw [this] at hα
    exact (Option.some.inj hα).symm
  subst hα3
  exact ⟨hout, fun h => by subst h; exact gdG_not_core_empty ls₃ gdδ hUv⟩

/-- `gdTy` reads only `'1`, which the stack's reading and `gdδ` read alike. -/
theorem vC_gdTy_reading (b : Bool) (ls : List SRec) :
    vC b gdTy ls (extS gdδ gdσ gdαs) = vC b gdTy ls gdδ := by
  refine vC_congr gdTy (fun y hy => ?_) b ls
  simp only [VFree, CFree, Lifetime.Life.mentions, beq_iff_eq] at hy
  rcases hy with h | rfl | h
  · exact h.elim
  · rfl
  · exact h.elim

/-- **`GdCtxNotCore`**: `gd` is outside the restriction, its one live slot's Core half failing
(`gdNotCore`). -/
theorem gdCtxNotCore : GdCtxNotCore (ℍ := ℍ) := by
  intro h
  obtain ⟨-, hgs⟩ := pure_sep_iff.mp h
  obtain ⟨ρ₁, ρ₂, hc, ⟨-, hcore⟩, -⟩ := hgs
  have hρ₁ : ρ₁ = PMap.empty := eq_empty_of_compS_left hc
  subst hρ₁
  rw [vC_gdTy_reading] at hcore
  exact gdNotCore gdls hcore

/-! ### The restriction is met at `gd`'s index with a `U` slot -/

/-- **The clause at the identity**: the dropped views handed back as they were, at the list
itself. -/
theorem relendJ_id {δ : LSub} {σ : LStack} {P : LSub → List Life → List SRec → WProp}
    {αs : List Life} {ls : List SRec} {ρ : WRes} (hro : RecsOutside αs ls)
    (h : RelendJ δ σ P αs ls ρ) : P δ αs ls ρ := by
  obtain ⟨ds, ρz, ρn, hc, hn, -, H⟩ := h
  have hl : Inst.life none αs = αs := Inst.life_none αs
  have := H none (fun c θ h => by cases h) ls (Ext.refl ls ρz) (keepsT_refl ls ρz)
    (fun y hy _ => ⟨y, hy, RecUpTo.refl y⟩) (by rw [hl]; exact hro) ρn ρ
    (by rw [hl]; exact hn) hc
  rwa [hl] at this

/-- `λ_. ()` is a W value at `U(F 1)` over nothing, at every index. -/
theorem unitThunk_W (σ : LStack) (δ : LSub) (αs : List Life) (ls : List SRec)
    (hl : αs.length = σ.length) :
    vRLM (ℍ := ℍ) .binder0 none σ δ gdArg αs ls (Val.lam .unit) PMap.empty := by
  rw [vRLM_thunk0]
  intro _ _
  refine relendJ_emp hl fun δ' αs' ls' => ?_
  show wpTS ls' (.app (.val (Val.lam .unit)) (.val .unit)) _ _
  exact wpTS_lolli ls' .unit .unit _ _ (wpTS_val ls' .unit _ _ ⟨rfl, rfl⟩)

/-- `λ_. ()` is a Core value at `U(F 1)` over nothing. -/
theorem unitThunk_core (s : LSub) (ls : List SRec) :
    vC true gdArg ls s (Val.lam .unit) PMap.empty := by
  intro ls' _
  show wpTS ls' (.app (.val (Val.lam .unit)) (.val .unit)) _ _
  exact wpTS_lolli ls' .unit .unit _ _ (wpTS_val ls' .unit _ _ ⟨rfl, rfl⟩)

/-- `gdF₀`'s run after its argument's: `(); λ_. ()`, the answer boxed over nothing. -/
theorem gdF₀_tail {ls : List SRec} {Q : List SRec → Val → WProp}
    (hQ : ∀ ls₃, Q ls₃ (Val.lam .unit) PMap.empty) (g : Val) {P : List SRec → Val → WProp}
    (hP : ∀ ls₃ w ρ₃, P ls₃ w ρ₃ → ρ₃ = PMap.empty ∧ w = Val.unit) {ρ : WRes}
    (hg : wpTS (ℍ := ℍ) ls (.app (.val g) (.val .unit)) P ρ) :
    wpTS (ℍ := ℍ) ls (.app (.val gdF₀) (.val g)) Q ρ := by
  refine wpTS_lolli ls _ g Q ρ ?_
  show wpTS ls (Kont.plug (.seq .hole (.val (Val.lam .unit))) (.app (.val g) (.val .unit))) Q ρ
  refine wpTS_bind (.seq .hole (.val (Val.lam .unit))) _ ls Q ρ ?_
  refine wpTS_mono (fun ls₃ w ρ₃ hw => ?_) ρ hg
  obtain ⟨rfl, rfl⟩ := hP ls₃ w ρ₃ hw
  show wpTS ls₃ (.seq (.val .unit) (.val (Val.lam .unit))) Q PMap.empty
  exact wpTS_1 ls₃ _ Q _ (wpTS_val ls₃ _ Q _ (hQ ls₃))

/-- **`GdRestrictedMet`**: `gdF₀` is W's and Core's at `gd`'s index. At W, at each instantiation
the argument's clause at the identity runs it to `()` over nothing (`relendJ_id`), and the answer
`λ_. ()` boxed at `'1` holds nothing. At Core the same, the argument's clause at the list itself. -/
theorem gdRestrictedMet : GdRestrictedMet (ℍ := ℍ) := by
  refine pure_sep_mk trivial ⟨PMap.empty, PMap.empty, ResU.comp_empty_right _, ⟨?_, ?_⟩,
    ⟨rfl, trivial⟩⟩
  · rw [vRLM_thunk0]
    intro _ _
    refine ⟨gdσ.map fun _ => false, PMap.empty, PMap.empty, ResU.comp_empty_right _,
      ⟨vwSW_false rfl, placeViewsL_empty⟩, stratS_empty _,
      fun ι _ ls' _ _ _ hro ρv τ hv hcv => ?_⟩
    rw [vwSW_false_inv hv.1] at hcv
    rw [eq_empty_of_compS_empty hcv]
    intro ls'' σ' αs' hE hF _ g ρa τ' ha hc
    have hE' : ls'' = ls' := by simpa [ExtQ, Placement.bindFut] using hE
    have hF' : σ' = gdσ ∧ αs' = ι.life gdαs := by simpa [FutQI, Placement.bindFut] using hF
    obtain ⟨rfl, rfl⟩ := hF'
    subst hE'
    rw [eq_of_compS_empty_left hc] at *
    intro ht hpv
    rw [vRLM_thunk0] at ha
    have hg := relendJ_id hro (ha ht hpv)
    refine gdF₀_tail (fun ls₃ => ⟨ι.life1 (lifeN 3), ?_,
      unitThunk_W _ _ _ ls₃ rfl, ResU.inStratum_empty _⟩) g (fun _ _ _ hw => ⟨hw.1, hw.2⟩) hg
    rw [extS_inst, Inst.interp_sub]
    show ((extS gdδ gdσ gdαs).find? 1).map _ = _
    rw [gdS_find]; rfl
  · intro ls' _ g ρa τ ha hc
    rw [eq_of_compS_empty_left hc]
    have hg := ha ls' (Ext.refl ls' ρa)
    refine gdF₀_tail (fun ls₃ => ⟨lifeN 3, ?_, unitThunk_core _ ls₃, ResU.inStratum_empty _⟩) g
      (fun _ _ _ hw => ⟨hw.1, hw.2⟩) hg
    show (extS gdδ gdσ gdαs).find? 1 = some 3
    rw [gdS_find]; rfl


/-! ### The restricted route: what is carried, and the step at a `U` slot -/

/-- **`MonoOwnGMC` at a context whose live slots reach no `U`**, with `StackPayAvoids`: the W half
by `monoOwnUFree_go`, the Core half by locality (the pushed variable is free in no live type,
`CtxFresh`, and the pushed reading agrees with the old one elsewhere). -/
def MonoOwnGMCUFreeA (p : Placement) : Prop :=
  ∀ (σ : LStack) (δ : LSub) (Γ : Ctx VTy) (γ : List Val) (αs : List Life) (ls : List SRec)
    (ρ : WRes) (C : CTy) (e : LEnt) (a : Life),
    StackPayAvoids e.x σ → (∀ s ∈ Γ, s.live = true → UFreeM s.ty) →
    StackOK σ αs → OuterBelowTop αs → RecsOutside αs ls → SubOutside σ αs δ →
    OwnPushI δ C ρ (σ, αs) e a → δ.find? e.x = none → CtxFresh e.x Γ →
    RecsOutside (a :: αs) ls → SubFresh δ a →
    TabAtS σ αs ρ → PlaceViewsL (extS δ σ αs) σ αs ls ρ →
    gRLMC (ℍ := ℍ) p σ δ αs ls Γ γ ρ → gRLMC (ℍ := ℍ) p (e :: σ) δ (a :: αs) ls Γ γ ρ

theorem monoOwnGMCUFreeA (p : Placement) : MonoOwnGMCUFreeA (ℍ := ℍ) p := by
  intro σ δ Γ γ αs ls ρ C e a hσ hU hok _ _ _ hpush _ hfr _ hsf ht hpv hg
  obtain ⟨_, _, _, _, _, _, hoi, _, _⟩ := hpush
  obtain ⟨hlw, hgs⟩ := pure_sep_iff.mp hg
  refine pure_sep_mk hlw ?_
  have key : ∀ (Γ : Ctx VTy) (γ : List Val) (ρ : WRes),
      (∀ s ∈ Γ, s.live = true → UFreeM s.ty) → CtxFresh e.x Γ →
      (TabAtS σ αs ρ ∧ PlaceViewsL (extS δ σ αs) σ αs ls ρ ∧ (∀ ψ, ¬ DeepAt ρ e.l ψ) ∧
        ρ.InStratum a) →
      gSepRLMC (ℍ := ℍ) p σ δ αs ls Γ γ ρ →
        gSepRLMC (ℍ := ℍ) p (e :: σ) δ (a :: αs) ls Γ γ ρ := by
    intro Γ
    induction Γ with
    | nil => intro γ ρ _ _ _ h; cases γ <;> exact h
    | cons s Γ ih =>
        intro γ ρ hU' hfr' hF h
        cases γ with
        | nil => exact h
        | cons v γ =>
            have hU'' : ∀ s' ∈ Γ, s'.live = true → UFreeM s'.ty :=
              fun s' hs' hl => hU' s' (List.mem_cons_of_mem _ hs') hl
            have hfr'' : CtxFresh e.x Γ := fun s' hs' hl => hfr' s' (List.mem_cons_of_mem _ hs') hl
            by_cases hl : s.live = true
            · simp only [gSepRLMC, hl, if_true] at h ⊢
              obtain ⟨ρ₁, ρ₂, hc, ⟨h₁, h₁c⟩, h₂⟩ := h
              have hx := (hfr' s List.mem_cons_self hl).1
              refine ⟨ρ₁, ρ₂, hc, ⟨monoOwnUFree_go p e a s.ty none none σ δ αs ls v ρ₁
                  (hU' s List.mem_cons_self hl) (envPushNone σ δ αs ls e a) hok hoi.chain hsf hσ
                  hx (pushFacts_left hc hF) h₁, ?_⟩, ih γ ρ₂ hU'' hfr'' (pushFacts_right hc hF) h₂⟩
              rw [vC_congr s.ty (δ₂ := extS δ σ αs)
                (fun y hy => extS_push_find δ e σ a αs (fun he => hx (he ▸ hy)))]
              exact h₁c
            · simp only [gSepRLMC, hl] at h ⊢
              exact ih γ ρ hU'' hfr'' hF h
  exact key Γ γ ρ hU hfr ⟨ht, hpv, hoi.placeFree, hoi.below⟩ hgs

end ProbeD1

end
