import ProbeD1.R1Stmt0

/-!
# ProbeD1 — a block pushed across a context reaching no `U` (`GROUND.md` §4.5, item 3)

The block's `U`-free push: `monoOwnUFree_go`'s recursion with the single entry replaced by a block
of entries named `x` at one lifetime `a` (`monoOwnUFreeB_go`, `monoOwnGUFreeMB`). A value's borrow
leaves are top-level cells, under no `imm` ancestor, so none lies at a block place, where the
callback's part holds only `own` cells frozen under an `imm` ancestor (`OwnOKB.placeFree`). The
leaves' `CohS` and `RetainedPay` are read at the pushed stack as at the old one (`cohS_pushB`,
`retainedPayPushB_len`), the reading agreeing off `x`.

The single push onto a stack that may hold blocks is `monoOwnGUFreeMA`'s, which reads only the
stack's length (`monoOwnGUFreeMA_len`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace ProbeD1
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open GhostEnd (LEnt LStack LKind extS TabAtS)

/-! ### The reading at a pushed block -/

/-- A block of entries named `x` read off `x` is the old reading. -/
theorem extS_blockPush_ne {δ : LSub} {σ : LStack} {αs : List Life} {τ : LStack} {x : LifeVar}
    {a : Life} (hτx : ∀ e ∈ τ, e.x = x) {y : LifeVar} (hy : x ≠ y) :
    (extS δ (τ ++ σ) (blockL τ a ++ αs)).find? y = (extS δ σ αs).find? y := by
  induction τ with
  | nil => rfl
  | cons e τ ih =>
      have he : e.x = x := hτx e (List.mem_cons_self ..)
      show ((extS δ (τ ++ σ) (blockL τ a ++ αs)).extend e.x a).find? y = _
      rw [find?_extend_ne _ _ (by rw [he]; exact hy)]
      exact ih fun e' he' => hτx e' (List.mem_cons_of_mem _ he')

/-- A non-empty block of entries named `x` at `a` reads `x` at `a`. -/
theorem extS_blockPush_self {δ : LSub} {σ : LStack} {αs : List Life} {τ : LStack} {x : LifeVar}
    {a : Life} (hτx : ∀ e ∈ τ, e.x = x) (hne : τ ≠ []) :
    (extS δ (τ ++ σ) (blockL τ a ++ αs)).find? x = some a := by
  obtain ⟨e, τ', rfl⟩ := List.exists_cons_of_ne_nil hne
  show ((extS δ (τ' ++ σ) (blockL τ' a ++ αs)).extend e.x a).find? x = some a
  rw [hτx e (List.mem_cons_self ..), find?_extend_self]

/-- At a block, an `innerAt` away from the block's places is the old stack's. -/
theorem innerAt_blockPush {σ : LStack} {αs : List Life} {τ : LStack} {a : Life} {l : BoCa.Loc}
    (hl : l ∉ τ.map LEnt.l) : innerAt (τ ++ σ) (blockL τ a ++ αs) l = innerAt σ αs l :=
  innerAt_append_right (by simp [blockL]) hl

/-! ### A leaf across a block push -/

/-- **`CohS` across a block push** at a leaf away from the block's places. -/
theorem cohS_pushB {σ : LStack} {αs : List Life} {s s' : LSub} {τ : LStack} {x : LifeVar}
    {a : Life} {A : VTy} {l : BoCa.Loc} {ρ : WRes} (hne : l ∉ τ.map LEnt.l)
    (hag : ∀ y, x ≠ y → s'.find? y = s.find? y)
    (hA : ∀ (b : Lifetime.Life) (T : VTy), (A = .mut b T ∨ A = .imm b T) → ¬ VFree x T)
    (hσ : StackPayAvoids x σ) (h : CohS σ αs s A (.loc l) ρ) :
    CohS (τ ++ σ) (blockL τ a ++ αs) s' A (.loc l) ρ := by
  intro l' e' α' hl' hi
  cases hl'
  rw [innerAt_blockPush hne] at hi
  obtain ⟨hk, hat⟩ := h l e' α' rfl hi
  have he' : e' ∈ σ := (List.of_mem_zip (innerAt_mem hi).1).1
  refine ⟨?_, hat⟩
  have hagT : ∀ T, ¬ VFree x T → ∀ y, VFree y T → s'.find? y = s.find? y :=
    fun T hT y hy => hag y (fun hxy => hT (hxy ▸ hy))
  cases A with
  | «mut» b T =>
      exact ⟨hk.1, (TyEq.of_agree T (hagT T (hA b T (Or.inl rfl)))).trans
        (hk.2.trans (TyEq.of_agree e'.T (fun y hy => (hagT e'.T (hσ e' he') y hy).symm)))⟩
  | imm b T =>
      exact ⟨hk.1, (TyEq.of_agree T (hagT T (hA b T (Or.inr rfl)))).trans
        (hk.2.trans (TyEq.of_agree e'.T (fun y hy => (hagT e'.T (hσ e' he') y hy).symm)))⟩
  | unit | zero | unk | int _ | opq _ | tvar _ | tensor _ _ | sum _ _ | thunk _ | bang _
  | box _ _ | ref _ | mu _ | fam _ => exact hk.elim

/-- **`RetainedPay` across a block pushed fresh below the reading**: onto a non-empty stack the cut
is the same and the reading agrees off `x`; onto the empty stack the cut appears just above the
block's lifetime, and every value of the reading is above it (`SubFresh`). -/
theorem retainedPayPushB_len {σ : LStack} {αs : List Life} {δ : LSub} {τ : LStack} {x : LifeVar}
    {a : Life} {T : VTy} {v : Val} (hok : αs.length = σ.length) (hτx : ∀ e ∈ τ, e.x = x)
    (hsf : SubFresh δ a) (hx : ¬ VFree x T)
    (h : RetainedPay σ αs (extS δ σ αs) T v) :
    RetainedPay (τ ++ σ) (blockL τ a ++ αs) (extS δ (τ ++ σ) (blockL τ a ++ αs)) T v := by
  intro l' hv hi
  have hlτ : l' ∉ τ.map LEnt.l := by
    intro hm
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
    unfold innerAt at hi
    rw [List.find?_eq_none] at hi
    have hmem : (e, a) ∈ (τ ++ σ).zip (blockL τ a ++ αs) := by
      rw [List.zip_append (by simp [blockL])]
      exact List.mem_append_left _ (mem_zip_blockL he a)
    exact hi (e, a) hmem (by simp)
  rw [innerAt_blockPush hlτ] at hi
  intro y hy m hm hint
  have hyx : x ≠ y := fun he => hx (he ▸ hy)
  rw [extS_blockPush_ne hτx hyx] at hm
  cases σ with
  | nil =>
      have hαs : αs = [] := List.length_eq_zero_iff.mp (by simpa using hok)
      subst hαs
      have hmem : (y, m) ∈ δ.entries := assocFind_mem hm
      have hlt : a < OrderDual.toDual m := hsf (y, m) hmem
      obtain ⟨c, hc, hlt'⟩ := hint
      have hc' : c = OrderDual.toDual (OrderDual.ofDual a - 1) := by
        obtain ⟨o, ho, hco⟩ := cutOf_eq.mp hc
        have hmo : o ∈ blockL τ a ++ [] := List.mem_of_getLast? ho
        rw [List.append_nil] at hmo
        obtain ⟨_, _, rfl⟩ := List.mem_map.mp hmo
        exact hco
      subst hc'
      exact absurd hlt' (not_lt.mpr (cut_le_of_lt hlt))
  | cons e₀ σ₀ =>
      obtain ⟨α₀, αs₀, rfl⟩ : ∃ α₀ αs₀, αs = α₀ :: αs₀ := by
        cases αs with
        | nil => exact absurd hok (by simp)
        | cons α₀ αs₀ => exact ⟨α₀, αs₀, rfl⟩
      refine h l' hv hi y hy m hm ?_
      obtain ⟨c, hc, hlt'⟩ := hint
      refine ⟨c, ?_, hlt'⟩
      have : (blockL τ a ++ α₀ :: αs₀).getLast? = (α₀ :: αs₀).getLast? := by
        cases h' : (α₀ :: αs₀).getLast? with
        | none => simp at h'
        | some o => rw [List.getLast?_append, h']; rfl
      simp only [cutOf, this] at hc ⊢
      exact hc

/-- **A leaf across a block push**: Core's leaf at the pushed reading (`vC_congr`), `CohS` by
`cohS_pushB`, `RetainedPay` by `retainedPayPushB_len`. The leaf's cell is top-level, so it lies at
no block place. -/
theorem vRLJ_leaf_pushB_len {p : Placement} {σ : LStack} {δ : LSub} {αs : List Life}
    {ls : List SRec} {τ : LStack} {x : LifeVar} {a : Life} {A : VTy} {v : Val} {ρ : WRes}
    (hA : (∃ b T, A = .mut b T) ∨ (∃ b T, A = .imm b T)) (hx : ¬ VFree x A)
    (hτx : ∀ e ∈ τ, e.x = x) (hok : αs.length = σ.length) (hsf : SubFresh δ a)
    (hpf : ∀ e ∈ τ, ∀ ψ, DeepAt ρ e.l ψ → ψ.kind = Kind.own ∧ ¬ ExAt ρ e.l ψ)
    (hσ : StackPayAvoids x σ) (h : vRLJ (ℍ := ℍ) p σ δ A αs ls v ρ) :
    vRLJ (ℍ := ℍ) p (τ ++ σ) δ A (blockL τ a ++ αs) ls v ρ := by
  have hagree : ∀ y, VFree y A →
      (extS δ (τ ++ σ) (blockL τ a ++ αs)).find? y = (extS δ σ αs).find? y :=
    fun y hy => extS_blockPush_ne hτx (fun he => hx (he ▸ hy))
  have hag : ∀ y, x ≠ y →
      (extS δ (τ ++ σ) (blockL τ a ++ αs)).find? y = (extS δ σ αs).find? y :=
    fun y hy => extS_blockPush_ne hτx hy
  have hnot : ∀ ℓ ψ, ρ.get ℓ = some ψ → ψ.kind ≠ Kind.own → ℓ ∉ τ.map LEnt.l := by
    intro ℓ ψ hg hk hm
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
    exact (hpf e he ψ (DeepAt.top hg)).2 (ExAt.top hg)
  rcases hA with ⟨b, T, rfl⟩ | ⟨b, T, rfl⟩
  · rw [vRLJ_mut_eq] at h ⊢
    obtain ⟨hvc, hcoh, hpay⟩ := h
    obtain ⟨α, -, ℓ, hsep⟩ := id hvc
    obtain ⟨rfl, b', u, σ', hσ', Q, hw, ls₀, -, hρ, -⟩ := pure_sep_iff.mp hsep
    have hℓ : ℓ ∉ τ.map LEnt.l := hnot ℓ _ (by rw [hρ, ResU.single_get_self])
      CellU.kind_mutOf_ne_own
    have hxT : ¬ VFree x T := fun h' => hx (Or.inr h')
    refine ⟨by rw [vC_congr _ hagree]; exact hvc, ?_, retainedPayPushB_len hok hτx hsf hxT hpay⟩
    exact cohS_pushB hℓ hag (fun b'' T'' hb => by
      rcases hb with hb | hb <;> cases hb; exact hxT) hσ hcoh
  · rw [vRLJ_imm_eq] at h ⊢
    obtain ⟨hvc, hcoh, hpay⟩ := h
    obtain ⟨α, -, ℓ, hsep⟩ := id hvc
    obtain ⟨⟨rfl, -⟩, S, u, χ, hχ, ls₀, hρ, -⟩ := pure_sep_iff.mp hsep
    have hℓ : ℓ ∉ τ.map LEnt.l := hnot ℓ _ (by rw [hρ, ResU.single_get_self])
      (by rw [CellU.kind_immOf]; decide)
    have hxT : ¬ VFree x T := fun h' => hx (Or.inr h')
    refine ⟨by rw [vC_congr _ hagree]; exact hvc, ?_, retainedPayPushB_len hok hτx hsf hxT hpay⟩
    exact cohS_pushB hℓ hag (fun b'' T'' hb => by
      rcases hb with hb | hb <;> cases hb; exact hxT) hσ hcoh

/-! ### A value reaching no `U` across a block push -/

/-- **An environment's candidates carried across a block push**: `EnvPush` at a block. -/
def EnvPushB (η η' : Option (Nat → WEnt)) (σ : LStack) (δ : LSub) (αs : List Life)
    (ls : List SRec) (τ : LStack) (x : LifeVar) (a : Life) : Prop :=
  (∀ n, (wEnv η' n).ty = (wEnv η n).ty) ∧ (∀ n, ¬ VFree x (wEnv η n).ty) ∧
  ∀ n v ρ, TabAtS σ αs ρ → PlaceViewsL (extS δ σ αs) σ αs ls ρ →
    (∀ e ∈ τ, ∀ ψ, DeepAt ρ e.l ψ → ψ.kind = Kind.own ∧ ¬ ExAt ρ e.l ψ) →
    ρ.InStratum a → wEnvP η n v ρ → wEnvP η' n v ρ

theorem envPushBNone (σ : LStack) (δ : LSub) (αs : List Life) (ls : List SRec) (τ : LStack)
    (x : LifeVar) (a : Life) : EnvPushB none none σ δ αs ls τ x a :=
  ⟨fun _ => rfl, fun _ h => h, fun _ _ _ _ _ _ _ h => absurd h id⟩

/-- The block's facts at a resource hold at its parts. -/
theorem pushFactsB_left {σ : LStack} {αs : List Life} {s : LSub} {ls : List SRec} {τ : LStack}
    {a : Life} {ρ₁ ρ₂ ρ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ)
    (h : TabAtS σ αs ρ ∧ PlaceViewsL s σ αs ls ρ ∧
      (∀ e ∈ τ, ∀ ψ, DeepAt ρ e.l ψ → ψ.kind = Kind.own ∧ ¬ ExAt ρ e.l ψ) ∧ ρ.InStratum a) :
    TabAtS σ αs ρ₁ ∧ PlaceViewsL s σ αs ls ρ₁ ∧
      (∀ e ∈ τ, ∀ ψ, DeepAt ρ₁ e.l ψ → ψ.kind = Kind.own ∧ ¬ ExAt ρ₁ e.l ψ) ∧
      ρ₁.InStratum a := by
  refine ⟨tabAtS_left hc h.1, placeViewsL_left hc h.2.1, fun e he ψ hd => ?_,
    ((outlives_comp hc a).mp h.2.2.2).1⟩
  obtain ⟨ψ', hd', hs⟩ := DeepAt.of_compS_left hc hd
  refine ⟨hs.kind ▸ (h.2.2.1 e he ψ' hd').1, fun hx => ?_⟩
  obtain ⟨ψ'', hx'', -⟩ := ExAt.of_compS_left hc hx
  exact (h.2.2.1 e he ψ'' hx''.toDeepAt).2 hx''

theorem pushFactsB_right {σ : LStack} {αs : List Life} {s : LSub} {ls : List SRec} {τ : LStack}
    {a : Life} {ρ₁ ρ₂ ρ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ)
    (h : TabAtS σ αs ρ ∧ PlaceViewsL s σ αs ls ρ ∧
      (∀ e ∈ τ, ∀ ψ, DeepAt ρ e.l ψ → ψ.kind = Kind.own ∧ ¬ ExAt ρ e.l ψ) ∧ ρ.InStratum a) :
    TabAtS σ αs ρ₂ ∧ PlaceViewsL s σ αs ls ρ₂ ∧
      (∀ e ∈ τ, ∀ ψ, DeepAt ρ₂ e.l ψ → ψ.kind = Kind.own ∧ ¬ ExAt ρ₂ e.l ψ) ∧
      ρ₂.InStratum a :=
  pushFactsB_left (ResU.CompS.comm hc) h

/-- **A value reaching no `U` across a block push**: `monoOwnUFree_go_len`'s recursion at a
block. -/
theorem monoOwnUFreeB_go (p : Placement) (τ : LStack) (x : LifeVar) (a : Life)
    (hτx : ∀ e ∈ τ, e.x = x) : ∀ (A : VTy)
    (η η' : Option (Nat → WEnt)) (σ : LStack) (δ : LSub) (αs : List Life) (ls : List SRec)
    (v : Val) (ρ : WRes),
    UFreeM A → EnvPushB η η' σ δ αs ls τ x a → αs.length = σ.length →
    SubFresh δ a → StackPayAvoids x σ → ¬ VFree x A →
    (TabAtS σ αs ρ ∧ PlaceViewsL (extS δ σ αs) σ αs ls ρ ∧
      (∀ e ∈ τ, ∀ ψ, DeepAt ρ e.l ψ → ψ.kind = Kind.own ∧ ¬ ExAt ρ e.l ψ) ∧ ρ.InStratum a) →
    vRLM (ℍ := ℍ) p η σ δ A αs ls v ρ →
      vRLM (ℍ := ℍ) p η' (τ ++ σ) δ A (blockL τ a ++ αs) ls v ρ := by
  intro A
  induction A using VTy.recV with
  | thunk C => intro _ _ _ _ _ _ _ _ hu; exact hu.elim
  | tensor A B ihA ihB =>
      intro η η' σ δ αs ls v ρ hu hE hok hsf hσ hx hF h
      obtain ⟨v₁, v₂, hsep⟩ := h
      obtain ⟨rfl, ρ₁, ρ₂, hc, h₁, h₂⟩ := pure_sep_iff.mp hsep
      exact ⟨v₁, v₂, pure_sep_mk rfl ⟨ρ₁, ρ₂, hc,
        ihA η η' σ δ αs ls v₁ ρ₁ hu.1 hE hok hsf hσ (fun h' => hx (Or.inl h'))
          (pushFactsB_left hc hF) h₁,
        ihB η η' σ δ αs ls v₂ ρ₂ hu.2 hE hok hsf hσ (fun h' => hx (Or.inr h'))
          (pushFactsB_right hc hF) h₂⟩⟩
  | sum A B ihA ihB =>
      intro η η' σ δ αs ls v ρ hu hE hok hsf hσ hx hF h
      rcases h with ⟨v₁, hsep⟩ | ⟨v₂, hsep⟩
      · obtain ⟨rfl, h₁⟩ := pure_sep_iff.mp hsep
        exact Or.inl ⟨v₁, pure_sep_mk rfl
          (ihA η η' σ δ αs ls v₁ ρ hu.1 hE hok hsf hσ (fun h' => hx (Or.inl h')) hF h₁)⟩
      · obtain ⟨rfl, h₂⟩ := pure_sep_iff.mp hsep
        exact Or.inr ⟨v₂, pure_sep_mk rfl
          (ihB η η' σ δ αs ls v₂ ρ hu.2 hE hok hsf hσ (fun h' => hx (Or.inr h')) hF h₂)⟩
  | bang A ih =>
      intro η η' σ δ αs ls v ρ hu hE hok hsf hσ hx hF h
      exact ⟨h.1, ih η η' σ δ αs ls v ρ hu hE hok hsf hσ hx hF h.2.1,
        pBox_of_not_thunk fun C hC => by subst hC; exact hu⟩
  | box b A ih =>
      intro η η' σ δ αs ls v ρ hu hE hok hsf hσ hx hF h
      obtain ⟨α, hα, hv, hout⟩ := h
      have hb : b.mentions x = false := by
        cases hm : b.mentions x
        · rfl
        · exact absurd (Or.inl hm) hx
      refine ⟨α, ?_, ih η η' σ δ αs ls v ρ hu hE hok hsf hσ (fun h' => hx (Or.inr h')) hF hv,
        hout⟩
      show b.interp (extS δ (τ ++ σ) (blockL τ a ++ αs)) = some α
      rw [interp_congr b (fun y hy => extS_blockPush_ne hτx (fun hxy => by
        rw [← hxy] at hy; rw [hb] at hy; exact absurd hy (by decide)))]
      exact hα
  | ref A ih =>
      intro η η' σ δ αs ls v ρ hu hE hok hsf hσ hx hF h
      obtain ⟨ℓ, v', hsep⟩ := h
      obtain ⟨rfl, ρo, ρa, hc, hown, ha⟩ := pure_sep_iff.mp hsep
      exact ⟨ℓ, v', pure_sep_mk rfl ⟨ρo, ρa, hc, hown,
        ih η η' σ δ αs ls v' ρa hu hE hok hsf hσ hx (pushFactsB_right hc hF) ha⟩⟩
  | «mut» b T _ =>
      intro η η' σ δ αs ls v ρ _ hE hok hsf hσ hx hF h
      rw [vRLM_mut_eq] at h ⊢
      rw [wClose_congr hE.1]
      refine vRLJ_leaf_pushB_len (Or.inl ⟨b, _, rfl⟩) ?_ hτx hok hsf hF.2.2.1 hσ h
      rintro (hm | hT)
      · exact hx (Or.inl hm)
      · exact not_vFree_wClose (fun h' => hx (Or.inr h')) hE.2.1 hT
  | imm b T _ =>
      intro η η' σ δ αs ls v ρ _ hE hok hsf hσ hx hF h
      rw [vRLM_imm_eq] at h ⊢
      rw [wClose_congr hE.1]
      refine vRLJ_leaf_pushB_len (Or.inr ⟨b, _, rfl⟩) ?_ hτx hok hsf hF.2.2.1 hσ h
      rintro (hm | hT)
      · exact hx (Or.inl hm)
      · exact not_vFree_wClose (fun h' => hx (Or.inr h')) hE.2.1 hT
  | unit =>
      intro η η' σ δ αs ls v ρ _ _ _ _ _ _ _ h
      show vC true .unit ls (extS δ (τ ++ σ) (blockL τ a ++ αs)) v ρ
      rw [vC_congr .unit (δ₂ := extS δ σ αs) (fun y hy => hy.elim)]; exact h
  | int w =>
      intro η η' σ δ αs ls v ρ _ _ _ _ _ _ _ h
      show vC true (.int w) ls (extS δ (τ ++ σ) (blockL τ a ++ αs)) v ρ
      rw [vC_congr (.int w) (δ₂ := extS δ σ αs) (fun y hy => hy.elim)]; exact h
  | opq k =>
      intro η η' σ δ αs ls v ρ _ _ _ _ _ _ _ h
      show vC true (.opq k) ls (extS δ (τ ++ σ) (blockL τ a ++ αs)) v ρ
      rw [vC_congr (.opq k) (δ₂ := extS δ σ αs) (fun y hy => hy.elim)]; exact h
  | unk =>
      intro η η' σ δ αs ls v ρ _ _ _ _ _ _ _ h
      show vC true .unk ls (extS δ (τ ++ σ) (blockL τ a ++ αs)) v ρ
      rw [vC_congr .unk (δ₂ := extS δ σ αs) (fun y hy => hy.elim)]; exact h
  | zero => intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h; exact h.elim
  | tvar n =>
      intro η η' σ δ αs ls v ρ _ hE _ _ _ _ hF h
      exact hE.2.2 n v ρ hF.1 hF.2.1 hF.2.2.1 hF.2.2.2 h
  | fam L ih =>
      intro η η' σ δ αs ls v ρ hu hE hok hsf hσ hx hF h
      obtain ⟨ℓ, c, hsep⟩ := h
      obtain ⟨⟨rfl, hcn⟩, hs⟩ := pure_sep_iff.mp hsep
      refine ⟨ℓ, c, pure_sep_mk ⟨rfl, hcn⟩ ?_⟩
      exact sepRange_mono_down
        (R := fun ρ' => TabAtS σ αs ρ' ∧ PlaceViewsL (extS δ σ αs) σ αs ls ρ' ∧
          (∀ e ∈ τ, ∀ ψ, DeepAt ρ' e.l ψ → ψ.kind = Kind.own ∧ ¬ ExAt ρ' e.l ψ) ∧ ρ'.InStratum a)
        (fun a₁ a₂ a' hc hR => ⟨pushFactsB_left hc hR, pushFactsB_right hc hR⟩)
        (fun m ρ' hR hm => ih η η' σ δ αs ls (.loc m) ρ' hu hE hok hsf hσ hx hR hm) hF hs
  | mu A ih =>
      intro η η' σ δ αs ls v ρ hu hE hok hsf hσ hx hF h
      obtain ⟨hnm, hcl, hlfp⟩ := h
      let P' : Val → WProp := fun v ρ => vRLM (ℍ := ℍ) p η σ δ (.mu A) αs ls v ρ ∧
        (TabAtS σ αs ρ → PlaceViewsL (extS δ σ αs) σ αs ls ρ →
          (∀ e ∈ τ, ∀ ψ, DeepAt ρ e.l ψ → ψ.kind = Kind.own ∧ ¬ ExAt ρ e.l ψ) →
          ρ.InStratum a → vRLM (ℍ := ℍ) p η' (τ ++ σ) δ (.mu A) (blockL τ a ++ αs) ls v ρ)
      have hxM : ¬ VFree x (wClose η (.mu A)) := not_vFree_wClose hx hE.2.1
      have hE₁ : EnvPushB (some (VTy.scons ⟨wClose η (.mu A), P'⟩ (wEnv η)))
          (some (VTy.scons ⟨wClose η' (.mu A),
            vRLM (ℍ := ℍ) p η' (τ ++ σ) δ (.mu A) (blockL τ a ++ αs) ls⟩ (wEnv η'))) σ δ αs ls
            τ x a := by
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
          exact ih _ _ σ δ αs ls v' ρ' hu hE₁ hok hsf hσ hx ⟨ht', hpv', hpf', hin'⟩ h'
      exact (hlfp P' hclosed).2 hF.1 hF.2.1 hF.2.2.1 hF.2.2.2

/-- **A context reaching no `U` across a block push**: `monoOwnUFreeB_go` at each live slot. -/
theorem monoOwnGUFreeMB (p : Placement) {σ : LStack} {δ : LSub} {Γ : Ctx VTy} {γ : List Val}
    {αs : List Life} {ls : List SRec} {ρ : WRes} {τ : LStack} {x : LifeVar} {a : Life}
    (hτx : ∀ e ∈ τ, e.x = x) (hσ : StackPayAvoids x σ)
    (hU : ∀ s ∈ Γ, s.live = true → UFreeM s.ty) (hok : αs.length = σ.length)
    (hfr : ∀ s ∈ Γ, s.live = true → ¬ VFree x s.ty) (hsf : SubFresh δ a)
    (hF : TabAtS σ αs ρ ∧ PlaceViewsL (extS δ σ αs) σ αs ls ρ ∧
      (∀ e ∈ τ, ∀ ψ, DeepAt ρ e.l ψ → ψ.kind = Kind.own ∧ ¬ ExAt ρ e.l ψ) ∧ ρ.InStratum a)
    (hg : gRLM (ℍ := ℍ) p σ δ αs ls Γ γ ρ) :
    gRLM (ℍ := ℍ) p (τ ++ σ) δ (blockL τ a ++ αs) ls Γ γ ρ := by
  obtain ⟨hlw, hgs⟩ := pure_sep_iff.mp hg
  refine pure_sep_mk hlw ?_
  clear hg hlw
  induction Γ generalizing γ ρ with
  | nil => cases γ <;> exact hgs
  | cons s Γ ih =>
      cases γ with
      | nil => exact hgs
      | cons v γ =>
          have hU' : ∀ s' ∈ Γ, s'.live = true → UFreeM s'.ty :=
            fun s' hs' hl => hU s' (List.mem_cons_of_mem _ hs') hl
          have hfr' : ∀ s' ∈ Γ, s'.live = true → ¬ VFree x s'.ty :=
            fun s' hs' hl => hfr s' (List.mem_cons_of_mem _ hs') hl
          by_cases hl : s.live = true
          · simp only [gSepRLM, hl, if_true] at hgs ⊢
            obtain ⟨ρ₁, ρ₂, hc, h₁, h₂⟩ := hgs
            exact ⟨ρ₁, ρ₂, hc,
              monoOwnUFreeB_go p τ x a hτx s.ty none none σ δ αs ls v ρ₁
                (hU s List.mem_cons_self hl) (envPushBNone σ δ αs ls τ x a) hok hsf hσ
                (hfr s List.mem_cons_self hl) (pushFactsB_left hc hF) h₁,
              ih hU' hfr' (pushFactsB_right hc hF) h₂⟩
          · simp only [gSepRLM, hl] at hgs ⊢
            exact ih hU' hfr' hF hgs

/-- **`MonoOwnGUFreeMA` at every stack with one lifetime per entry**, blocks admitted below the
push: `monoOwnUFree_go_len` at each live slot. -/
theorem monoOwnGUFreeMA_len (p : Placement) {σ : LStack} {δ : LSub} {Γ : Ctx VTy} {γ : List Val}
    {αs : List Life} {ls : List SRec} {ρ : WRes} {C : CTy} {e : LEnt} {a : Life}
    (hσ : StackPayAvoids e.x σ) (hU : ∀ s ∈ Γ, s.live = true → UFreeM s.ty)
    (hok : αs.length = σ.length) (hpush : OwnPushI δ C ρ (σ, αs) e a) (hfr : CtxFresh e.x Γ)
    (hsf : SubFresh δ a) (ht : TabAtS σ αs ρ) (hpv : PlaceViewsL (extS δ σ αs) σ αs ls ρ)
    (hg : gRLM (ℍ := ℍ) p σ δ αs ls Γ γ ρ) : gRLM (ℍ := ℍ) p (e :: σ) δ (a :: αs) ls Γ γ ρ := by
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
                monoOwnUFree_go_len p e a s.ty none none σ δ αs ls v ρ₁
                  (hU' s List.mem_cons_self hl) (envPushNone σ δ αs ls e a) hok hoi.chain hsf hσ
                  (hfr' s List.mem_cons_self hl).1 (pushFacts_left hc hF) h₁,
                ih γ ρ₂ hU'' hfr'' (pushFacts_right hc hF) h₂⟩
            · simp only [gSepRLM, hl] at h ⊢
              exact ih γ ρ hU'' hfr'' hF h
  exact key Γ γ ρ hU hfr ⟨ht, hpv, hoi.placeFree, hoi.below⟩ hgs

end ProbeD1

end
