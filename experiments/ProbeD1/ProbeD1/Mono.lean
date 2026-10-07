import ProbeD1.Views

/-!
# ProbeD1 — monotonicity along W's order (statement 0, per placement)

* **`cbpv` and `binder`** (`monoV_fut`, `monoG_fut`): values and contexts are Kripke along `Fut`.
  At `U` it is by construction (DESIGN §4.3): the clause quantifies over the futures of its stack,
  a future of a future is a future (`Fut` is a closure), and the futures the clause owes at the new
  stack, taken after a re-lend, are futures of the old stack after a re-lend (`futReLend`), at the
  part above the outermost lend (`futPart`), avoiding the type (`futAvoidsTrans`). The witnesses
  are the old ones: the dropped views are the old views at the future, the inserted entries'
  flags off (`vwS_fut`), and the share stays above the outermost lend (`stratS_fut`). The other
  formers are componentwise, and a leaf reads `vC` at `extS δ σ' αs'`, which agrees with
  `extS δ σ αs` at the type's free variables (`extS_find_fut`, `FutAvoidsV`), along `Ext`
  (`vC_local`).
* **`MonoHideFromMonoV`** (`monoHideFromMonoV`): hiding is the one-step future that inserts nothing
  at depth `0`.

`binder0`'s `U` clause ranges over the stack itself, so `MonoV binder0` at a `U` value needs the
forced computation carried to the future, `MonoC binder0`, which at `⊸` reads its argument back at
the old stack under the old stack's guard (DESIGN §4.3). That is not derived here.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace ProbeD1
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open GhostEnd (LEnt LStack LKind extS vwE vwS vis stratS ReLend TabAtS)

/-! ### Bookkeeping -/

/-- A stack's views have one flag and one lifetime per entry. -/
theorem vwS_length {δ : LSub} : ∀ {seen : List BoCa.Loc} {σ : LStack} {ds : List Bool}
    {αs : List Life} {ls : List SRec} {ρ : WRes}, vwS δ seen σ ds αs ls ρ →
    ds.length = σ.length ∧ αs.length = σ.length
  | _, [], [], [], _, _, _ => ⟨rfl, rfl⟩
  | _, _ :: _, _ :: _, _ :: _, _, _, ⟨_, _, _, _, h₂⟩ => by
      have := vwS_length h₂; simp [this.1, this.2]
  | _, [], [], _ :: _, _, _, h => h.elim
  | _, [], _ :: _, [], _, _, h => h.elim
  | _, [], _ :: _, _ :: _, _, _, h => h.elim
  | _, _ :: _, [], [], _, _, h => h.elim
  | _, _ :: _, [], _ :: _, _, _, h => h.elim
  | _, _ :: _, _ :: _, [], _, _, h => h.elim

/-- A re-lend of a stack in shape is in shape. -/
theorem StackOK.reLend {σ : LStack} {αs αs' : List Life} (hok : StackOK σ αs)
    (hr : ReLend αs' αs) : StackOK σ αs' :=
  ⟨hr.1.length_eq.trans hok.1, hr.2, hok.2.2⟩

theorem futQ_true {δ : LSub} {ρ : WRes} {s s' : Stk} : FutQ true δ ρ s s' ↔ Fut δ ρ s s' :=
  Iff.rfl

/-- A future's inserted entries avoid a `U C` exactly when they avoid `C`. -/
theorem futAvoidsV_thunk {C : CTy} {σ σ' : LStack} : FutAvoidsV (.thunk C) σ σ' ↔ FutAvoids C σ σ' :=
  Iff.rfl

/-! ### The `U` clause along a future -/

/-- **The `U` clause over futures is Kripke along `Fut`, by construction.** -/
theorem relendU_fut {own : Bool} {δ : LSub} {σ σ' : LStack} {C : CTy}
    {P : LStack → List Life → List SRec → WProp} {αs αs' : List Life} {ls ls' : List SRec}
    {ρ : WRes} (hok : StackOK σ αs) (he : Ext ls ls' ρ) (hf : Fut δ ρ (σ, αs) (σ', αs'))
    (hav : FutAvoids C σ σ') (h : RelendU true own δ σ C P αs ls ρ) :
    RelendU true own δ σ' C P αs' ls' ρ := by
  obtain ⟨ds, ρz, ρn, hc, hn, hz, H⟩ := h
  have hl : ds.length = σ.length := (vwS_length hn).1
  have hfz : Fut δ ρz (σ, αs) (σ', αs') := futPart δ ρz ρn ρ _ _ hc hf
  refine ⟨futDs σ ds σ', ρz, ρn, hc, ?_, stratS_fut (s := (σ, αs)) hok hfz hz, ?_⟩
  · rw [vwS_fut hok hf hl [] ls']
    exact GhostEnd.vwS_local (he.right hc) hn
  · intro ls'' he' αs₁ hr σ'' αs₂ hf' hav'
    obtain ⟨αs₀, hr₀, hf₀⟩ := futReLend δ ρ σ σ' αs αs' αs₁ hok hf hr
    have hf₀z : Fut δ ρz (σ, αs₀) (σ', αs₁) := futPart δ ρz ρn ρ _ _ hc hf₀
    have hcomp : FutQ true δ ρz (σ, αs₀) (σ'', αs₂) := hf₀z.trans (futQ_true.mp hf')
    obtain ⟨H₁, H₂⟩ := H ls'' ((he.left hc).trans he') αs₀ hr₀ σ'' αs₂ hcomp
      (futAvoidsTrans.1 C σ σ' σ'' hav hav')
    have hv := vwS_fut (hok.reLend hr₀) hf₀z hl [] ls''
    refine ⟨?_, fun hown en a hpush => ?_⟩
    · rw [hv]; exact H₁
    · rw [hv]; exact H₂ hown en a hpush

/-! ### Leaves along a future -/

/-- A future's substitution agrees with the stack's at the free variables of a type it avoids. -/
theorem extS_agree_fut {δ : LSub} {ρ : WRes} {σ σ' : LStack} {αs αs' : List Life}
    (hok : StackOK σ αs) (hf : Fut δ ρ (σ, αs) (σ', αs')) {A : VTy} (hav : FutAvoidsV A σ σ') :
    ∀ y, VFree y A → (extS δ σ αs).find? y = (extS δ σ' αs').find? y := by
  intro y hy
  refine (extS_find_fut hok hf fun hm => ?_).symm
  obtain ⟨e, he, hex⟩ := List.mem_map.mp hm
  by_contra hn
  rw [← hex] at hn hy
  exact (hav e he hn).1 hy

/-- **A leaf along a future**: `vC` at the future's substitution, along `Ext`. -/
theorem vC_fut {δ : LSub} {ρ' : WRes} {σ σ' : LStack} {αs αs' : List Life}
    (hok : StackOK σ αs) (hf : Fut δ ρ' (σ, αs) (σ', αs')) {A : VTy} (hav : FutAvoidsV A σ σ')
    {ls ls' : List SRec} {v : Val} {ρ : WRes} (he : Ext ls ls' ρ)
    (h : vC true A ls (extS δ σ αs) v ρ) : vC true A ls' (extS δ σ' αs') v ρ := by
  rw [← vC_congr A (extS_agree_fut hok hf hav) true ls']
  exact vC_local true A he h

/-! ### `MonoV` and `MonoG` at the placements whose `U` clause ranges over futures -/

section
variable {σ σ' : LStack} {y : LifeVar}

theorem FutAvoidsV.tensor_left {A B : VTy} (h : FutAvoidsV (.tensor A B) σ σ') : FutAvoidsV A σ σ' :=
  fun e he hx => ⟨fun h' => (h e he hx).1 (Or.inl h'),
    fun h' => (h e he hx).2 (List.mem_append_left _ h')⟩

theorem FutAvoidsV.tensor_right {A B : VTy} (h : FutAvoidsV (.tensor A B) σ σ') : FutAvoidsV B σ σ' :=
  fun e he hx => ⟨fun h' => (h e he hx).1 (Or.inr h'),
    fun h' => (h e he hx).2 (List.mem_append_right _ h')⟩

theorem FutAvoidsV.sum_left {A B : VTy} (h : FutAvoidsV (.sum A B) σ σ') : FutAvoidsV A σ σ' :=
  fun e he hx => ⟨fun h' => (h e he hx).1 (Or.inl h'),
    fun h' => (h e he hx).2 (List.mem_append_left _ h')⟩

theorem FutAvoidsV.sum_right {A B : VTy} (h : FutAvoidsV (.sum A B) σ σ') : FutAvoidsV B σ σ' :=
  fun e he hx => ⟨fun h' => (h e he hx).1 (Or.inr h'),
    fun h' => (h e he hx).2 (List.mem_append_right _ h')⟩

theorem FutAvoidsV.bang {A : VTy} (h : FutAvoidsV (.bang A) σ σ') : FutAvoidsV A σ σ' := h

theorem FutAvoidsV.ref {A : VTy} (h : FutAvoidsV (.ref A) σ σ') : FutAvoidsV A σ σ' := h

theorem FutAvoidsV.box {a : Lifetime.Life} {A : VTy} (h : FutAvoidsV (.box a A) σ σ') :
    FutAvoidsV A σ σ' :=
  fun e he hx => ⟨fun h' => (h e he hx).1 (Or.inr h'), (h e he hx).2⟩

end

/-- **`MonoV` at a placement whose `U` clause ranges over futures**, by induction on the type. -/
theorem monoV_fut (p : Placement) (hp : p.uFut = true) : ∀ (A : VTy) (σ : LStack) (δ : LSub)
    (αs : List Life) (ls ls' : List SRec) (v : Val) (ρ : WRes) (σ' : LStack) (αs' : List Life),
    StackOK σ αs → Ext ls ls' ρ → Fut δ ρ (σ, αs) (σ', αs') → FutAvoidsV A σ σ' →
    TabAtS σ αs ρ → vRL p σ δ A αs ls v ρ → vRL p σ' δ A αs' ls' v ρ
  | .thunk C, σ, δ, αs, ls, ls', f, ρ, σ', αs', hok, he, hf, hav, ht, h => by
      have hp' : (p.uFut || p.uOwn) = true := by rw [hp]; rfl
      intro _
      have h' := h ht
      simp only [hp', if_true] at h' ⊢
      rw [hp] at h' ⊢
      exact relendU_fut hok he hf (futAvoidsV_thunk.mp hav) h'
  | .tensor A B, σ, δ, αs, ls, ls', v, ρ, σ', αs', hok, he, hf, hav, ht, h => by
      obtain ⟨v₁, v₂, hs⟩ := h
      obtain ⟨rfl, ρ₁, ρ₂, hc, h₁, h₂⟩ := pure_sep_iff.mp hs
      have ht' := (GhostEnd.tabAtS_comp hc).mp ht
      exact ⟨v₁, v₂, pure_sep_mk rfl ⟨ρ₁, ρ₂, hc,
        monoV_fut p hp A σ δ αs ls ls' v₁ ρ₁ σ' αs' hok (he.left hc)
          (futPart δ ρ₁ ρ₂ ρ _ _ hc hf) hav.tensor_left ht'.1 h₁,
        monoV_fut p hp B σ δ αs ls ls' v₂ ρ₂ σ' αs' hok (he.right hc)
          (futPart δ ρ₂ ρ₁ ρ _ _ (ResU.CompS.comm hc) hf) hav.tensor_right ht'.2 h₂⟩⟩
  | .sum A B, σ, δ, αs, ls, ls', v, ρ, σ', αs', hok, he, hf, hav, ht, h => by
      rcases h with ⟨v₁, hs⟩ | ⟨v₂, hs⟩
      · obtain ⟨rfl, h₁⟩ := pure_sep_iff.mp hs
        exact Or.inl ⟨v₁, pure_sep_mk rfl
          (monoV_fut p hp A σ δ αs ls ls' v₁ ρ σ' αs' hok he hf hav.sum_left ht h₁)⟩
      · obtain ⟨rfl, h₂⟩ := pure_sep_iff.mp hs
        exact Or.inr ⟨v₂, pure_sep_mk rfl
          (monoV_fut p hp B σ δ αs ls ls' v₂ ρ σ' αs' hok he hf hav.sum_right ht h₂)⟩
  | .bang A, σ, δ, αs, ls, ls', v, ρ, σ', αs', hok, he, hf, hav, ht, h => by
      obtain ⟨rfl, h₁⟩ := h
      exact ⟨rfl, monoV_fut p hp A σ δ αs ls ls' v _ σ' αs' hok he hf hav.bang ht h₁⟩
  | .box a A, σ, δ, αs, ls, ls', v, ρ, σ', αs', hok, he, hf, hav, ht, h => by
      obtain ⟨α, hα, hP, hO⟩ := h
      have hint : a.interp (extS δ σ' αs') = a.interp (extS δ σ αs) :=
        (interp_congr a fun x hx => extS_agree_fut hok hf hav x (Or.inl hx)).symm
      exact ⟨α, hint.trans hα,
        monoV_fut p hp A σ δ αs ls ls' v ρ σ' αs' hok he hf hav.box ht hP, hO⟩
  | .ref A, σ, δ, αs, ls, ls', v, ρ, σ', αs', hok, he, hf, hav, ht, h => by
      obtain ⟨ℓ, v', hs⟩ := h
      obtain ⟨rfl, ρ₁, ρ₂, hc, h₁, h₂⟩ := pure_sep_iff.mp hs
      have ht' := (GhostEnd.tabAtS_comp hc).mp ht
      exact ⟨ℓ, v', pure_sep_mk rfl ⟨ρ₁, ρ₂, hc, h₁,
        monoV_fut p hp A σ δ αs ls ls' v' ρ₂ σ' αs' hok (he.right hc)
          (futPart δ ρ₂ ρ₁ ρ _ _ (ResU.CompS.comm hc) hf) hav.ref ht'.2 h₂⟩⟩
  | .unit, _, _, _, _, _, _, _, _, _, hok, he, hf, hav, _, h => vC_fut hok hf hav he h
  | .zero, _, _, _, _, _, _, _, _, _, hok, he, hf, hav, _, h => vC_fut hok hf hav he h
  | .imm _ _, _, _, _, _, _, _, _, _, _, hok, he, hf, hav, _, h => vC_fut hok hf hav he h
  | .mut _ _, _, _, _, _, _, _, _, _, _, hok, he, hf, hav, _, h => vC_fut hok hf hav he h
  | .unk, _, _, _, _, _, _, _, _, _, hok, he, hf, hav, _, h => vC_fut hok hf hav he h
  | .tvar _, _, _, _, _, _, _, _, _, _, hok, he, hf, hav, _, h => vC_fut hok hf hav he h
  | .mu _, _, _, _, _, _, _, _, _, _, hok, he, hf, hav, _, h => vC_fut hok hf hav he h
  | .int _, _, _, _, _, _, _, _, _, _, hok, he, hf, hav, _, h => vC_fut hok hf hav he h
  | .fam _, _, _, _, _, _, _, _, _, _, hok, he, hf, hav, _, h => vC_fut hok hf hav he h
  | .opq _, _, _, _, _, _, _, _, _, _, hok, he, hf, hav, _, h => vC_fut hok hf hav he h

/-- **`MonoV` at `cbpv`.** -/
theorem monoV_cbpv : MonoV (ℍ := ℍ) .cbpv :=
  fun σ δ A αs ls ls' v ρ σ' αs' => monoV_fut .cbpv rfl A σ δ αs ls ls' v ρ σ' αs'

/-- **`MonoV` at `binder`.** -/
theorem monoV_binder : MonoV (ℍ := ℍ) .binder :=
  fun σ δ A αs ls ls' v ρ σ' αs' => monoV_fut .binder rfl A σ δ αs ls ls' v ρ σ' αs'

/-- The separating part of a context follows its values, slot by slot. -/
theorem gSepRL_mono (p : Placement) (hV : MonoV (ℍ := ℍ) p) {σ σ' : LStack} {δ : LSub}
    {αs αs' : List Life} {ls ls' : List SRec} (hok : StackOK σ αs) :
    ∀ (Γ : Ctx VTy) (γ : List Val) (ρ : WRes), (∀ s ∈ Γ, s.live = true → FutAvoidsV s.ty σ σ') →
      Ext ls ls' ρ → Fut δ ρ (σ, αs) (σ', αs') → TabAtS σ αs ρ →
      gSepRL p σ δ αs ls Γ γ ρ → gSepRL p σ' δ αs' ls' Γ γ ρ
  | [], _, _, _, _, _, _, h => h
  | _ :: _, [], _, _, _, _, _, h => h
  | s :: Γ, v :: γ, ρ, hav, he, hf, ht, h => by
      have hav' : ∀ s' ∈ Γ, s'.live = true → FutAvoidsV s'.ty σ σ' :=
        fun s' hs' hl => hav s' (List.mem_cons_of_mem _ hs') hl
      by_cases hl : s.live = true
      · simp only [gSepRL, hl, if_true] at h ⊢
        obtain ⟨ρ₁, ρ₂, hc, h₁, h₂⟩ := h
        have ht' := (GhostEnd.tabAtS_comp hc).mp ht
        exact ⟨ρ₁, ρ₂, hc,
          hV σ δ s.ty αs ls ls' v ρ₁ σ' αs' hok (he.left hc) (futPart δ ρ₁ ρ₂ ρ _ _ hc hf)
            (hav s List.mem_cons_self hl) ht'.1 h₁,
          gSepRL_mono p hV hok Γ γ ρ₂ hav' (he.right hc)
            (futPart δ ρ₂ ρ₁ ρ _ _ (ResU.CompS.comm hc) hf) ht'.2 h₂⟩
      · simp only [gSepRL, hl] at h ⊢
        exact gSepRL_mono p hV hok Γ γ ρ hav' he hf ht h

/-- **Contexts follow their values**: `MonoG` from `MonoV`, slot by slot. -/
theorem monoG_of_monoV (p : Placement) (hV : MonoV (ℍ := ℍ) p) : MonoG (ℍ := ℍ) p := by
  intro σ δ Γ γ αs ls ls' ρ σ' αs' hok he hf hav ht hg
  obtain ⟨hlw, hgs⟩ := pure_sep_iff.mp hg
  exact pure_sep_mk hlw (gSepRL_mono p hV hok Γ γ ρ hav he hf ht hgs)

/-- **`MonoG` at `cbpv`.** -/
theorem monoG_cbpv : MonoG (ℍ := ℍ) .cbpv := monoG_of_monoV .cbpv monoV_cbpv

/-- **`MonoG` at `binder`.** -/
theorem monoG_binder : MonoG (ℍ := ℍ) .binder := monoG_of_monoV .binder monoV_binder

/-! ### Hiding -/

/-- Hiding the names `N` is the one-step future that inserts nothing at depth `0`. -/
theorem fut_hide {δ : LSub} {ρ : WRes} {σ : LStack} {αs : List Life} (hok : StackOK σ αs)
    (N : UInt32 → Bool) : Fut δ ρ (σ, αs) (hideS N σ, αs) := by
  refine Relation.ReflTransGen.single ⟨0, [], [], some N, ?_, ?_, ?_⟩
  · exact
      { len := rfl
        depth_le := Nat.zero_le _
        chain := by simpa [futL] using hok.2.1
        below := fun _ h => absurd h List.not_mem_nil
        vars_stack := fun _ h => absurd h List.not_mem_nil
        vars_sub := fun _ h => absurd h List.not_mem_nil
        nodup := List.nodup_nil
        places := fun _ h => absurd h List.not_mem_nil
        pay := fun _ h => absurd h List.not_mem_nil }
  · show hideS N σ = σ.take 0 ++ [] ++ hideS N (σ.drop 0)
    simp
  · show αs = futL 0 [] αs
    simp [futL]

/-- **`MonoHideFromMonoV`**: hiding is `MonoV`'s instance at the one-step future that inserts
nothing and hides `N` at depth `0`. -/
theorem monoHideFromMonoV : MonoHideFromMonoV (ℍ := ℍ) := by
  intro p hV σ δ A αs ls v ρ N hok ht h
  refine hV σ δ A αs ls ls v ρ (hideS N σ) αs hok (Ext.refl ls ρ) (fut_hide hok N) ?_ ht h
  intro e he hx
  exact absurd (by rw [← hideS_map_x N σ]; exact List.mem_map_of_mem he) hx

end ProbeD1

end
