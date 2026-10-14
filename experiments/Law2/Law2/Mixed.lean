import GhostEnd.StackStep
import Law2.Kappa

/-!
# Law2 — a mixed stack of lends folds back to `ewpTS`, by one induction on the stack

A suspended computation may hold several lends open across a stop, nested: `mut` lends of distinct
places, `imm` lends, and reborrows of a place an outer entry already lends. GhostEnd's stacked
piece (`OpenS`, D16.1) reads such a computation with the stack `σ` of open lends as a parameter,
and proves one commutation step per kind of entry, at every stack:

* `stack_step_other`: a `mut` lend of a place `σ` does not hold (6.65 at a resuming table);
* `stack_step_imm`: an `imm` lend of such a place (6.64 at a resuming table);
* `stack_step_reborrow`: a `mut` reborrow of the place the next entry lends `mut` (6.66, then 6.65).

`fold_other` folds a stack of `mut` lends of distinct places. `fold_mixed` folds **every stack
mixing the three kinds** (`MixedStack`), by one induction on the stack: each entry is folded by its
own step, the owners of the entries that are not reborrows beside the piece (`ownersM`) and in its
answer (`withOwnersM`). There is no case on the depth: the three steps are statements at every
stack, and the induction carries the piece at every `Ext`-extension of the list, which the `imm`
step asks for and the other two keep.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Law2
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Kont Head)
open BoCa.Lifetime (LifeVar LifeCtx LSub)
open GhostEnd

/-- **A mixed stack of lends**, innermost first: each entry is a `mut` lend of a place no outer
entry holds, an `imm` lend of such a place, or a `mut` reborrow of the place the next entry lends
`mut`, at the same payload. -/
inductive MixedStack : LStack → Prop
  | nil : MixedStack []
  | mutOther {e : LEnt} {σ : LStack} :
      e.k = .mut → e.l ∉ σ.map LEnt.l → MixedStack σ → MixedStack (e :: σ)
  | immOther {e : LEnt} {σ : LStack} {v : Val} :
      e.k = .imm v → e.l ∉ σ.map LEnt.l → MixedStack σ → MixedStack (e :: σ)
  | reborrow {e eh : LEnt} {σ₀ : LStack} :
      e.k = .mut → eh.k = .mut → e.l = eh.l → e.T = eh.T → MixedStack (eh :: σ₀) →
      MixedStack (e :: eh :: σ₀)

/-- Whether an entry reborrows the place of the next entry. -/
def Reb (e : LEnt) (σ : LStack) : Prop := σ.head?.map LEnt.l = some e.l

instance (e : LEnt) (σ : LStack) : Decidable (Reb e σ) := by unfold Reb; infer_instance

/-- The owners a stack's lenders hold: one per entry that is not a reborrow (6.65's
`∃w. ℓ ↦ w ⋆ 𝒱⟦T⟧(w)`, 6.64's `ℓ ↦ v ⋆ 𝒱⟦T⟧(v)`). -/
def ownersM (δ : LSub) : LStack → List SRec → WProp
  | [], _ => emp
  | e :: σ, ls => (if Reb e σ then emp else ownerE δ e ls) ⋆ ownersM δ σ ls

/-- An answer with the owners of a stack's lenders beside it, innermost handed back first. -/
def withOwnersM (δ : LSub) : LStack → (List SRec → Val → WProp) → List SRec → Val → WProp
  | [], Q => Q
  | e :: σ, Q => withOwnersM δ σ (if Reb e σ then Q else fun ls v => ownerE δ e ls ⋆ Q ls v)

theorem not_reb_of_not_mem {e : LEnt} {σ : LStack} (h : e.l ∉ σ.map LEnt.l) : ¬ Reb e σ := by
  intro hr
  cases σ with
  | nil => simp [Reb] at hr
  | cons eh σ' =>
      simp only [Reb, List.head?_cons, Option.map_some, Option.some.injEq] at hr
      exact h (by rw [← hr]; exact List.mem_map_of_mem (List.mem_cons_self))

theorem reb_cons {e eh : LEnt} {σ₀ : LStack} (h : e.l = eh.l) : Reb e (eh :: σ₀) := by
  simp [Reb, h]

theorem ownerE_local {δ : LSub} {e : LEnt} {ls ls' : List SRec} {ρ : WRes} (he : Ext ls ls' ρ)
    (h : ownerE δ e ls ρ) : ownerE δ e ls' ρ := by
  unfold ownerE at h ⊢
  cases hk : e.k with
  | «mut» => rw [hk] at h; exact owner_local he h
  | imm v => rw [hk] at h; exact ownerI_local he h

section fold
variable {δ : LSub} {Tab : OpTab}

/-- **A mixed stack folds back to `ewpTS`, by one induction on the stack.** D16.1's piece at a
mixed stack, given at every `Ext`-extension of the list, every stop crossing every entry, beside
the owners of the entries that are not reborrows, is the piece's `ewpTS`, answering with those
owners. Each entry is folded by the step of its kind; the base is `openS_nil_ewp`. -/
theorem fold_mixed (hLR : LinResume Tab) (hL : Tab.Local) {β : Life} :
    ∀ {σ : LStack}, MixedStack σ → AllCross σ Tab →
    (∀ e ∈ σ, ∀ ls w ρ, vCE (ℍ := ℍ) none true e.T ls δ w ρ → ρ.InStratum β) →
    (∀ e ∈ σ, ∀ v, e.k = .imm v → AdmWf e.T δ) →
    ∀ (Qa : List SRec → Val → WProp), (∀ ls₁ ls₂ u ρ, Ext ls₁ ls₂ ρ → Qa ls₁ u ρ → Qa ls₂ u ρ) →
    ∀ (ds : List Bool) (bs : List Life), ds.length = σ.length → bs.length = σ.length →
      (∀ a ∈ bs, a ≤ β) →
      ∀ (ls : List SRec) (e : Expr) (ρo ρ ρt : WRes), ownersM (ℍ := ℍ) δ σ ls ρo →
        (∀ ls₁, Ext ls ls₁ ρ →
          OpenS (ℍ := ℍ) δ σ Tab (cbQ δ σ Qa) σ.length ds bs [] ls₁ e ρ) →
        ResU.CompS ρo ρ ρt → ewpTS (ℍ := ℍ) ls e (opTable Tab) (withOwnersM δ σ Qa) ρt := by
  intro σ hσ
  induction hσ with
  | nil =>
      intro _ _ _ Qa _ ds bs hd hb _ ls e ρo ρ ρt ho h hc
      obtain rfl : ds = [] := List.eq_nil_of_length_eq_zero hd
      obtain rfl : bs = [] := List.eq_nil_of_length_eq_zero hb
      obtain ⟨rfl, -⟩ := ho
      rw [eq_of_compS_empty_left hc]
      exact openS_nil_ewp (h ls (Ext.refl ls ρ))
  | @mutOther en σ hk hl hσ ih =>
      intro hx hP hadm Qa hQa ds bs hd hb hβ ls e ρo ρ ρt ho h hc
      obtain ⟨l', x', T', k', cr'⟩ := en
      simp only at hk hl
      subst hk
      obtain ⟨d, ds, rfl⟩ : ∃ d ds', ds = d :: ds' := by
        cases ds with
        | nil => simp at hd
        | cons d ds' => exact ⟨d, ds', rfl⟩
      obtain ⟨b, bs, rfl⟩ : ∃ b bs', bs = b :: bs' := by
        cases bs with
        | nil => simp at hb
        | cons b bs' => exact ⟨b, bs', rfl⟩
      have hnr : ¬ Reb ⟨l', x', T', .mut, cr'⟩ σ := not_reb_of_not_mem hl
      obtain ⟨o, os, hco, ho', hos⟩ := ho
      rw [if_neg hnr] at ho'
      obtain ⟨y, hy, hcy⟩ := compS_exch hco hc
      have hP' := hP _ (List.mem_cons_self ..)
      have hβ' : ∀ a ∈ bs.getLast?, a ≤ β :=
        fun a ha => hβ a (List.mem_cons_of_mem _ (List.mem_of_getLast? ha))
      have hstep : ∀ ls₁, Ext ls ls₁ y →
          OpenS δ σ Tab (cbQ δ σ fun ls v => owner l' T' δ ls ⋆ Qa ls v) σ.length ds bs [] ls₁ e
            y :=
        fun ls₁ he => stack_step_other hLR (σ := σ) hx hl hP' hβ'
          (owner_local (Ext.left hy he) ho') (h ls₁ (Ext.right hy he)) hy
      have hQa' : ∀ ls₁ ls₂ u ρ, Ext ls₁ ls₂ ρ →
          (fun ls v => owner l' T' δ ls ⋆ Qa ls v) ls₁ u ρ →
          (fun ls v => owner l' T' δ ls ⋆ Qa ls v) ls₂ u ρ :=
        fun _ _ _ _ he ⟨a, b, hcab, ha, hb⟩ =>
          ⟨a, b, hcab, owner_local (he.left hcab) ha, hQa _ _ _ _ (he.right hcab) hb⟩
      have := ih hx.tail (fun e he => hP e (List.mem_cons_of_mem _ he))
        (fun e he => hadm e (List.mem_cons_of_mem _ he)) _ hQa' ds bs (by simpa using hd)
        (by simpa using hb) (fun a ha => hβ a (List.mem_cons_of_mem _ ha)) ls e os y ρt hos
        hstep (ResU.CompS.comm hcy)
      simp only [withOwnersM, if_neg hnr]
      exact this
  | @immOther en σ v hk hl hσ ih =>
      intro hx hP hadm Qa hQa ds bs hd hb hβ ls e ρo ρ ρt ho h hc
      obtain ⟨l', x', T', k', cr'⟩ := en
      simp only at hk hl
      subst hk
      obtain ⟨d, ds, rfl⟩ : ∃ d ds', ds = d :: ds' := by
        cases ds with
        | nil => simp at hd
        | cons d ds' => exact ⟨d, ds', rfl⟩
      obtain ⟨b, bs, rfl⟩ : ∃ b bs', bs = b :: bs' := by
        cases bs with
        | nil => simp at hb
        | cons b bs' => exact ⟨b, bs', rfl⟩
      have hnr : ¬ Reb ⟨l', x', T', .imm v, cr'⟩ σ := not_reb_of_not_mem hl
      obtain ⟨o, os, hco, ho', hos⟩ := ho
      rw [if_neg hnr] at ho'
      obtain ⟨y, hy, hcy⟩ := compS_exch hco hc
      have hP' := hP _ (List.mem_cons_self ..)
      have hadm' : AdmWf T' δ := hadm _ (List.mem_cons_self ..) v rfl
      have hβ' : ∀ a ∈ bs.getLast?, a ≤ β :=
        fun a ha => hβ a (List.mem_cons_of_mem _ (List.mem_of_getLast? ha))
      have hstep : ∀ ls₁, Ext ls ls₁ y →
          OpenS δ σ Tab (cbQ δ σ fun ls u => ownerI l' v T' δ ls ⋆ Qa ls u) σ.length ds bs []
            ls₁ e y :=
        fun ls₁ he => stack_step_imm hLR hL (σ := σ) hx hl hadm' hP' hQa hβ'
          (ownerI_local (Ext.left hy he) ho')
          (fun ls₂ he₂ => h ls₂ (Ext.trans (Ext.right hy he) he₂)) hy
      have hQa' : ∀ ls₁ ls₂ u ρ, Ext ls₁ ls₂ ρ →
          (fun ls u => ownerI l' v T' δ ls ⋆ Qa ls u) ls₁ u ρ →
          (fun ls u => ownerI l' v T' δ ls ⋆ Qa ls u) ls₂ u ρ :=
        fun _ _ _ _ he ⟨a, b, hcab, ha, hb⟩ =>
          ⟨a, b, hcab, ownerI_local (he.left hcab) ha, hQa _ _ _ _ (he.right hcab) hb⟩
      have := ih hx.tail (fun e he => hP e (List.mem_cons_of_mem _ he))
        (fun e he => hadm e (List.mem_cons_of_mem _ he)) _ hQa' ds bs (by simpa using hd)
        (by simpa using hb) (fun a ha => hβ a (List.mem_cons_of_mem _ ha)) ls e os y ρt hos
        hstep (ResU.CompS.comm hcy)
      simp only [withOwnersM, if_neg hnr]
      exact this
  | @reborrow en eh σ₀ hk hkh hll hTT hσ ih =>
      intro hx hP hadm Qa hQa ds bs hd hb hβ ls e ρo ρ ρt ho h hc
      obtain ⟨l, x, T, k, cr⟩ := en
      obtain ⟨lh, xh, Th, kh, crh⟩ := eh
      simp only at hk hkh hll hTT
      subst hk hkh hll hTT
      obtain ⟨d, dh, ds, rfl⟩ : ∃ d dh ds', ds = d :: dh :: ds' := by
        match ds, hd with
        | d :: dh :: ds', _ => exact ⟨d, dh, ds', rfl⟩
      obtain ⟨b, bh, bs, rfl⟩ : ∃ b bh bs', bs = b :: bh :: bs' := by
        match bs, hb with
        | b :: bh :: bs', _ => exact ⟨b, bh, bs', rfl⟩
      have hr : Reb ⟨l, x, T, .mut, cr⟩ (⟨l, xh, T, .mut, crh⟩ :: σ₀) := reb_cons rfl
      obtain ⟨o, os, hco, ho', hos⟩ := ho
      rw [if_pos hr] at ho'
      obtain ⟨rfl, -⟩ := ho'
      rw [eq_of_compS_empty_left hco] at hc
      have hstep : ∀ ls₁, Ext ls ls₁ ρ →
          OpenS δ (⟨l, xh, T, .mut, crh⟩ :: σ₀) Tab (cbQ δ (⟨l, xh, T, .mut, crh⟩ :: σ₀) Qa)
            (σ₀.length + 1) (true :: ds) (bh :: bs) [] ls₁ e ρ :=
        fun ls₁ he => stack_step_reborrow hx (hP _ (List.mem_cons_self ..)) (h ls₁ he)
      have := ih hx.tail (fun e he => hP e (List.mem_cons_of_mem _ he))
        (fun e he => hadm e (List.mem_cons_of_mem _ he)) Qa hQa (true :: ds) (bh :: bs)
        (by simpa using hd) (by simpa using hb) (fun a ha => hβ a (List.mem_cons_of_mem _ ha))
        ls e os ρ ρt hos hstep hc
      simp only [withOwnersM, if_pos hr]
      exact this

end fold

end Law2

end
