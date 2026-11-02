import Support.Model.Tree.CarrierGraft

/-!
# `✓` carried along a relation between carriers

`ResUT.Valid.graft` carries `✓` along the map `trU`. The walks it carries read only a cell's
tag, its value and its witness (`CellUT.compatS_iff`, `CellUT.compatR_iff`), and the witness
only up to equality. So `✓` is carried along any relation `W` between witnesses in `K` and in
`K'` that is single-valued and relates witnesses cell by cell, with tags and values kept
(`WitRel`). The re-reading of `Tree/KSem.lean`, which replaces the stored predicate of each
`mut` cell, is such a relation.

The proofs are `Tree/CarrierGraft.lean`'s, with `TSim`/`RSim` read through `W`.
-/

noncomputable section

namespace BoCa.Fig16.Tree
open BoCa.Fig16

variable {Loc Val : Type} {K K' : WCactus}

variable (Loc Val K K') in
/-- A single-valued relation between witnesses that relates them cell by cell, keeping tags and
values. -/
structure WitRel where
  /-- `W χ χ'`: `χ'` in `K'` is related to `χ` in `K`. -/
  W : ResUT Loc Val K → ResUT Loc Val K' → Prop
  /-- Single-valued. -/
  func : ∀ {a b c}, W a b → W a c → b = c
  /-- Cell by cell: tag, value, and the witnesses related again. -/
  pt : ∀ {a b}, W a b → ∀ l, Option.Rel
    (fun (ψ' : CellUT Loc Val K') (ψ : CellUT Loc Val K) =>
      ψ'.kind = ψ.kind ∧ ψ'.erase = ψ.erase ∧ W ψ.wit ψ'.wit) (b.get l) (a.get l)

namespace WitRel

variable (W : WitRel Loc Val K K')

/-- `ψ'` agrees with `ψ` on everything the definedness of `▶◀` and `⋈` reads. -/
def TSim (ψ' : CellUT Loc Val K') (ψ : CellUT Loc Val K) : Prop :=
  ψ'.kind = ψ.kind ∧ ψ'.erase = ψ.erase ∧ W.W ψ.wit ψ'.wit

/-- Resources related cell by cell. -/
def RSim (ρ' : ResUT Loc Val K') (ρ : ResUT Loc Val K) : Prop :=
  ∀ l, Option.Rel W.TSim (ρ'.get l) (ρ.get l)

theorem rsim_of_W {a : ResUT Loc Val K} {b : ResUT Loc Val K'} (h : W.W a b) : W.RSim b a :=
  W.pt h

variable {W}

theorem wtsim_compatS {ψ₁ ψ₂ : CellUT Loc Val K} {ψ₁' ψ₂' : CellUT Loc Val K'}
    (h₁ : W.TSim ψ₁' ψ₁) (h₂ : W.TSim ψ₂' ψ₂) (h : CellUT.CompatS ψ₁ ψ₂) :
    CellUT.CompatS ψ₁' ψ₂' := by
  obtain ⟨k₁, k₂, hv, hw⟩ := CellUT.compatS_iff.mp h
  exact CellUT.compatS_iff.mpr ⟨h₁.1.trans k₁, h₂.1.trans k₂, h₁.2.1.trans (hv.trans h₂.2.1.symm),
    W.func h₁.2.2 (hw ▸ h₂.2.2)⟩

theorem wtsim_compatR {ψ₁ ψ₂ : CellUT Loc Val K} {ψ₁' ψ₂' : CellUT Loc Val K'}
    (h₁ : W.TSim ψ₁' ψ₁) (h₂ : W.TSim ψ₂' ψ₂) (h : CellUT.CompatR ψ₁ ψ₂) :
    CellUT.CompatR ψ₁' ψ₂' := by
  obtain ⟨hv, hw⟩ := CellUT.compatR_iff.mp h
  refine CellUT.compatR_iff.mpr ⟨h₁.2.1.trans (hv.trans h₂.2.1.symm), fun k₁ k₂ => ?_⟩
  exact W.func h₁.2.2 (hw (h₁.1 ▸ k₁) (h₂.1 ▸ k₂) ▸ h₂.2.2)

theorem wtsim_compS {ψ₁ ψ₂ ψ : CellUT Loc Val K} {ψ₁' ψ₂' : CellUT Loc Val K'}
    (h₁ : W.TSim ψ₁' ψ₁) (h₂ : W.TSim ψ₂' ψ₂) (h : CellUT.CompS ψ₁ ψ₂ ψ) :
    ∃ ψ', CellUT.CompS ψ₁' ψ₂' ψ' ∧ W.TSim ψ' ψ := by
  have k := wtsim_compatS h₁ h₂ h.compat
  have hs := CellUT.compS_spec _ _ k
  refine ⟨_, hs, ?_, ?_, ?_⟩
  · rw [CellUT.CompS.kind hs, CellUT.CompS.kind h]
  · rw [(CellUT.CompS.erase hs).1, (CellUT.CompS.erase h).1, h₁.2.1]
  · rw [(CellUT.CompS.wit hs).1, (CellUT.CompS.wit h).1]; exact h₁.2.2

theorem wtsim_compR {ψ₁ ψ₂ ψ : CellUT Loc Val K} {ψ₁' ψ₂' : CellUT Loc Val K'}
    (h₁ : W.TSim ψ₁' ψ₁) (h₂ : W.TSim ψ₂' ψ₂) (h : CellUT.CompR ψ₁ ψ₂ ψ) :
    ∃ ψ', CellUT.CompR ψ₁' ψ₂' ψ' ∧ W.TSim ψ' ψ := by
  obtain ⟨ψ', hr⟩ := wtsim_compatR h₁ h₂ ⟨ψ, h⟩
  refine ⟨ψ', hr, ?_, ?_, ?_⟩
  · rw [CellUT.CompR.kind_eq hr, CellUT.CompR.kind_eq h, h₁.1, h₂.1]
  · rw [(CellUT.CompR.erase hr).2, (CellUT.CompR.erase h).2, h₁.2.1]
  · rw [CellUT.CompR.wit_eq hr, CellUT.CompR.wit_eq h, h₁.1]
    split
    · exact h₂.2.2
    · exact h₁.2.2

theorem wrsim_empty :
    W.RSim (PMap.empty : ResUT Loc Val K') (PMap.empty : ResUT Loc Val K) :=
  fun _ => Option.Rel.none

theorem wrsim_restrict {ρ' : ResUT Loc Val K'} {ρ : ResUT Loc Val K}
    (h : W.RSim ρ' ρ) (k : Kind) :
    W.RSim (G.restrict CellUT.kind ρ' k) (G.restrict CellUT.kind ρ k) := by
  intro l
  show Option.Rel _ ((ρ'.get l).bind _) ((ρ.get l).bind _)
  have hl := h l
  cases e₁ : ρ'.get l <;> cases e₂ : ρ.get l <;> rw [e₁, e₂] at hl
  · exact Option.Rel.none
  · cases hl
  · cases hl
  · cases hl with
    | some hψ =>
        simp only [Option.bind_some]
        rw [hψ.1]
        split
        · exact Option.Rel.some hψ
        · exact Option.Rel.none

theorem wrsim_sites {ρ' : ResUT Loc Val K'} {ρ : ResUT Loc Val K}
    (h : W.RSim ρ' ρ) {k : Kind} {d : List Loc} (hd : G.Sites CellUT.kind ρ k d) :
    G.Sites CellUT.kind ρ' k d := by
  refine ⟨hd.1, fun l => (hd.2 l).trans ?_⟩
  have hl := h l
  cases e₁ : ρ'.get l <;> cases e₂ : ρ.get l <;> rw [e₁, e₂] at hl
  · simp
  · cases hl
  · cases hl
  · rename_i a b
    cases hl with
    | some hψ =>
        constructor
        · rintro ⟨ψ, e, hk⟩; cases e; exact ⟨a, rfl, hψ.1.trans hk⟩
        · rintro ⟨ψ, e, hk⟩; cases e; exact ⟨b, rfl, hψ.1.symm.trans hk⟩

/-- A composite carried along related operands. -/
theorem wrsim_comp {R : CellUT Loc Val K → CellUT Loc Val K → Prop}
    {C : CellUT Loc Val K → CellUT Loc Val K → CellUT Loc Val K → Prop}
    {R' : CellUT Loc Val K' → CellUT Loc Val K' → Prop}
    {C' : CellUT Loc Val K' → CellUT Loc Val K' → CellUT Loc Val K' → Prop}
    (hR' : ∀ ψ₁ ψ₂ ψ, C' ψ₁ ψ₂ ψ → R' ψ₁ ψ₂)
    (hC : ∀ {ψ₁ ψ₂ ψ ψ₁' ψ₂'}, W.TSim ψ₁' ψ₁ → W.TSim ψ₂' ψ₂ → C ψ₁ ψ₂ ψ →
      ∃ ψ', C' ψ₁' ψ₂' ψ' ∧ W.TSim ψ' ψ)
    {ρ₁ ρ₂ ρ : ResUT Loc Val K} {ρ₁' ρ₂' : ResUT Loc Val K'}
    (h₁ : W.RSim ρ₁' ρ₁) (h₂ : W.RSim ρ₂' ρ₂) (h : G.Comp R C ρ₁ ρ₂ ρ) :
    ∃ ρ', G.Comp R' C' ρ₁' ρ₂' ρ' ∧ W.RSim ρ' ρ := by
  have key : ∀ l, ∃ o, G.OptComp C' (ρ₁'.get l) (ρ₂'.get l) o ∧
      Option.Rel (W.TSim) o (ρ.get l) := by
    intro l
    have hp := h.2 l
    have k₁ := h₁ l
    have k₂ := h₂ l
    revert hp k₁ k₂
    cases ρ₁'.get l <;> cases ρ₁.get l <;> cases ρ₂'.get l <;> cases ρ₂.get l <;>
      intro hp k₁ k₂ <;> cases k₁ <;> cases k₂
    · exact ⟨none, rfl, by rw [show ρ.get l = none from hp]; exact .none⟩
    · rename_i k₂
      exact ⟨_, rfl, by rw [show ρ.get l = some _ from hp]; exact .some k₂⟩
    · rename_i k₁
      exact ⟨_, rfl, by rw [show ρ.get l = some _ from hp]; exact .some k₁⟩
    · rename_i k₁ k₂
      obtain ⟨χ, eχ, hχ⟩ := hp
      obtain ⟨χ', hc, hs⟩ := hC k₁ k₂ hχ
      exact ⟨some χ', ⟨χ', rfl, hc⟩, by rw [eχ]; exact .some hs⟩
  obtain ⟨f, hf⟩ : ∃ f : Loc → Option (CellUT Loc Val K'), ∀ l,
      G.OptComp C' (ρ₁'.get l) (ρ₂'.get l) (f l) ∧ Option.Rel (W.TSim) (f l) (ρ.get l) :=
    ⟨fun l => (key l).choose, fun l => (key l).choose_spec⟩
  have fin : FinDom f := by
    obtain ⟨d, hd⟩ := ρ.finite
    refine ⟨d, fun l hl => hd l fun e => hl ?_⟩
    have := (hf l).2
    rw [e] at this
    revert this
    cases f l with
    | none => intro _; rfl
    | some _ => intro h; cases h
  refine ⟨⟨f, fin⟩, ⟨fun l ψ₁ ψ₂ e₁ e₂ => ?_, fun l => (hf l).1⟩, fun l => (hf l).2⟩
  have := (hf l).1
  rw [e₁, e₂] at this
  obtain ⟨ψ, -, hc⟩ := this
  exact hR' _ _ _ hc

theorem wrsim_bigComp {R : CellUT Loc Val K → CellUT Loc Val K → Prop}
    {C : CellUT Loc Val K → CellUT Loc Val K → CellUT Loc Val K → Prop}
    {R' : CellUT Loc Val K' → CellUT Loc Val K' → Prop}
    {C' : CellUT Loc Val K' → CellUT Loc Val K' → CellUT Loc Val K' → Prop}
    (hR' : ∀ ψ₁ ψ₂ ψ, C' ψ₁ ψ₂ ψ → R' ψ₁ ψ₂)
    (hC : ∀ {ψ₁ ψ₂ ψ ψ₁' ψ₂'}, W.TSim ψ₁' ψ₁ → W.TSim ψ₂' ψ₂ → C ψ₁ ψ₂ ψ →
      ∃ ψ', C' ψ₁' ψ₂' ψ' ∧ W.TSim ψ' ψ)
    {es : List (ResUT Loc Val K)} {b : ResUT Loc Val K} (h : G.BigComp R C es b) :
    ∀ {es' : List (ResUT Loc Val K')}, List.Forall₂ (W.RSim) es' es →
      ∃ b', G.BigComp R' C' es' b' ∧ W.RSim b' b := by
  induction h with
  | nil =>
      intro es' hes
      cases hes
      exact ⟨_, G.BigComp.nil, wrsim_empty⟩
  | cons hrest hcomp ih =>
      intro es' hes
      cases hes with
      | cons hσ hrest' =>
          obtain ⟨τ', hτ', sτ⟩ := ih hrest'
          obtain ⟨ρ', hρ', sρ⟩ := wrsim_comp hR' hC hσ sτ hcomp
          exact ⟨ρ', G.BigComp.cons hτ' hρ', sρ⟩

/-- **The exclusive walk carries over.** -/
theorem ExW.sim {R : CellUT Loc Val K → CellUT Loc Val K → Prop}
    {C : CellUT Loc Val K → CellUT Loc Val K → CellUT Loc Val K → Prop}
    {R' : CellUT Loc Val K' → CellUT Loc Val K' → Prop}
    {C' : CellUT Loc Val K' → CellUT Loc Val K' → CellUT Loc Val K' → Prop}
    (hR' : ∀ ψ₁ ψ₂ ψ, C' ψ₁ ψ₂ ψ → R' ψ₁ ψ₂)
    (hC : ∀ {ψ₁ ψ₂ ψ ψ₁' ψ₂'}, W.TSim ψ₁' ψ₁ → W.TSim ψ₂' ψ₂ → C ψ₁ ψ₂ ψ →
      ∃ ψ', C' ψ₁' ψ₂' ψ' ∧ W.TSim ψ' ψ)
    {ρ σ : ResUT Loc Val K} (h : G.ExW CellUT.kind CellUT.wit R C ρ σ) :
    ∀ ρ', W.RSim ρ' ρ → ∃ σ', G.ExW CellUT.kind CellUT.wit R' C' ρ' σ' ∧ W.RSim σ' σ := by
  refine G.ExW.rec (motive_1 := fun ρ σ _ => ∀ ρ', W.RSim ρ' ρ →
      ∃ σ', G.ExW CellUT.kind CellUT.wit R' C' ρ' σ' ∧ W.RSim σ' σ)
    (motive_2 := fun ρ w _ => ∀ ρ', W.RSim ρ' ρ →
      ∃ w', G.ExWits CellUT.kind CellUT.wit R' C' ρ' w' ∧ w'.map Prod.fst = w.map Prod.fst ∧
        List.Forall₂ (W.RSim) (w'.map Prod.snd) (w.map Prod.snd))
    ?mk ?nil ?cons h
  case mk =>
    intro ρ₀ σ₀ nm b w hs _ hb hnm hσ ih ρ' hρ
    obtain ⟨w', hw', hfst, hsnd⟩ := ih ρ' hρ
    obtain ⟨b', hb', sb⟩ := wrsim_bigComp hR' hC hb hsnd
    obtain ⟨nm', hnm', snm⟩ := wrsim_comp hR' hC (wrsim_restrict hρ _)
      (wrsim_restrict hρ _) hnm
    obtain ⟨σ', hσ', sσ⟩ := wrsim_comp hR' hC snm sb hσ
    exact ⟨σ', G.ExW.mk (hfst ▸ wrsim_sites hρ hs) hw' hb' hnm' hσ', sσ⟩
  case nil =>
    intro ρ₀ ρ' _
    exact ⟨[], G.ExWits.nil, rfl, List.Forall₂.nil⟩
  case cons =>
    intro ρ₀ e l w ψ hψ hk _ _ ihe ihw ρ' hρ
    obtain ⟨w', hw', hfst, hsnd⟩ := ihw ρ' hρ
    have hl := hρ l
    rw [hψ] at hl
    obtain ⟨ψ', eψ', sψ⟩ : ∃ ψ', ρ'.get l = some ψ' ∧ W.TSim ψ' ψ := by
      revert hl
      cases ρ'.get l with
      | none => intro hl; cases hl
      | some ψ' => intro hl; cases hl with | some h => exact ⟨ψ', rfl, h⟩
    obtain ⟨e', he', se⟩ := ihe ψ'.wit (W.rsim_of_W sψ.2.2)
    exact ⟨(l, e') :: w', G.ExWits.cons ψ' eψ' (sψ.1.trans hk) he' hw',
      by simp [hfst], List.Forall₂.cons se hsnd⟩

/-- **The aliasable walk carries over.** -/
theorem AgW.sim {ρ σ : ResUT Loc Val K} (h : AgWT ρ σ) :
    ∀ ρ', W.RSim ρ' ρ → ∃ σ', AgWT ρ' σ' ∧ W.RSim σ' σ := by
  have hR' : ∀ ψ₁ ψ₂ ψ, CellUT.CompR (K := K') (Loc := Loc) (Val := Val) ψ₁ ψ₂ ψ →
      CellUT.CompatR ψ₁ ψ₂ := fun _ _ ψ hc => ⟨ψ, hc⟩
  have hC : ∀ {ψ₁ ψ₂ ψ : CellUT Loc Val K} {ψ₁' ψ₂' : CellUT Loc Val K'},
      W.TSim ψ₁' ψ₁ → W.TSim ψ₂' ψ₂ → CellUT.CompR ψ₁ ψ₂ ψ →
      ∃ ψ', CellUT.CompR ψ₁' ψ₂' ψ' ∧ W.TSim ψ' ψ := fun a b c => wtsim_compR a b c
  refine G.AgW.rec (motive_1 := fun ρ σ _ => ∀ ρ', W.RSim ρ' ρ →
      ∃ σ', AgWT ρ' σ' ∧ W.RSim σ' σ)
    (motive_2 := fun ρ w _ => ∀ ρ', W.RSim ρ' ρ →
      ∃ w', G.AgWitsM CellUT.kind CellUT.wit CellUT.CompatR CellUT.CompR ρ' w' ∧
        w'.map Prod.fst = w.map Prod.fst ∧
        List.Forall₂ (W.RSim) (w'.map Prod.snd) (w.map Prod.snd))
    (motive_3 := fun ρ w _ => ∀ ρ', W.RSim ρ' ρ →
      ∃ w', G.AgWitsI CellUT.kind CellUT.wit CellUT.CompatR CellUT.CompR ρ' w' ∧
        w'.map Prod.fst = w.map Prod.fst ∧
        List.Forall₂ (W.RSim) (w'.map Prod.snd) (w.map Prod.snd))
    ?mk ?nilM ?consM ?nilI ?consI h
  case mk =>
    intro ρ₀ σ₀ a bm bi wm wi hsm hsi _ _ hbm hbi ha hσ ihm ihi ρ' hρ
    obtain ⟨wm', hwm', fm, sm⟩ := ihm ρ' hρ
    obtain ⟨wi', hwi', fi, si⟩ := ihi ρ' hρ
    obtain ⟨bm', hbm', sbm⟩ := wrsim_bigComp hR' hC hbm sm
    obtain ⟨bi', hbi', sbi⟩ := wrsim_bigComp hR' hC hbi si
    obtain ⟨a', ha', sa⟩ := wrsim_comp hR' hC (wrsim_restrict hρ _) sbm ha
    obtain ⟨σ', hσ', sσ⟩ := wrsim_comp hR' hC sa sbi hσ
    exact ⟨σ', G.AgW.mk (fm ▸ wrsim_sites hρ hsm) (fi ▸ wrsim_sites hρ hsi) hwm' hwi'
      hbm' hbi' ha' hσ', sσ⟩
  case nilM => intro ρ₀ ρ' _; exact ⟨[], G.AgWitsM.nil, rfl, List.Forall₂.nil⟩
  case consM =>
    intro ρ₀ e l w ψ hψ hk _ _ ihe ihw ρ' hρ
    obtain ⟨w', hw', hfst, hsnd⟩ := ihw ρ' hρ
    have hl := hρ l
    rw [hψ] at hl
    obtain ⟨ψ', eψ', sψ⟩ : ∃ ψ', ρ'.get l = some ψ' ∧ W.TSim ψ' ψ := by
      revert hl
      cases ρ'.get l with
      | none => intro hl; cases hl
      | some ψ' => intro hl; cases hl with | some h => exact ⟨ψ', rfl, h⟩
    obtain ⟨e', he', se⟩ := ihe ψ'.wit (W.rsim_of_W sψ.2.2)
    exact ⟨(l, e') :: w', G.AgWitsM.cons ψ' eψ' (sψ.1.trans hk) he' hw',
      by simp [hfst], List.Forall₂.cons se hsnd⟩
  case nilI => intro ρ₀ ρ' _; exact ⟨[], G.AgWitsI.nil, rfl, List.Forall₂.nil⟩
  case consI =>
    intro ρ₀ p l w ψ hψ hk e a hex _ hp _ iha ihw ρ' hρ
    obtain ⟨w', hw', hfst, hsnd⟩ := ihw ρ' hρ
    have hl := hρ l
    rw [hψ] at hl
    obtain ⟨ψ', eψ', sψ⟩ : ∃ ψ', ρ'.get l = some ψ' ∧ W.TSim ψ' ψ := by
      revert hl
      cases ρ'.get l with
      | none => intro hl; cases hl
      | some ψ' => intro hl; cases hl with | some h => exact ⟨ψ', rfl, h⟩
    have sw : W.RSim ψ'.wit ψ.wit := W.rsim_of_W sψ.2.2
    obtain ⟨e', he', se⟩ := ExW.sim hR' hC hex ψ'.wit sw
    obtain ⟨a', ha', sa⟩ := iha ψ'.wit sw
    obtain ⟨p', hp', sp⟩ := wrsim_comp hR' hC se sa hp
    exact ⟨(l, p') :: w', G.AgWitsI.cons ψ' eψ' (sψ.1.trans hk) e' a' he' ha' hp' hw',
      by simp [hfst], List.Forall₂.cons sp hsnd⟩

/-- **`✓` carries along `W`**: a world related cell by cell to a valid world is valid. -/
theorem ResUT.Valid.sim {ρ : ResUT Loc Val K} {ρ' : ResUT Loc Val K'} (h : ResUT.Valid ρ)
    (hs : W.RSim ρ' ρ) : ResUT.Valid ρ' := by
  obtain ⟨σ, e, a, he, ha, hσ⟩ := h
  have hRS : ∀ ψ₁ ψ₂ ψ, CellUT.CompS (K := K') (Loc := Loc) (Val := Val) ψ₁ ψ₂ ψ →
      CellUT.CompatS ψ₁ ψ₂ := fun _ _ _ hc => hc.compat
  have hCS : ∀ {ψ₁ ψ₂ ψ : CellUT Loc Val K} {ψ₁' ψ₂' : CellUT Loc Val K'},
      W.TSim ψ₁' ψ₁ → W.TSim ψ₂' ψ₂ → CellUT.CompS ψ₁ ψ₂ ψ →
      ∃ ψ', CellUT.CompS ψ₁' ψ₂' ψ' ∧ W.TSim ψ' ψ := fun a b c => wtsim_compS a b c
  obtain ⟨e', he', se⟩ := ExW.sim hRS hCS he _ hs
  obtain ⟨a', ha', sa⟩ := AgW.sim ha _ hs
  obtain ⟨σ', hσ', -⟩ := wrsim_comp hRS hCS se sa hσ
  exact ⟨σ', e', a', he', ha', hσ'⟩

end WitRel

end BoCa.Fig16.Tree

end
