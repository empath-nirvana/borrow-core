import Support.Model.Tree.World.Records

/-!
# The walks carried along a re-reading, with each `imm` cell's lifetimes

`[spec §62]`. `Tree/CarrierSim.lean` carries the walks along any single-valued relation between witnesses,
relating cells by tag, value and witness (`WitRel.TSim`). A re-reading (`RR`) also keeps each
`imm` cell's lifetimes (`RC.imm`'s `hs`), and `○` computes a composite's lifetimes from its
operands' (`CellUT.CompR.lsOfI_eq`), so the walks carried along `RR` keep them too
(`agW_simL`). The proofs are `Tree/CarrierSim.lean`'s, with `LSim` for `TSim`.
-/

noncomputable section

namespace BoCa.Fig16.Tree.Wp
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree

variable {Θ : LocTy} {K K' : WCactus}

/-- Two lifetime readings merged: the union where both are `imm`. -/
def lsMerge : Option TSet → Option TSet → Option TSet
  | some s, some t => some (s ∪ t)
  | some s, none => some s
  | none, o => o

/-- The lifetimes of `ψ₁ ● ψ₂` are its operands' merged. -/
theorem compS_lsOfI_eq {ψ₁ ψ₂ ψ : TCell K} (h : CellUT.CompS ψ₁ ψ₂ ψ) :
    ψ.lsOfI = lsMerge ψ₁.lsOfI ψ₂.lsOfI := by
  obtain ⟨s₁, s₂, v, ρ, h₁, h₂, h₃, rfl, rfl, rfl⟩ := h
  rfl

/-- **The lifetimes of `ψ₁ ○ ψ₂`** are its operands' merged. -/
theorem compR_lsOfI_eq {ψ₁ ψ₂ ψ : TCell K} (h : CellUT.CompR ψ₁ ψ₂ ψ) :
    ψ.lsOfI = lsMerge ψ₁.lsOfI ψ₂.lsOfI := by
  cases h with
  | same =>
      rcases ψ₁ with _ | i | _
      · rfl
      · simp [CellUT.lsOfI, lsMerge, TSet.ext_iff]
      · rfl
  | strict k => exact compS_lsOfI_eq (CellUT.compS_spec _ _ k)
  | mutMut => rfl
  | mutOwn => rfl
  | ownMut => rfl
  | immOwn => rfl
  | ownImm => rfl
  | immMut => rfl
  | mutImm => rfl

/-- A cell and its re-reading: tag, value, witness re-read, and lifetimes kept. -/
def LSim (Θ : LocTy) (ψ' : TCell K') (ψ : TCell K) : Prop :=
  (ψ'.kind = ψ.kind ∧ ψ'.erase = ψ.erase ∧ RR Θ ψ.wit ψ'.wit) ∧ ψ'.lsOfI = ψ.lsOfI

/-- Resources related cell by cell by `LSim`. -/
def LRSim (Θ : LocTy) (ρ' : TRes K') (ρ : TRes K) : Prop :=
  ∀ l, Option.Rel (LSim Θ) (ρ'.get l) (ρ.get l)

theorem rc_lsOfI {l : BoCa.Loc} {ψ : TCell K} {ψ' : TCell K'} (h : RC Θ l ψ ψ') :
    ψ'.lsOfI = ψ.lsOfI := by
  cases h with
  | own => rfl
  | imm _ _ _ hs => simp [CellUT.lsOfI, hs]
  | «mut» => rfl

theorem rc_lsim {l : BoCa.Loc} {ψ : TCell K} {ψ' : TCell K'} (h : RC Θ l ψ ψ') : LSim Θ ψ' ψ :=
  ⟨⟨h.kind, h.erase, h.wit⟩, rc_lsOfI h⟩

theorem lrsim_of_RR {ρ : TRes K} {ρ' : TRes K'} (h : RR Θ ρ ρ') : LRSim Θ ρ' ρ := by
  intro l
  cases e : ρ.get l with
  | none => rw [(h.1 l).mp e]; exact .none
  | some ψ =>
      obtain ⟨ψ', e', hr⟩ := h.get_some e
      rw [e']; exact .some (rc_lsim hr)

theorem lsim_compatR {ψ₁ ψ₂ : TCell K} {ψ₁' ψ₂' : TCell K'}
    (h₁ : LSim Θ ψ₁' ψ₁) (h₂ : LSim Θ ψ₂' ψ₂) (h : CellUT.CompatR ψ₁ ψ₂) :
    CellUT.CompatR ψ₁' ψ₂' := by
  obtain ⟨hv, hw⟩ := CellUT.compatR_iff.mp h
  refine CellUT.compatR_iff.mpr ⟨h₁.1.2.1.trans (hv.trans h₂.1.2.1.symm), fun k₁ k₂ => ?_⟩
  exact RR.func h₁.1.2.2 (hw (h₁.1.1 ▸ k₁) (h₂.1.1 ▸ k₂) ▸ h₂.1.2.2)

theorem lsim_compR {ψ₁ ψ₂ ψ : TCell K} {ψ₁' ψ₂' : TCell K'}
    (h₁ : LSim Θ ψ₁' ψ₁) (h₂ : LSim Θ ψ₂' ψ₂) (h : CellUT.CompR ψ₁ ψ₂ ψ) :
    ∃ ψ', CellUT.CompR ψ₁' ψ₂' ψ' ∧ LSim Θ ψ' ψ := by
  obtain ⟨ψ', hr⟩ := lsim_compatR h₁ h₂ ⟨ψ, h⟩
  refine ⟨ψ', hr, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [CellUT.CompR.kind_eq hr, CellUT.CompR.kind_eq h, h₁.1.1, h₂.1.1]
  · rw [(CellUT.CompR.erase hr).2, (CellUT.CompR.erase h).2, h₁.1.2.1]
  · rw [CellUT.CompR.wit_eq hr, CellUT.CompR.wit_eq h, h₁.1.1]
    split
    · exact h₂.1.2.2
    · exact h₁.1.2.2
  · rw [compR_lsOfI_eq hr, compR_lsOfI_eq h, h₁.2, h₂.2]

theorem wrsim_emptyL :
    LRSim Θ (PMap.empty : TRes K') (PMap.empty : TRes K) :=
  fun _ => Option.Rel.none

theorem wrsim_restrictL {ρ' : TRes K'} {ρ : TRes K}
    (h : LRSim Θ ρ' ρ) (k : Kind) :
    LRSim Θ (G.restrict CellUT.kind ρ' k) (G.restrict CellUT.kind ρ k) := by
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
        rw [hψ.1.1]
        split
        · exact Option.Rel.some hψ
        · exact Option.Rel.none

theorem wrsim_sitesL {ρ' : TRes K'} {ρ : TRes K}
    (h : LRSim Θ ρ' ρ) {k : Kind} {d : List BoCa.Loc} (hd : G.Sites CellUT.kind ρ k d) :
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
        · rintro ⟨ψ, e, hk⟩; cases e; exact ⟨a, rfl, hψ.1.1.trans hk⟩
        · rintro ⟨ψ, e, hk⟩; cases e; exact ⟨b, rfl, hψ.1.1.symm.trans hk⟩

/-- A composite carried along related operands. -/
theorem wrsim_compL {R : TCell K → TCell K → Prop}
    {C : TCell K → TCell K → TCell K → Prop}
    {R' : TCell K' → TCell K' → Prop}
    {C' : TCell K' → TCell K' → TCell K' → Prop}
    (hR' : ∀ ψ₁ ψ₂ ψ, C' ψ₁ ψ₂ ψ → R' ψ₁ ψ₂)
    (hC : ∀ {ψ₁ ψ₂ ψ ψ₁' ψ₂'}, LSim Θ ψ₁' ψ₁ → LSim Θ ψ₂' ψ₂ → C ψ₁ ψ₂ ψ →
      ∃ ψ', C' ψ₁' ψ₂' ψ' ∧ LSim Θ ψ' ψ)
    {ρ₁ ρ₂ ρ : TRes K} {ρ₁' ρ₂' : TRes K'}
    (h₁ : LRSim Θ ρ₁' ρ₁) (h₂ : LRSim Θ ρ₂' ρ₂) (h : G.Comp R C ρ₁ ρ₂ ρ) :
    ∃ ρ', G.Comp R' C' ρ₁' ρ₂' ρ' ∧ LRSim Θ ρ' ρ := by
  have key : ∀ l, ∃ o, G.OptComp C' (ρ₁'.get l) (ρ₂'.get l) o ∧
      Option.Rel (LSim Θ) o (ρ.get l) := by
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
  obtain ⟨f, hf⟩ : ∃ f : BoCa.Loc → Option (TCell K'), ∀ l,
      G.OptComp C' (ρ₁'.get l) (ρ₂'.get l) (f l) ∧ Option.Rel (LSim Θ) (f l) (ρ.get l) :=
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

theorem wrsim_bigCompL {R : TCell K → TCell K → Prop}
    {C : TCell K → TCell K → TCell K → Prop}
    {R' : TCell K' → TCell K' → Prop}
    {C' : TCell K' → TCell K' → TCell K' → Prop}
    (hR' : ∀ ψ₁ ψ₂ ψ, C' ψ₁ ψ₂ ψ → R' ψ₁ ψ₂)
    (hC : ∀ {ψ₁ ψ₂ ψ ψ₁' ψ₂'}, LSim Θ ψ₁' ψ₁ → LSim Θ ψ₂' ψ₂ → C ψ₁ ψ₂ ψ →
      ∃ ψ', C' ψ₁' ψ₂' ψ' ∧ LSim Θ ψ' ψ)
    {es : List (TRes K)} {b : TRes K} (h : G.BigComp R C es b) :
    ∀ {es' : List (TRes K')}, List.Forall₂ (LRSim Θ) es' es →
      ∃ b', G.BigComp R' C' es' b' ∧ LRSim Θ b' b := by
  induction h with
  | nil =>
      intro es' hes
      cases hes
      exact ⟨_, G.BigComp.nil, wrsim_emptyL⟩
  | cons hrest hcomp ih =>
      intro es' hes
      cases hes with
      | cons hσ hrest' =>
          obtain ⟨τ', hτ', sτ⟩ := ih hrest'
          obtain ⟨ρ', hρ', sρ⟩ := wrsim_compL hR' hC hσ sτ hcomp
          exact ⟨ρ', G.BigComp.cons hτ' hρ', sρ⟩

/-- **The exclusive walk carries over.** -/
theorem exW_simL {R : TCell K → TCell K → Prop}
    {C : TCell K → TCell K → TCell K → Prop}
    {R' : TCell K' → TCell K' → Prop}
    {C' : TCell K' → TCell K' → TCell K' → Prop}
    (hR' : ∀ ψ₁ ψ₂ ψ, C' ψ₁ ψ₂ ψ → R' ψ₁ ψ₂)
    (hC : ∀ {ψ₁ ψ₂ ψ ψ₁' ψ₂'}, LSim Θ ψ₁' ψ₁ → LSim Θ ψ₂' ψ₂ → C ψ₁ ψ₂ ψ →
      ∃ ψ', C' ψ₁' ψ₂' ψ' ∧ LSim Θ ψ' ψ)
    {ρ σ : TRes K} (h : G.ExW CellUT.kind CellUT.wit R C ρ σ) :
    ∀ ρ' : TRes K', LRSim Θ ρ' ρ → ∃ σ', G.ExW CellUT.kind CellUT.wit R' C' ρ' σ' ∧ LRSim Θ σ' σ := by
  refine G.ExW.rec (motive_1 := fun ρ σ _ => ∀ ρ' : TRes K', LRSim Θ ρ' ρ →
      ∃ σ', G.ExW CellUT.kind CellUT.wit R' C' ρ' σ' ∧ LRSim Θ σ' σ)
    (motive_2 := fun ρ w _ => ∀ ρ' : TRes K', LRSim Θ ρ' ρ →
      ∃ w', G.ExWits CellUT.kind CellUT.wit R' C' ρ' w' ∧ w'.map Prod.fst = w.map Prod.fst ∧
        List.Forall₂ (LRSim Θ) (w'.map Prod.snd) (w.map Prod.snd))
    ?mk ?nil ?cons h
  case mk =>
    intro ρ₀ σ₀ nm b w hs _ hb hnm hσ ih ρ' hρ
    obtain ⟨w', hw', hfst, hsnd⟩ := ih ρ' hρ
    obtain ⟨b', hb', sb⟩ := wrsim_bigCompL hR' hC hb hsnd
    obtain ⟨nm', hnm', snm⟩ := wrsim_compL hR' hC (wrsim_restrictL hρ _)
      (wrsim_restrictL hρ _) hnm
    obtain ⟨σ', hσ', sσ⟩ := wrsim_compL hR' hC snm sb hσ
    exact ⟨σ', G.ExW.mk (hfst ▸ wrsim_sitesL hρ hs) hw' hb' hnm' hσ', sσ⟩
  case nil =>
    intro ρ₀ ρ' _
    exact ⟨[], G.ExWits.nil, rfl, List.Forall₂.nil⟩
  case cons =>
    intro ρ₀ e l w ψ hψ hk _ _ ihe ihw ρ' hρ
    obtain ⟨w', hw', hfst, hsnd⟩ := ihw ρ' hρ
    have hl := hρ l
    rw [hψ] at hl
    obtain ⟨ψ', eψ', sψ⟩ : ∃ ψ', ρ'.get l = some ψ' ∧ LSim Θ ψ' ψ := by
      revert hl
      cases ρ'.get l with
      | none => intro hl; cases hl
      | some ψ' => intro hl; cases hl with | some h => exact ⟨ψ', rfl, h⟩
    obtain ⟨e', he', se⟩ := ihe ψ'.wit (lrsim_of_RR sψ.1.2.2)
    exact ⟨(l, e') :: w', G.ExWits.cons ψ' eψ' (sψ.1.1.trans hk) he' hw',
      by simp [hfst], List.Forall₂.cons se hsnd⟩

/-- **The aliasable walk carries over.** -/
theorem agW_simL {ρ σ : TRes K} (h : AgWT ρ σ) :
    ∀ ρ' : TRes K', LRSim Θ ρ' ρ → ∃ σ', AgWT ρ' σ' ∧ LRSim Θ σ' σ := by
  have hR' : ∀ ψ₁ ψ₂ ψ, CellUT.CompR (K := K') (Loc := BoCa.Loc) (Val := BoCa.Val) ψ₁ ψ₂ ψ →
      CellUT.CompatR ψ₁ ψ₂ := fun _ _ ψ hc => ⟨ψ, hc⟩
  have hC : ∀ {ψ₁ ψ₂ ψ : TCell K} {ψ₁' ψ₂' : TCell K'},
      LSim Θ ψ₁' ψ₁ → LSim Θ ψ₂' ψ₂ → CellUT.CompR ψ₁ ψ₂ ψ →
      ∃ ψ', CellUT.CompR ψ₁' ψ₂' ψ' ∧ LSim Θ ψ' ψ := fun a b c => lsim_compR a b c
  refine G.AgW.rec (motive_1 := fun ρ σ _ => ∀ ρ' : TRes K', LRSim Θ ρ' ρ →
      ∃ σ', AgWT ρ' σ' ∧ LRSim Θ σ' σ)
    (motive_2 := fun ρ w _ => ∀ ρ' : TRes K', LRSim Θ ρ' ρ →
      ∃ w', G.AgWitsM CellUT.kind CellUT.wit CellUT.CompatR CellUT.CompR ρ' w' ∧
        w'.map Prod.fst = w.map Prod.fst ∧
        List.Forall₂ (LRSim Θ) (w'.map Prod.snd) (w.map Prod.snd))
    (motive_3 := fun ρ w _ => ∀ ρ' : TRes K', LRSim Θ ρ' ρ →
      ∃ w', G.AgWitsI CellUT.kind CellUT.wit CellUT.CompatR CellUT.CompR ρ' w' ∧
        w'.map Prod.fst = w.map Prod.fst ∧
        List.Forall₂ (LRSim Θ) (w'.map Prod.snd) (w.map Prod.snd))
    ?mk ?nilM ?consM ?nilI ?consI h
  case mk =>
    intro ρ₀ σ₀ a bm bi wm wi hsm hsi _ _ hbm hbi ha hσ ihm ihi ρ' hρ
    obtain ⟨wm', hwm', fm, sm⟩ := ihm ρ' hρ
    obtain ⟨wi', hwi', fi, si⟩ := ihi ρ' hρ
    obtain ⟨bm', hbm', sbm⟩ := wrsim_bigCompL hR' hC hbm sm
    obtain ⟨bi', hbi', sbi⟩ := wrsim_bigCompL hR' hC hbi si
    obtain ⟨a', ha', sa⟩ := wrsim_compL hR' hC (wrsim_restrictL hρ _) sbm ha
    obtain ⟨σ', hσ', sσ⟩ := wrsim_compL hR' hC sa sbi hσ
    exact ⟨σ', G.AgW.mk (fm ▸ wrsim_sitesL hρ hsm) (fi ▸ wrsim_sitesL hρ hsi) hwm' hwi'
      hbm' hbi' ha' hσ', sσ⟩
  case nilM => intro ρ₀ ρ' _; exact ⟨[], G.AgWitsM.nil, rfl, List.Forall₂.nil⟩
  case consM =>
    intro ρ₀ e l w ψ hψ hk _ _ ihe ihw ρ' hρ
    obtain ⟨w', hw', hfst, hsnd⟩ := ihw ρ' hρ
    have hl := hρ l
    rw [hψ] at hl
    obtain ⟨ψ', eψ', sψ⟩ : ∃ ψ', ρ'.get l = some ψ' ∧ LSim Θ ψ' ψ := by
      revert hl
      cases ρ'.get l with
      | none => intro hl; cases hl
      | some ψ' => intro hl; cases hl with | some h => exact ⟨ψ', rfl, h⟩
    obtain ⟨e', he', se⟩ := ihe ψ'.wit (lrsim_of_RR sψ.1.2.2)
    exact ⟨(l, e') :: w', G.AgWitsM.cons ψ' eψ' (sψ.1.1.trans hk) he' hw',
      by simp [hfst], List.Forall₂.cons se hsnd⟩
  case nilI => intro ρ₀ ρ' _; exact ⟨[], G.AgWitsI.nil, rfl, List.Forall₂.nil⟩
  case consI =>
    intro ρ₀ p l w ψ hψ hk e a hex _ hp _ iha ihw ρ' hρ
    obtain ⟨w', hw', hfst, hsnd⟩ := ihw ρ' hρ
    have hl := hρ l
    rw [hψ] at hl
    obtain ⟨ψ', eψ', sψ⟩ : ∃ ψ', ρ'.get l = some ψ' ∧ LSim Θ ψ' ψ := by
      revert hl
      cases ρ'.get l with
      | none => intro hl; cases hl
      | some ψ' => intro hl; cases hl with | some h => exact ⟨ψ', rfl, h⟩
    have sw : LRSim Θ ψ'.wit ψ.wit := lrsim_of_RR sψ.1.2.2
    obtain ⟨e', he', se⟩ := exW_simL hR' hC hex ψ'.wit sw
    obtain ⟨a', ha', sa⟩ := iha ψ'.wit sw
    obtain ⟨p', hp', sp⟩ := wrsim_compL hR' hC se sa hp
    exact ⟨(l, p') :: w', G.AgWitsI.cons ψ' eψ' (sψ.1.1.trans hk) e' a' he' ha' hp' hw',
      by simp [hfst], List.Forall₂.cons sp hsnd⟩

end BoCa.Fig16.Tree.Wp

end
