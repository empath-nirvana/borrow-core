import Support.Model.Tree.World.World

/-!
# The flattening along re-reading, lifetime sets kept

`ResUT.Flat.rr` (`TreeWp/World.lean`) carries `⦇·⦈` along `RR`, relating the two flattenings
cell by cell through `rrRel`'s `TSim`: tag, value and witness re-read. `↭`'s `imm` clause
(row 5.27) also reads an `imm` cell's lifetime set, and its `mut` clause a `mut` cell's `β̄`, so
reading `↭` across a re-reading asks for those too. A re-read `imm` cell keeps its lifetime set and
a re-read `mut` cell's `β̄` is read as `min_{K′} β̄` (`RC`); `○` and `●` compute the lifetime set of
a composite from its operands' (`CellUT.CompR.lsOf_eq`), and `min_{K′}` commutes with that
computation (`rlsOf_lsc`). So the walks carry the relation `LsSim`: `TSim` and the lifetime set
re-read (`ResUT.Flat.rrLs`).

A `mut` cell's invariant is not carried: the re-reading reads it off the location typing at the
new tree, and a `○`-composite's `P̂ ∧ Q̂` is read on `Res_{min(β̄₁ ∪ β̄₂)}`, which is not `Res_β̄₁ ∩
Res_β̄₂`.

The walk lemmas are `Tree/CarrierSim.lean`'s, with `LsSim` for `TSim`.
-/

noncomputable section

namespace BoCa.Fig16.Tree
open BoCa.Fig16

variable {K K' : WCactus}

/-! ### Lifetime sets of composites -/

/-- The lifetime set of a re-read cell of tag `k` and lifetime set `o`. -/
def rlsOf (K' : WCactus) : Kind → Option TSet → Option TSet
  | .mut, o => o.map K'.minS
  | _, o => o

/-- The lifetime set `○` gives a composite of two cells of tags `k₁`, `k₂` and lifetime sets
`o₁`, `o₂`. -/
def lsc (K : WCactus) : Kind → Option TSet → Kind → Option TSet → Option TSet
  | .own, _, _, o₂ => o₂
  | .imm, o₁, .own, _ => o₁
  | .mut, o₁, .own, _ => o₁
  | .imm, o₁, .imm, o₂ => Option.map₂ (fun s t : TSet => s ∪ t) o₁ o₂
  | .mut, o₁, .mut, o₂ => Option.map₂ (fun s t => K.minS (s ∪ t)) o₁ o₂
  | .imm, o₁, .mut, _ => o₁
  | .mut, _, .imm, o₂ => o₂

theorem CellUT.CompS.lsOf_eq {ψ₁ ψ₂ ψ : TCell K} (h : CellUT.CompS ψ₁ ψ₂ ψ) :
    ψ.lsOf = Option.map₂ (fun s t : TSet => s ∪ t) ψ₁.lsOf ψ₂.lsOf := by
  obtain ⟨s₁, s₂, v, ρ, h₁, h₂, h₃, rfl, rfl, rfl⟩ := h
  rfl

/-- **The lifetime set of `ψ₁ ○ ψ₂`.** -/
theorem CellUT.CompR.lsOf_eq {ψ₁ ψ₂ ψ : TCell K} (h : CellUT.CompR ψ₁ ψ₂ ψ) :
    ψ.lsOf = lsc K ψ₁.kind ψ₁.lsOf ψ₂.kind ψ₂.lsOf := by
  cases h with
  | same =>
      cases ψ₁ with
      | own v => rfl
      | imm i => show some i.ls = some (i.ls ∪ i.ls); rw [TSet.union_self]
      | «mut» m => show some m.ls = some (K.minS (m.ls ∪ m.ls)); rw [K.minS_self m.anti]
  | strict k =>
      rw [CellUT.CompS.lsOf_eq (CellUT.compS_spec _ _ k), (CellUT.CompatS.kinds k).1,
        (CellUT.CompatS.kinds k).2]
      rfl
  | mutMut => rfl
  | mutOwn => rfl
  | ownMut => rfl
  | immOwn => rfl
  | ownImm => rfl
  | immMut => rfl
  | mutImm => rfl

/-- `min_{K′}(min_K(s ∪ t)) = min_{K′}(min_{K′} s ∪ min_{K′} t)`. -/
theorem minS_reread (hE : K.Ext K') (s t : TSet) :
    K'.minS (K.minS (s ∪ t)) = K'.minS (K'.minS s ∪ K'.minS t) := by
  rw [WCactus.minS_minS hE, K'.minS_union_minS_left, TSet.union_comm s (K'.minS t),
    K'.minS_union_minS_left, TSet.union_comm]

/-- **Re-reading commutes with the composite's lifetime set.** -/
theorem rlsOf_lsc (hE : K.Ext K') (k₁ k₂ : Kind) (o₁ o₂ : Option TSet) :
    rlsOf K' (kcomb k₁ k₂) (lsc K k₁ o₁ k₂ o₂) =
      lsc K' k₁ (rlsOf K' k₁ o₁) k₂ (rlsOf K' k₂ o₂) := by
  cases k₁ <;> cases k₂ <;> cases o₁ <;> cases o₂ <;>
    simp [rlsOf, lsc, kcomb, Option.map₂, minS_reread hE]

/-! ### The cell relation -/

variable (Θ : LocTy)

/-- **A cell and its re-reading, up to the `mut` invariant**: tag, value and witness re-read, as
`rrRel`'s `TSim`, and the lifetime set re-read. -/
def LsSim (ψ' : TCell K') (ψ : TCell K) : Prop :=
  ψ'.kind = ψ.kind ∧ ψ'.erase = ψ.erase ∧ RR Θ ψ.wit ψ'.wit ∧
    ψ'.lsOf = rlsOf K' ψ.kind ψ.lsOf

/-- Resources related cell by cell. -/
def LsRSim (ρ' : TRes K') (ρ : TRes K) : Prop :=
  ∀ l, Option.Rel (LsSim Θ) (ρ'.get l) (ρ.get l)

variable {Θ}

theorem RC.lsSim {l : BoCa.Loc} {ψ : TCell K} {ψ' : TCell K'} (h : RC Θ l ψ ψ') :
    LsSim Θ ψ' ψ := by
  refine ⟨h.kind, h.erase, h.wit, ?_⟩
  cases h with
  | own => rfl
  | imm _ _ _ hs => exact congrArg some hs
  | «mut» _ _ _ _ _ hs => exact congrArg some hs

theorem RR.lsRSim {ρ : TRes K} {ρ' : TRes K'} (h : RR Θ ρ ρ') : LsRSim Θ ρ' ρ := by
  intro l
  cases e : ρ.get l with
  | none => rw [(h.1 l).mp e]; exact Option.Rel.none
  | some ψ =>
      obtain ⟨ψ', e', hr⟩ := h.get_some e
      rw [e']
      exact Option.Rel.some hr.lsSim

theorem lsSim_compatS {ψ₁ ψ₂ : TCell K} {ψ₁' ψ₂' : TCell K'} (h₁ : LsSim Θ ψ₁' ψ₁)
    (h₂ : LsSim Θ ψ₂' ψ₂) (h : CellUT.CompatS ψ₁ ψ₂) : CellUT.CompatS ψ₁' ψ₂' := by
  obtain ⟨k₁, k₂, hv, hw⟩ := CellUT.compatS_iff.mp h
  exact CellUT.compatS_iff.mpr ⟨h₁.1.trans k₁, h₂.1.trans k₂,
    h₁.2.1.trans (hv.trans h₂.2.1.symm), RR.func h₁.2.2.1 (hw ▸ h₂.2.2.1)⟩

theorem lsSim_compatR {ψ₁ ψ₂ : TCell K} {ψ₁' ψ₂' : TCell K'} (h₁ : LsSim Θ ψ₁' ψ₁)
    (h₂ : LsSim Θ ψ₂' ψ₂) (h : CellUT.CompatR ψ₁ ψ₂) : CellUT.CompatR ψ₁' ψ₂' := by
  obtain ⟨hv, hw⟩ := CellUT.compatR_iff.mp h
  refine CellUT.compatR_iff.mpr ⟨h₁.2.1.trans (hv.trans h₂.2.1.symm), fun k₁ k₂ => ?_⟩
  exact RR.func h₁.2.2.1 (hw (h₁.1 ▸ k₁) (h₂.1 ▸ k₂) ▸ h₂.2.2.1)

theorem lsSim_compS {ψ₁ ψ₂ ψ : TCell K} {ψ₁' ψ₂' : TCell K'} (h₁ : LsSim Θ ψ₁' ψ₁)
    (h₂ : LsSim Θ ψ₂' ψ₂) (h : CellUT.CompS ψ₁ ψ₂ ψ) :
    ∃ ψ', CellUT.CompS ψ₁' ψ₂' ψ' ∧ LsSim Θ ψ' ψ := by
  have k := lsSim_compatS h₁ h₂ h.compat
  have hs := CellUT.compS_spec _ _ k
  have kψ₁ : ψ₁.kind = Kind.imm := (CellUT.CompatS.kinds h.compat).1
  have kψ₂ : ψ₂.kind = Kind.imm := (CellUT.CompatS.kinds h.compat).2
  refine ⟨_, hs, ?_, ?_, ?_, ?_⟩
  · rw [CellUT.CompS.kind hs, CellUT.CompS.kind h]
  · rw [(CellUT.CompS.erase hs).1, (CellUT.CompS.erase h).1, h₁.2.1]
  · rw [(CellUT.CompS.wit hs).1, (CellUT.CompS.wit h).1]; exact h₁.2.2.1
  · rw [CellUT.CompS.lsOf_eq hs, CellUT.CompS.lsOf_eq h, CellUT.CompS.kind h, h₁.2.2.2,
      h₂.2.2.2, kψ₁, kψ₂]
    rfl

theorem lsSim_compR (hE : K.Ext K') {ψ₁ ψ₂ ψ : TCell K} {ψ₁' ψ₂' : TCell K'}
    (h₁ : LsSim Θ ψ₁' ψ₁) (h₂ : LsSim Θ ψ₂' ψ₂) (h : CellUT.CompR ψ₁ ψ₂ ψ) :
    ∃ ψ', CellUT.CompR ψ₁' ψ₂' ψ' ∧ LsSim Θ ψ' ψ := by
  obtain ⟨ψ', hr⟩ := lsSim_compatR h₁ h₂ ⟨ψ, h⟩
  refine ⟨ψ', hr, ?_, ?_, ?_, ?_⟩
  · rw [CellUT.CompR.kind_eq hr, CellUT.CompR.kind_eq h, h₁.1, h₂.1]
  · rw [(CellUT.CompR.erase hr).2, (CellUT.CompR.erase h).2, h₁.2.1]
  · rw [CellUT.CompR.wit_eq hr, CellUT.CompR.wit_eq h, h₁.1]
    split
    · exact h₂.2.2.1
    · exact h₁.2.2.1
  · rw [CellUT.CompR.lsOf_eq hr, CellUT.CompR.lsOf_eq h, CellUT.CompR.kind_eq h, h₁.1, h₂.1,
      h₁.2.2.2, h₂.2.2.2, rlsOf_lsc hE]

/-! ### The walks -/

theorem lsRSim_empty : LsRSim Θ (PMap.empty : TRes K') (PMap.empty : TRes K) :=
  fun _ => Option.Rel.none

theorem lsRSim_restrict {ρ' : TRes K'} {ρ : TRes K} (h : LsRSim Θ ρ' ρ) (k : Kind) :
    LsRSim Θ (G.restrict CellUT.kind ρ' k) (G.restrict CellUT.kind ρ k) := by
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

theorem lsRSim_sites {ρ' : TRes K'} {ρ : TRes K} (h : LsRSim Θ ρ' ρ) {k : Kind}
    {d : List BoCa.Loc} (hd : G.Sites CellUT.kind ρ k d) : G.Sites CellUT.kind ρ' k d := by
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
theorem lsRSim_comp {R : TCell K → TCell K → Prop} {C : TCell K → TCell K → TCell K → Prop}
    {R' : TCell K' → TCell K' → Prop} {C' : TCell K' → TCell K' → TCell K' → Prop}
    (hR' : ∀ ψ₁ ψ₂ ψ, C' ψ₁ ψ₂ ψ → R' ψ₁ ψ₂)
    (hC : ∀ {ψ₁ ψ₂ ψ ψ₁' ψ₂'}, LsSim Θ ψ₁' ψ₁ → LsSim Θ ψ₂' ψ₂ → C ψ₁ ψ₂ ψ →
      ∃ ψ', C' ψ₁' ψ₂' ψ' ∧ LsSim Θ ψ' ψ)
    {ρ₁ ρ₂ ρ : TRes K} {ρ₁' ρ₂' : TRes K'}
    (h₁ : LsRSim Θ ρ₁' ρ₁) (h₂ : LsRSim Θ ρ₂' ρ₂) (h : G.Comp R C ρ₁ ρ₂ ρ) :
    ∃ ρ', G.Comp R' C' ρ₁' ρ₂' ρ' ∧ LsRSim Θ ρ' ρ := by
  have key : ∀ l, ∃ o, G.OptComp C' (ρ₁'.get l) (ρ₂'.get l) o ∧
      Option.Rel (LsSim Θ) o (ρ.get l) := by
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
      G.OptComp C' (ρ₁'.get l) (ρ₂'.get l) (f l) ∧ Option.Rel (LsSim Θ) (f l) (ρ.get l) :=
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

theorem lsRSim_bigComp {R : TCell K → TCell K → Prop} {C : TCell K → TCell K → TCell K → Prop}
    {R' : TCell K' → TCell K' → Prop} {C' : TCell K' → TCell K' → TCell K' → Prop}
    (hR' : ∀ ψ₁ ψ₂ ψ, C' ψ₁ ψ₂ ψ → R' ψ₁ ψ₂)
    (hC : ∀ {ψ₁ ψ₂ ψ ψ₁' ψ₂'}, LsSim Θ ψ₁' ψ₁ → LsSim Θ ψ₂' ψ₂ → C ψ₁ ψ₂ ψ →
      ∃ ψ', C' ψ₁' ψ₂' ψ' ∧ LsSim Θ ψ' ψ)
    {es : List (TRes K)} {b : TRes K} (h : G.BigComp R C es b) :
    ∀ {es' : List (TRes K')}, List.Forall₂ (LsRSim Θ) es' es →
      ∃ b', G.BigComp R' C' es' b' ∧ LsRSim Θ b' b := by
  induction h with
  | nil =>
      intro es' hes
      cases hes
      exact ⟨_, G.BigComp.nil, lsRSim_empty⟩
  | cons hrest hcomp ih =>
      intro es' hes
      cases hes with
      | cons hσ hrest' =>
          obtain ⟨τ', hτ', sτ⟩ := ih hrest'
          obtain ⟨ρ', hρ', sρ⟩ := lsRSim_comp hR' hC hσ sτ hcomp
          exact ⟨ρ', G.BigComp.cons hτ' hρ', sρ⟩

/-- **The exclusive walk carries over.** -/
theorem ExW.lsSim {R : TCell K → TCell K → Prop} {C : TCell K → TCell K → TCell K → Prop}
    {R' : TCell K' → TCell K' → Prop} {C' : TCell K' → TCell K' → TCell K' → Prop}
    (hR' : ∀ ψ₁ ψ₂ ψ, C' ψ₁ ψ₂ ψ → R' ψ₁ ψ₂)
    (hC : ∀ {ψ₁ ψ₂ ψ ψ₁' ψ₂'}, LsSim Θ ψ₁' ψ₁ → LsSim Θ ψ₂' ψ₂ → C ψ₁ ψ₂ ψ →
      ∃ ψ', C' ψ₁' ψ₂' ψ' ∧ LsSim Θ ψ' ψ)
    {ρ σ : TRes K} (h : G.ExW CellUT.kind CellUT.wit R C ρ σ) :
    ∀ ρ' : TRes K', LsRSim Θ ρ' ρ → ∃ σ', G.ExW CellUT.kind CellUT.wit R' C' ρ' σ' ∧ LsRSim Θ σ' σ := by
  refine G.ExW.rec (motive_1 := fun ρ σ _ => ∀ ρ' : TRes K', LsRSim Θ ρ' ρ →
      ∃ σ', G.ExW CellUT.kind CellUT.wit R' C' ρ' σ' ∧ LsRSim Θ σ' σ)
    (motive_2 := fun ρ w _ => ∀ ρ' : TRes K', LsRSim Θ ρ' ρ →
      ∃ w', G.ExWits CellUT.kind CellUT.wit R' C' ρ' w' ∧ w'.map Prod.fst = w.map Prod.fst ∧
        List.Forall₂ (LsRSim Θ) (w'.map Prod.snd) (w.map Prod.snd))
    ?mk ?nil ?cons h
  case mk =>
    intro ρ₀ σ₀ nm b w hs _ hb hnm hσ ih ρ' hρ
    obtain ⟨w', hw', hfst, hsnd⟩ := ih ρ' hρ
    obtain ⟨b', hb', sb⟩ := lsRSim_bigComp hR' hC hb hsnd
    obtain ⟨nm', hnm', snm⟩ := lsRSim_comp hR' hC (lsRSim_restrict hρ _)
      (lsRSim_restrict hρ _) hnm
    obtain ⟨σ', hσ', sσ⟩ := lsRSim_comp hR' hC snm sb hσ
    exact ⟨σ', G.ExW.mk (hfst ▸ lsRSim_sites hρ hs) hw' hb' hnm' hσ', sσ⟩
  case nil =>
    intro ρ₀ ρ' _
    exact ⟨[], G.ExWits.nil, rfl, List.Forall₂.nil⟩
  case cons =>
    intro ρ₀ e l w ψ hψ hk _ _ ihe ihw ρ' hρ
    obtain ⟨w', hw', hfst, hsnd⟩ := ihw ρ' hρ
    have hl := hρ l
    rw [hψ] at hl
    obtain ⟨ψ', eψ', sψ⟩ : ∃ ψ', ρ'.get l = some ψ' ∧ LsSim Θ ψ' ψ := by
      revert hl
      cases ρ'.get l with
      | none => intro hl; cases hl
      | some ψ' => intro hl; cases hl with | some h => exact ⟨ψ', rfl, h⟩
    obtain ⟨e', he', se⟩ := ihe ψ'.wit sψ.2.2.1.lsRSim
    exact ⟨(l, e') :: w', G.ExWits.cons ψ' eψ' (sψ.1.trans hk) he' hw',
      by simp [hfst], List.Forall₂.cons se hsnd⟩

/-- **The aliasable walk carries over.** -/
theorem AgW.lsSim (hE : K.Ext K') {ρ σ : TRes K} (h : AgWT ρ σ) :
    ∀ ρ' : TRes K', LsRSim Θ ρ' ρ → ∃ σ', AgWT ρ' σ' ∧ LsRSim Θ σ' σ := by
  have hR' : ∀ ψ₁ ψ₂ ψ, CellUT.CompR (K := K') (Loc := BoCa.Loc) (Val := BoCa.Val) ψ₁ ψ₂ ψ →
      CellUT.CompatR ψ₁ ψ₂ := fun _ _ ψ hc => ⟨ψ, hc⟩
  have hC : ∀ {ψ₁ ψ₂ ψ : TCell K} {ψ₁' ψ₂' : TCell K'},
      LsSim Θ ψ₁' ψ₁ → LsSim Θ ψ₂' ψ₂ → CellUT.CompR ψ₁ ψ₂ ψ →
      ∃ ψ', CellUT.CompR ψ₁' ψ₂' ψ' ∧ LsSim Θ ψ' ψ := fun a b c => lsSim_compR hE a b c
  refine G.AgW.rec (motive_1 := fun ρ σ _ => ∀ ρ' : TRes K', LsRSim Θ ρ' ρ →
      ∃ σ', AgWT ρ' σ' ∧ LsRSim Θ σ' σ)
    (motive_2 := fun ρ w _ => ∀ ρ' : TRes K', LsRSim Θ ρ' ρ →
      ∃ w', G.AgWitsM CellUT.kind CellUT.wit CellUT.CompatR CellUT.CompR ρ' w' ∧
        w'.map Prod.fst = w.map Prod.fst ∧
        List.Forall₂ (LsRSim Θ) (w'.map Prod.snd) (w.map Prod.snd))
    (motive_3 := fun ρ w _ => ∀ ρ' : TRes K', LsRSim Θ ρ' ρ →
      ∃ w', G.AgWitsI CellUT.kind CellUT.wit CellUT.CompatR CellUT.CompR ρ' w' ∧
        w'.map Prod.fst = w.map Prod.fst ∧
        List.Forall₂ (LsRSim Θ) (w'.map Prod.snd) (w.map Prod.snd))
    ?mk ?nilM ?consM ?nilI ?consI h
  case mk =>
    intro ρ₀ σ₀ a bm bi wm wi hsm hsi _ _ hbm hbi ha hσ ihm ihi ρ' hρ
    obtain ⟨wm', hwm', fm, sm⟩ := ihm ρ' hρ
    obtain ⟨wi', hwi', fi, si⟩ := ihi ρ' hρ
    obtain ⟨bm', hbm', sbm⟩ := lsRSim_bigComp hR' hC hbm sm
    obtain ⟨bi', hbi', sbi⟩ := lsRSim_bigComp hR' hC hbi si
    obtain ⟨a', ha', sa⟩ := lsRSim_comp hR' hC (lsRSim_restrict hρ _) sbm ha
    obtain ⟨σ', hσ', sσ⟩ := lsRSim_comp hR' hC sa sbi hσ
    exact ⟨σ', G.AgW.mk (fm ▸ lsRSim_sites hρ hsm) (fi ▸ lsRSim_sites hρ hsi) hwm' hwi'
      hbm' hbi' ha' hσ', sσ⟩
  case nilM => intro ρ₀ ρ' _; exact ⟨[], G.AgWitsM.nil, rfl, List.Forall₂.nil⟩
  case consM =>
    intro ρ₀ e l w ψ hψ hk _ _ ihe ihw ρ' hρ
    obtain ⟨w', hw', hfst, hsnd⟩ := ihw ρ' hρ
    have hl := hρ l
    rw [hψ] at hl
    obtain ⟨ψ', eψ', sψ⟩ : ∃ ψ', ρ'.get l = some ψ' ∧ LsSim Θ ψ' ψ := by
      revert hl
      cases ρ'.get l with
      | none => intro hl; cases hl
      | some ψ' => intro hl; cases hl with | some h => exact ⟨ψ', rfl, h⟩
    obtain ⟨e', he', se⟩ := ihe ψ'.wit sψ.2.2.1.lsRSim
    exact ⟨(l, e') :: w', G.AgWitsM.cons ψ' eψ' (sψ.1.trans hk) he' hw',
      by simp [hfst], List.Forall₂.cons se hsnd⟩
  case nilI => intro ρ₀ ρ' _; exact ⟨[], G.AgWitsI.nil, rfl, List.Forall₂.nil⟩
  case consI =>
    intro ρ₀ p l w ψ hψ hk e a hex _ hp _ iha ihw ρ' hρ
    obtain ⟨w', hw', hfst, hsnd⟩ := ihw ρ' hρ
    have hl := hρ l
    rw [hψ] at hl
    obtain ⟨ψ', eψ', sψ⟩ : ∃ ψ', ρ'.get l = some ψ' ∧ LsSim Θ ψ' ψ := by
      revert hl
      cases ρ'.get l with
      | none => intro hl; cases hl
      | some ψ' => intro hl; cases hl with | some h => exact ⟨ψ', rfl, h⟩
    have sw : LsRSim Θ ψ'.wit ψ.wit := sψ.2.2.1.lsRSim
    obtain ⟨e', he', se⟩ := ExW.lsSim hR' hC hex ψ'.wit sw
    obtain ⟨a', ha', sa⟩ := iha ψ'.wit sw
    obtain ⟨p', hp', sp⟩ := lsRSim_comp hR' hC se sa hp
    exact ⟨(l, p') :: w', G.AgWitsI.cons ψ' eψ' (sψ.1.trans hk) e' a' he' ha' hp' hw',
      by simp [hfst], List.Forall₂.cons sp hsnd⟩

/-- **The flattening carried along `RR`, lifetime sets kept.** -/
theorem ResUT.Flat.rrLs (hE : K.Ext K') {ρ σ : TRes K} {ρ' : TRes K'} (h : ResUT.Flat ρ σ)
    (hr : RR Θ ρ ρ') : ∃ σ', ResUT.Flat ρ' σ' ∧ LsRSim Θ σ' σ := by
  obtain ⟨e, a, he, ha, hσ⟩ := h
  have hs := hr.lsRSim
  have hRS : ∀ ψ₁ ψ₂ ψ, CellUT.CompS (K := K') (Loc := BoCa.Loc) (Val := BoCa.Val) ψ₁ ψ₂ ψ →
      CellUT.CompatS ψ₁ ψ₂ := fun _ _ _ hc => hc.compat
  have hCS : ∀ {ψ₁ ψ₂ ψ : TCell K} {ψ₁' ψ₂' : TCell K'},
      LsSim Θ ψ₁' ψ₁ → LsSim Θ ψ₂' ψ₂ → CellUT.CompS ψ₁ ψ₂ ψ →
      ∃ ψ', CellUT.CompS ψ₁' ψ₂' ψ' ∧ LsSim Θ ψ' ψ := fun a b c => lsSim_compS a b c
  obtain ⟨e', he', se⟩ := ExW.lsSim hRS hCS he _ hs
  obtain ⟨a', ha', sa⟩ := AgW.lsSim hE ha _ hs
  obtain ⟨σ', hσ', sσ⟩ := lsRSim_comp hRS hCS se sa hσ
  exact ⟨σ', ⟨e', a', he', ha', hσ'⟩, sσ⟩

end BoCa.Fig16.Tree

end
