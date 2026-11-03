import Support.Model.Tree.CarrierChainOps
import Support.Model.Tree.Graft

/-!
# Grafting in the tree-stratified carrier

`[spec §62]`. A graft whose capture point is above the resume point adds nestings and removes none
(`ParentFn.graft_mono`): the cactus after it, `K'`, keeps every strict nesting of the cactus
before it, `K` (`WCactus.Ext`). Then every stratum of `K` sits inside the stratum of the same
index in `K'`, and the world carries over:

* `TU : CellUT K → CellUT K'` (`trU`), by well-founded recursion on `K`'s strata, keeps every
  lifetime name, value and witness. An `imm` cell keeps its lifetime set; a `mut` cell's
  antichain `β̄` becomes `min_{K'}(β̄)`, its members with no member strictly below them in `K'`
  (two siblings of `K` may be nested in `K'`). The stored predicate `P̂ ∈ SProp_β̄` is carried
  as row 5.57 carries `SProp_α ⊆ SProp_{α′}`: extension by falsity outside its stratum's image.
  No lifetime is renamed (`trU_lifetimes`).
* `✓` carries over: `✓ρ` in `K` gives `✓(TU ρ)` in `K'` (`ResUT.Valid.graft`). The walks are
  carried with their results related up to tag, value and witness (`TSim`), which is all the
  definedness of `▶◀` and `⋈` reads (`CellUT.compatS_iff`, `CellUT.compatR_iff`).

**A handler's lend and a task resumed inside it** (`Tree/Graft.lean`'s `beforeP`/`graftP`), at
the carrier (`Tree/CarrierGraftEx.lean`): `graftWorld_valid_before`, `graftWorld_valid_after` (the world before the graft, carried to the
tree after it), and `graftCell_admitted`: after the graft, a `mut` cell at `α = 1` whose
witness holds a borrow at `β = 2` is a cell of `Cell_{α}` and its world is valid, while before
the graft its witness is in no stratum of `α` (`graftCell_refused_before`). This is
`graftEx_printed_refuses`'s cell, admitted with no lifetime renamed.
-/

noncomputable section

namespace BoCa.Fig16.Tree
open BoCa.Fig16

/-- `K'` keeps every strict nesting of `K`. -/
def WCactus.Ext (K K' : WCactus) : Prop := ∀ {a b : Life}, K.lt a b → K'.lt a b

theorem WCactus.Ext.above {K K' : WCactus} (hE : K.Ext K') {S T : TSet} (h : K.Above S T) :
    K'.Above S T := fun x hx y hy => hE (h x hx y hy)

variable {Loc Val : Type} {K K' : WCactus}

/-! ### The transport -/

variable (Loc Val K K') in
/-- The motive: a map out of `Cell_S` in `K`, landing in `Cell_S` of `K'`. -/
def TrM (S : TSet) : Type :=
  {f : CellT Loc Val K S → CellUT Loc Val K' // ∀ ψ, (f ψ).InStratum S}

/-- One layer of the transport. -/
def trLayer (S : TSet) (rec : ∀ T, K.Above S T → TrM Loc Val K K' T) :
    CellTF Loc Val K S (fun T _ => CellT Loc Val K T) → CellUT Loc Val K'
  | .own v => .own v
  | .imm s hs v ρ =>
      CellUT.immOf s v (ρ.map (rec s hs).1) (ResUT.inStratum_map _ (rec s hs).2 ρ)
  | .mut s hs _ v ρ P hw =>
      CellUT.mutOf (K'.minS s) v (ρ.map (rec s hs).1)
        (ResUT.inStratum_map _ (rec s hs).2 ρ).minS
        (fun w r => ∃ r₀ : ResT Loc Val K s, r₀.map (rec s hs).1 = r.val ∧ P w r₀)
        ⟨ρ, rfl, hw⟩

theorem trLayer_inStratum (hE : K.Ext K') (S : TSet)
    (rec : ∀ T, K.Above S T → TrM Loc Val K K' T)
    (x : CellTF Loc Val K S (fun T _ => CellT Loc Val K T)) :
    (trLayer S rec x).InStratum S := by
  cases x with
  | own v => exact trivial
  | imm s hs v ρ => exact hE.above hs
  | «mut» s hs a v ρ P hw => exact (K'.above_minS_iff).mpr (hE.above hs)

def trF (hE : K.Ext K') (S : TSet) (rec : ∀ T, K.Above S T → TrM Loc Val K K' T) :
    TrM Loc Val K K' S :=
  ⟨fun ψ => trLayer S rec ψ.toF, fun ψ => trLayer_inStratum hE S rec ψ.toF⟩

/-- The transport on `Cell_S`. -/
def Tr (hE : K.Ext K') : ∀ S, TrM Loc Val K K' S := WellFounded.fix K.above_wf (trF hE)

theorem Tr_eq (hE : K.Ext K') (S : TSet) :
    Tr (Loc := Loc) (Val := Val) hE S = trF hE S (fun T _ => Tr hE T) :=
  WellFounded.fix_eq K.above_wf (trF hE) S

/-- **The transport on the union**: every name, value and witness kept. -/
def trU (hE : K.Ext K') : CellUT Loc Val K → CellUT Loc Val K'
  | .own v => .own v
  | .imm i => CellUT.immOf i.ls i.v (i.ρ.map (Tr hE i.ls).1)
      (ResUT.inStratum_map _ (Tr hE i.ls).2 i.ρ)
  | .mut m => CellUT.mutOf (K'.minS m.ls) m.v (m.ρ.map (Tr hE m.ls).1)
      (ResUT.inStratum_map _ (Tr hE m.ls).2 m.ρ).minS
      (fun w r => ∃ r₀ : ResT Loc Val K m.ls, r₀.map (Tr hE m.ls).1 = r.val ∧ m.P w r₀)
      ⟨m.ρ, rfl, m.hw⟩

theorem Tr_apply (hE : K.Ext K') {S : TSet} (ψ : CellT Loc Val K S) :
    (Tr hE S).1 ψ = trU hE ψ.toU := by
  rw [Tr_eq]
  show trLayer S (fun T _ => Tr hE T) ψ.toF = trU hE (CellTF.toU ψ.toF)
  generalize ψ.toF = x
  cases x <;> rfl

theorem Tr_map (hE : K.Ext K') {S : TSet} (ρ : ResT Loc Val K S) :
    ρ.map (Tr hE S).1 = ρ.toU.map (trU hE) := by
  unfold ResT.toU
  rw [PMap.map_map]
  exact PMap.map_congr ρ fun _ ψ _ => Tr_apply hE ψ

theorem trU_inStratum (hE : K.Ext K') {S : TSet} {ψ : CellUT Loc Val K}
    (h : ψ.InStratum S) : (trU hE ψ).InStratum S := by
  cases ψ with
  | own v => exact trivial
  | imm i => exact hE.above h
  | «mut» m => exact (K'.above_minS_iff).mpr (hE.above h)

theorem trU_kind (hE : K.Ext K') (ψ : CellUT Loc Val K) : (trU hE ψ).kind = ψ.kind := by
  cases ψ <;> rfl

theorem trU_erase (hE : K.Ext K') (ψ : CellUT Loc Val K) : (trU hE ψ).erase = ψ.erase := by
  cases ψ <;> rfl

theorem trU_wit (hE : K.Ext K') (ψ : CellUT Loc Val K) :
    (trU hE ψ).wit = ψ.wit.map (trU hE) := by
  cases ψ with
  | own v =>
      refine PMap.ext fun l => ?_
      show (PMap.empty : ResUT Loc Val K').get l =
        ((PMap.empty : ResUT Loc Val K).map (trU hE)).get l
      simp
  | imm i =>
      show (CellUT.immOf i.ls i.v (i.ρ.map (Tr hE i.ls).1) _).wit = _
      rw [CellUT.wit_immOf, Tr_map]; rfl
  | «mut» m =>
      show (CellUT.mutOf (K'.minS m.ls) m.v (m.ρ.map (Tr hE m.ls).1) _
        (fun w r => ∃ r₀ : ResT Loc Val K m.ls, r₀.map (Tr hE m.ls).1 = r.val ∧ m.P w r₀)
        ⟨m.ρ, rfl, m.hw⟩).wit = _
      rw [CellUT.wit_mutOf, Tr_map]; rfl

/-- **No lifetime is renamed.** An `imm` cell keeps its lifetime set; a `mut` cell keeps the
members of its set with nothing strictly below them in `K'`. -/
theorem trU_lifetimes (hE : K.Ext K') (ψ : CellUT Loc Val K) :
    (∀ i : ImmT Loc Val K, ψ = .imm i → (trU hE ψ).lsOf = some i.ls) ∧
    (∀ m : MutT Loc Val K, ψ = .mut m → (trU hE ψ).lsOf = some (K'.minS m.ls)) ∧
    (∀ v : Val, ψ = .own v → trU hE ψ = .own v) := by
  refine ⟨?_, ?_, ?_⟩ <;> rintro _ rfl <;> rfl

/-! ### Carrying the walks: results up to tag, value and witness -/

/-- `ψ'` agrees with `ψ` on everything the definedness of `▶◀` and `⋈` reads. -/
def TSim (hE : K.Ext K') (ψ' : CellUT Loc Val K') (ψ : CellUT Loc Val K) : Prop :=
  ψ'.kind = ψ.kind ∧ ψ'.erase = ψ.erase ∧ ψ'.wit = ψ.wit.map (trU hE)

theorem tsim_trU (hE : K.Ext K') (ψ : CellUT Loc Val K) : TSim hE (trU hE ψ) ψ :=
  ⟨trU_kind hE ψ, trU_erase hE ψ, trU_wit hE ψ⟩

/-- The tag of `ψ₁ ○ ψ₂` is a function of the operands' tags. -/
def kcomb : Kind → Kind → Kind
  | .own, k => k
  | k, .own => k
  | .imm, _ => .imm
  | _, .imm => .imm
  | .mut, .mut => .mut

theorem CellUT.CompR.kind_eq {K : WCactus} {ψ₁ ψ₂ ψ : CellUT Loc Val K}
    (h : CellUT.CompR ψ₁ ψ₂ ψ) : ψ.kind = kcomb ψ₁.kind ψ₂.kind := by
  cases h with
  | same => cases ψ₁ <;> rfl
  | strict k =>
      rw [CellUT.CompS.kind (CellUT.compS_spec _ _ k), (CellUT.CompatS.kinds k).1,
        (CellUT.CompatS.kinds k).2]; rfl
  | mutMut => rfl
  | mutOwn => rfl
  | ownMut => rfl
  | immOwn => rfl
  | ownImm => rfl
  | immMut => rfl
  | mutImm => rfl

/-- The witness of `ψ₁ ○ ψ₂`: the first operand's, unless it is `own`. -/
theorem CellUT.CompR.wit_eq {K : WCactus} {ψ₁ ψ₂ ψ : CellUT Loc Val K}
    (h : CellUT.CompR ψ₁ ψ₂ ψ) :
    ψ.wit = if ψ₁.kind = Kind.own then ψ₂.wit else ψ₁.wit := by
  cases h with
  | same χ => split <;> rfl
  | strict k =>
      rw [if_neg (by rw [(CellUT.CompatS.kinds k).1]; exact fun c => Kind.noConfusion c)]
      exact (CellUT.CompS.wit (CellUT.compS_spec _ _ k)).1
  | mutMut => rw [if_neg (by simp), CellUT.wit_mutOf, CellUT.wit_mutOf]
  | mutOwn => rw [if_neg (by simp)]
  | ownMut => rw [if_pos (by simp)]
  | immOwn => rw [if_neg (by simp)]
  | ownImm => rw [if_pos (by simp)]
  | immMut => rw [if_neg (by simp)]
  | mutImm => rw [if_neg (by simp), CellUT.wit_mutOf, CellUT.wit_immOf]

theorem tsim_compatS (hE : K.Ext K') {ψ₁ ψ₂ : CellUT Loc Val K} {ψ₁' ψ₂' : CellUT Loc Val K'}
    (h₁ : TSim hE ψ₁' ψ₁) (h₂ : TSim hE ψ₂' ψ₂) (h : CellUT.CompatS ψ₁ ψ₂) :
    CellUT.CompatS ψ₁' ψ₂' := by
  obtain ⟨k₁, k₂, hv, hw⟩ := CellUT.compatS_iff.mp h
  exact CellUT.compatS_iff.mpr ⟨h₁.1.trans k₁, h₂.1.trans k₂, h₁.2.1.trans (hv.trans h₂.2.1.symm),
    h₁.2.2.trans (hw ▸ h₂.2.2.symm)⟩

theorem tsim_compatR (hE : K.Ext K') {ψ₁ ψ₂ : CellUT Loc Val K} {ψ₁' ψ₂' : CellUT Loc Val K'}
    (h₁ : TSim hE ψ₁' ψ₁) (h₂ : TSim hE ψ₂' ψ₂) (h : CellUT.CompatR ψ₁ ψ₂) :
    CellUT.CompatR ψ₁' ψ₂' := by
  obtain ⟨hv, hw⟩ := CellUT.compatR_iff.mp h
  refine CellUT.compatR_iff.mpr ⟨h₁.2.1.trans (hv.trans h₂.2.1.symm), fun k₁ k₂ => ?_⟩
  rw [h₁.2.2, h₂.2.2, hw (h₁.1 ▸ k₁) (h₂.1 ▸ k₂)]

theorem tsim_compS (hE : K.Ext K') {ψ₁ ψ₂ ψ : CellUT Loc Val K} {ψ₁' ψ₂' : CellUT Loc Val K'}
    (h₁ : TSim hE ψ₁' ψ₁) (h₂ : TSim hE ψ₂' ψ₂) (h : CellUT.CompS ψ₁ ψ₂ ψ) :
    ∃ ψ', CellUT.CompS ψ₁' ψ₂' ψ' ∧ TSim hE ψ' ψ := by
  have k := tsim_compatS hE h₁ h₂ h.compat
  have hs := CellUT.compS_spec _ _ k
  refine ⟨_, hs, ?_, ?_, ?_⟩
  · rw [CellUT.CompS.kind hs, CellUT.CompS.kind h]
  · rw [(CellUT.CompS.erase hs).1, (CellUT.CompS.erase h).1, h₁.2.1]
  · rw [(CellUT.CompS.wit hs).1, (CellUT.CompS.wit h).1, h₁.2.2]

theorem tsim_compR (hE : K.Ext K') {ψ₁ ψ₂ ψ : CellUT Loc Val K} {ψ₁' ψ₂' : CellUT Loc Val K'}
    (h₁ : TSim hE ψ₁' ψ₁) (h₂ : TSim hE ψ₂' ψ₂) (h : CellUT.CompR ψ₁ ψ₂ ψ) :
    ∃ ψ', CellUT.CompR ψ₁' ψ₂' ψ' ∧ TSim hE ψ' ψ := by
  obtain ⟨ψ', hr⟩ := tsim_compatR hE h₁ h₂ ⟨ψ, h⟩
  refine ⟨ψ', hr, ?_, ?_, ?_⟩
  · rw [CellUT.CompR.kind_eq hr, CellUT.CompR.kind_eq h, h₁.1, h₂.1]
  · rw [(CellUT.CompR.erase hr).2, (CellUT.CompR.erase h).2, h₁.2.1]
  · rw [CellUT.CompR.wit_eq hr, CellUT.CompR.wit_eq h, h₁.1]
    split
    · exact h₂.2.2
    · exact h₁.2.2

/-- Resources related cell by cell. -/
def RSim (hE : K.Ext K') (ρ' : ResUT Loc Val K') (ρ : ResUT Loc Val K) : Prop :=
  ∀ l, Option.Rel (TSim hE) (ρ'.get l) (ρ.get l)

theorem rsim_map (hE : K.Ext K') (ρ : ResUT Loc Val K) : RSim hE (ρ.map (trU hE)) ρ := by
  intro l
  rw [PMap.map_get]
  cases ρ.get l with
  | none => exact Option.Rel.none
  | some ψ => exact Option.Rel.some (tsim_trU hE ψ)

theorem rsim_empty (hE : K.Ext K') :
    RSim hE (PMap.empty : ResUT Loc Val K') (PMap.empty : ResUT Loc Val K) :=
  fun _ => Option.Rel.none

theorem rsim_restrict (hE : K.Ext K') {ρ' : ResUT Loc Val K'} {ρ : ResUT Loc Val K}
    (h : RSim hE ρ' ρ) (k : Kind) :
    RSim hE (G.restrict CellUT.kind ρ' k) (G.restrict CellUT.kind ρ k) := by
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

theorem rsim_sites (hE : K.Ext K') {ρ' : ResUT Loc Val K'} {ρ : ResUT Loc Val K}
    (h : RSim hE ρ' ρ) {k : Kind} {d : List Loc} (hd : G.Sites CellUT.kind ρ k d) :
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
theorem rsim_comp (hE : K.Ext K') {R : CellUT Loc Val K → CellUT Loc Val K → Prop}
    {C : CellUT Loc Val K → CellUT Loc Val K → CellUT Loc Val K → Prop}
    {R' : CellUT Loc Val K' → CellUT Loc Val K' → Prop}
    {C' : CellUT Loc Val K' → CellUT Loc Val K' → CellUT Loc Val K' → Prop}
    (hR' : ∀ ψ₁ ψ₂ ψ, C' ψ₁ ψ₂ ψ → R' ψ₁ ψ₂)
    (hC : ∀ {ψ₁ ψ₂ ψ ψ₁' ψ₂'}, TSim hE ψ₁' ψ₁ → TSim hE ψ₂' ψ₂ → C ψ₁ ψ₂ ψ →
      ∃ ψ', C' ψ₁' ψ₂' ψ' ∧ TSim hE ψ' ψ)
    {ρ₁ ρ₂ ρ : ResUT Loc Val K} {ρ₁' ρ₂' : ResUT Loc Val K'}
    (h₁ : RSim hE ρ₁' ρ₁) (h₂ : RSim hE ρ₂' ρ₂) (h : G.Comp R C ρ₁ ρ₂ ρ) :
    ∃ ρ', G.Comp R' C' ρ₁' ρ₂' ρ' ∧ RSim hE ρ' ρ := by
  have key : ∀ l, ∃ o, G.OptComp C' (ρ₁'.get l) (ρ₂'.get l) o ∧
      Option.Rel (TSim hE) o (ρ.get l) := by
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
      G.OptComp C' (ρ₁'.get l) (ρ₂'.get l) (f l) ∧ Option.Rel (TSim hE) (f l) (ρ.get l) :=
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

theorem rsim_bigComp (hE : K.Ext K') {R : CellUT Loc Val K → CellUT Loc Val K → Prop}
    {C : CellUT Loc Val K → CellUT Loc Val K → CellUT Loc Val K → Prop}
    {R' : CellUT Loc Val K' → CellUT Loc Val K' → Prop}
    {C' : CellUT Loc Val K' → CellUT Loc Val K' → CellUT Loc Val K' → Prop}
    (hR' : ∀ ψ₁ ψ₂ ψ, C' ψ₁ ψ₂ ψ → R' ψ₁ ψ₂)
    (hC : ∀ {ψ₁ ψ₂ ψ ψ₁' ψ₂'}, TSim hE ψ₁' ψ₁ → TSim hE ψ₂' ψ₂ → C ψ₁ ψ₂ ψ →
      ∃ ψ', C' ψ₁' ψ₂' ψ' ∧ TSim hE ψ' ψ)
    {es : List (ResUT Loc Val K)} {b : ResUT Loc Val K} (h : G.BigComp R C es b) :
    ∀ {es' : List (ResUT Loc Val K')}, List.Forall₂ (RSim hE) es' es →
      ∃ b', G.BigComp R' C' es' b' ∧ RSim hE b' b := by
  induction h with
  | nil =>
      intro es' hes
      cases hes
      exact ⟨_, G.BigComp.nil, rsim_empty hE⟩
  | cons hrest hcomp ih =>
      intro es' hes
      cases hes with
      | cons hσ hrest' =>
          obtain ⟨τ', hτ', sτ⟩ := ih hrest'
          obtain ⟨ρ', hρ', sρ⟩ := rsim_comp hE hR' hC hσ sτ hcomp
          exact ⟨ρ', G.BigComp.cons hτ' hρ', sρ⟩

/-- **The exclusive walk carries over.** -/
theorem ExW.graft (hE : K.Ext K') {R : CellUT Loc Val K → CellUT Loc Val K → Prop}
    {C : CellUT Loc Val K → CellUT Loc Val K → CellUT Loc Val K → Prop}
    {R' : CellUT Loc Val K' → CellUT Loc Val K' → Prop}
    {C' : CellUT Loc Val K' → CellUT Loc Val K' → CellUT Loc Val K' → Prop}
    (hR' : ∀ ψ₁ ψ₂ ψ, C' ψ₁ ψ₂ ψ → R' ψ₁ ψ₂)
    (hC : ∀ {ψ₁ ψ₂ ψ ψ₁' ψ₂'}, TSim hE ψ₁' ψ₁ → TSim hE ψ₂' ψ₂ → C ψ₁ ψ₂ ψ →
      ∃ ψ', C' ψ₁' ψ₂' ψ' ∧ TSim hE ψ' ψ)
    {ρ σ : ResUT Loc Val K} (h : G.ExW CellUT.kind CellUT.wit R C ρ σ) :
    ∀ ρ', RSim hE ρ' ρ → ∃ σ', G.ExW CellUT.kind CellUT.wit R' C' ρ' σ' ∧ RSim hE σ' σ := by
  refine G.ExW.rec (motive_1 := fun ρ σ _ => ∀ ρ', RSim hE ρ' ρ →
      ∃ σ', G.ExW CellUT.kind CellUT.wit R' C' ρ' σ' ∧ RSim hE σ' σ)
    (motive_2 := fun ρ w _ => ∀ ρ', RSim hE ρ' ρ →
      ∃ w', G.ExWits CellUT.kind CellUT.wit R' C' ρ' w' ∧ w'.map Prod.fst = w.map Prod.fst ∧
        List.Forall₂ (RSim hE) (w'.map Prod.snd) (w.map Prod.snd))
    ?mk ?nil ?cons h
  case mk =>
    intro ρ₀ σ₀ nm b w hs _ hb hnm hσ ih ρ' hρ
    obtain ⟨w', hw', hfst, hsnd⟩ := ih ρ' hρ
    obtain ⟨b', hb', sb⟩ := rsim_bigComp hE hR' hC hb hsnd
    obtain ⟨nm', hnm', snm⟩ := rsim_comp hE hR' hC (rsim_restrict hE hρ _)
      (rsim_restrict hE hρ _) hnm
    obtain ⟨σ', hσ', sσ⟩ := rsim_comp hE hR' hC snm sb hσ
    exact ⟨σ', G.ExW.mk (hfst ▸ rsim_sites hE hρ hs) hw' hb' hnm' hσ', sσ⟩
  case nil =>
    intro ρ₀ ρ' _
    exact ⟨[], G.ExWits.nil, rfl, List.Forall₂.nil⟩
  case cons =>
    intro ρ₀ e l w ψ hψ hk _ _ ihe ihw ρ' hρ
    obtain ⟨w', hw', hfst, hsnd⟩ := ihw ρ' hρ
    have hl := hρ l
    rw [hψ] at hl
    obtain ⟨ψ', eψ', sψ⟩ : ∃ ψ', ρ'.get l = some ψ' ∧ TSim hE ψ' ψ := by
      revert hl
      cases ρ'.get l with
      | none => intro hl; cases hl
      | some ψ' => intro hl; cases hl with | some h => exact ⟨ψ', rfl, h⟩
    obtain ⟨e', he', se⟩ := ihe ψ'.wit (by rw [sψ.2.2]; exact rsim_map hE _)
    exact ⟨(l, e') :: w', G.ExWits.cons ψ' eψ' (sψ.1.trans hk) he' hw',
      by simp [hfst], List.Forall₂.cons se hsnd⟩

/-- **The aliasable walk carries over.** -/
theorem AgW.graft (hE : K.Ext K') {ρ σ : ResUT Loc Val K} (h : AgWT ρ σ) :
    ∀ ρ', RSim hE ρ' ρ → ∃ σ', AgWT ρ' σ' ∧ RSim hE σ' σ := by
  have hR' : ∀ ψ₁ ψ₂ ψ, CellUT.CompR (K := K') (Loc := Loc) (Val := Val) ψ₁ ψ₂ ψ →
      CellUT.CompatR ψ₁ ψ₂ := fun _ _ ψ hc => ⟨ψ, hc⟩
  have hC : ∀ {ψ₁ ψ₂ ψ : CellUT Loc Val K} {ψ₁' ψ₂' : CellUT Loc Val K'},
      TSim hE ψ₁' ψ₁ → TSim hE ψ₂' ψ₂ → CellUT.CompR ψ₁ ψ₂ ψ →
      ∃ ψ', CellUT.CompR ψ₁' ψ₂' ψ' ∧ TSim hE ψ' ψ := fun a b c => tsim_compR hE a b c
  refine G.AgW.rec (motive_1 := fun ρ σ _ => ∀ ρ', RSim hE ρ' ρ →
      ∃ σ', AgWT ρ' σ' ∧ RSim hE σ' σ)
    (motive_2 := fun ρ w _ => ∀ ρ', RSim hE ρ' ρ →
      ∃ w', G.AgWitsM CellUT.kind CellUT.wit CellUT.CompatR CellUT.CompR ρ' w' ∧
        w'.map Prod.fst = w.map Prod.fst ∧
        List.Forall₂ (RSim hE) (w'.map Prod.snd) (w.map Prod.snd))
    (motive_3 := fun ρ w _ => ∀ ρ', RSim hE ρ' ρ →
      ∃ w', G.AgWitsI CellUT.kind CellUT.wit CellUT.CompatR CellUT.CompR ρ' w' ∧
        w'.map Prod.fst = w.map Prod.fst ∧
        List.Forall₂ (RSim hE) (w'.map Prod.snd) (w.map Prod.snd))
    ?mk ?nilM ?consM ?nilI ?consI h
  case mk =>
    intro ρ₀ σ₀ a bm bi wm wi hsm hsi _ _ hbm hbi ha hσ ihm ihi ρ' hρ
    obtain ⟨wm', hwm', fm, sm⟩ := ihm ρ' hρ
    obtain ⟨wi', hwi', fi, si⟩ := ihi ρ' hρ
    obtain ⟨bm', hbm', sbm⟩ := rsim_bigComp hE hR' hC hbm sm
    obtain ⟨bi', hbi', sbi⟩ := rsim_bigComp hE hR' hC hbi si
    obtain ⟨a', ha', sa⟩ := rsim_comp hE hR' hC (rsim_restrict hE hρ _) sbm ha
    obtain ⟨σ', hσ', sσ⟩ := rsim_comp hE hR' hC sa sbi hσ
    exact ⟨σ', G.AgW.mk (fm ▸ rsim_sites hE hρ hsm) (fi ▸ rsim_sites hE hρ hsi) hwm' hwi'
      hbm' hbi' ha' hσ', sσ⟩
  case nilM => intro ρ₀ ρ' _; exact ⟨[], G.AgWitsM.nil, rfl, List.Forall₂.nil⟩
  case consM =>
    intro ρ₀ e l w ψ hψ hk _ _ ihe ihw ρ' hρ
    obtain ⟨w', hw', hfst, hsnd⟩ := ihw ρ' hρ
    have hl := hρ l
    rw [hψ] at hl
    obtain ⟨ψ', eψ', sψ⟩ : ∃ ψ', ρ'.get l = some ψ' ∧ TSim hE ψ' ψ := by
      revert hl
      cases ρ'.get l with
      | none => intro hl; cases hl
      | some ψ' => intro hl; cases hl with | some h => exact ⟨ψ', rfl, h⟩
    obtain ⟨e', he', se⟩ := ihe ψ'.wit (by rw [sψ.2.2]; exact rsim_map hE _)
    exact ⟨(l, e') :: w', G.AgWitsM.cons ψ' eψ' (sψ.1.trans hk) he' hw',
      by simp [hfst], List.Forall₂.cons se hsnd⟩
  case nilI => intro ρ₀ ρ' _; exact ⟨[], G.AgWitsI.nil, rfl, List.Forall₂.nil⟩
  case consI =>
    intro ρ₀ p l w ψ hψ hk e a hex _ hp _ iha ihw ρ' hρ
    obtain ⟨w', hw', hfst, hsnd⟩ := ihw ρ' hρ
    have hl := hρ l
    rw [hψ] at hl
    obtain ⟨ψ', eψ', sψ⟩ : ∃ ψ', ρ'.get l = some ψ' ∧ TSim hE ψ' ψ := by
      revert hl
      cases ρ'.get l with
      | none => intro hl; cases hl
      | some ψ' => intro hl; cases hl with | some h => exact ⟨ψ', rfl, h⟩
    have sw : RSim hE ψ'.wit ψ.wit := by rw [sψ.2.2]; exact rsim_map hE _
    obtain ⟨e', he', se⟩ := ExW.graft hE hR' hC hex ψ'.wit sw
    obtain ⟨a', ha', sa⟩ := iha ψ'.wit sw
    obtain ⟨p', hp', sp⟩ := rsim_comp hE hR' hC se sa hp
    exact ⟨(l, p') :: w', G.AgWitsI.cons ψ' eψ' (sψ.1.trans hk) e' a' he' ha' hp' hw',
      by simp [hfst], List.Forall₂.cons sp hsnd⟩

/-- **`✓` carries over a graft**: a world valid in `K` is valid, carried, in `K'`. -/
theorem ResUT.Valid.graft (hE : K.Ext K') {ρ : ResUT Loc Val K} (h : ResUT.Valid ρ) :
    ResUT.Valid (ρ.map (trU hE)) := by
  obtain ⟨σ, e, a, he, ha, hσ⟩ := h
  have hRS : ∀ ψ₁ ψ₂ ψ, CellUT.CompS (K := K') (Loc := Loc) (Val := Val) ψ₁ ψ₂ ψ →
      CellUT.CompatS ψ₁ ψ₂ := fun _ _ _ hc => hc.compat
  have hCS : ∀ {ψ₁ ψ₂ ψ : CellUT Loc Val K} {ψ₁' ψ₂' : CellUT Loc Val K'},
      TSim hE ψ₁' ψ₁ → TSim hE ψ₂' ψ₂ → CellUT.CompS ψ₁ ψ₂ ψ →
      ∃ ψ', CellUT.CompS ψ₁' ψ₂' ψ' ∧ TSim hE ψ' ψ := fun a b c => tsim_compS hE a b c
  obtain ⟨e', he', se⟩ := ExW.graft hE hRS hCS he _ (rsim_map hE ρ)
  obtain ⟨a', ha', sa⟩ := AgW.graft hE ha _ (rsim_map hE ρ)
  obtain ⟨σ', hσ', -⟩ := rsim_comp hE hRS hCS se sa hσ
  exact ⟨σ', e', a', he', ha', hσ'⟩

end BoCa.Fig16.Tree

end
