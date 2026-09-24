import Paper.S5_Model.Definitions
import Paper.S6_1_StandardLemmas.Lemmas
import Support.Model.Algebra
import Support.Model.Ancestors
import Support.Model.Cells
import Support.Model.Composition
import Support.Model.FlatteningCells
import Support.Model.Lifetimes
import Support.Model.Prelude
import Support.Model.Singletons
import Support.Model.WalkSplitting

/-!
# Support — Model — Reborrow

`[about ours]`.  `reb_α` at one location, the frame read from `✓` alone, and the cells of a reborrow.
-/

noncomputable section

namespace BoCa.Fig16
variable {Loc Val : Type}

/-- A cell of kind `own` is `own(v)` at its own value. -/
theorem CellU.eq_ownOf_of_kind {ψ : CellU Loc Val} (h : ψ.kind = Kind.own) :
    ψ = CellU.ownOf ψ.erase := by
  rcases CellU.rep ψ with ⟨v, rfl⟩ | ⟨s, v, ρ, hs, rfl⟩ | ⟨b, v, ρ, hs, P, hw, rfl⟩
  · rfl
  · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- `▶◀` holds only between `imm` cells. -/
theorem CellU.CompatS.kind_left {ψ₁ ψ₂ : CellU Loc Val} (h : ψ₁.CompatS ψ₂) :
    ψ₁.kind = Kind.imm := by
  obtain ⟨s₁, s₂, v, ρ, h₁, h₂, e₁, e₂⟩ := h
  rw [e₁]; rfl

/-- Two `imm` cells with equal value and witness are `▶◀`. -/
theorem CellU.compatS_of {ψ₁ ψ₂ : CellU Loc Val} (k₁ : ψ₁.kind = Kind.imm)
    (k₂ : ψ₂.kind = Kind.imm) (hv : ψ₁.erase = ψ₂.erase) (hw : ψ₁.wit = ψ₂.wit) :
    ψ₁.CompatS ψ₂ := by
  obtain ⟨s₁, hs₁, e₁⟩ := CellU.imm_eta k₁
  obtain ⟨s₂, hs₂, e₂⟩ := CellU.imm_eta k₂
  revert hs₁ e₁
  rw [hv, hw]
  intro hs₁ e₁
  exact ⟨s₁, s₂, ψ₂.erase, ψ₂.wit, hs₁, hs₂, e₁, e₂⟩

theorem CellU.CompR.erase_left {a b c : CellU Loc Val} (h : CellU.CompR a b c) :
    c.erase = a.erase := by
  cases h with
  | strict h => obtain ⟨s₁, s₂, v, ρ, h₁, h₂, rfl, rfl⟩ := h; rfl
  | _ => rfl

theorem CellU.CompR.erase_right {a b c : CellU Loc Val} (h : CellU.CompR a b c) :
    c.erase = b.erase := by
  cases h with
  | strict h => obtain ⟨s₁, s₂, v, ρ, h₁, h₂, rfl, rfl⟩ := h; rfl
  | _ => rfl

theorem CellU.CompR.nonown_left {a b c : CellU Loc Val} (h : CellU.CompR a b c)
    (hk : a.kind ≠ Kind.own) : c.kind ≠ Kind.own ∧ c.wit = a.wit := by
  cases h with
  | same ψ => exact ⟨hk, rfl⟩
  | strict h =>
      have hs := CellU.compS_spec _ _ h
      exact ⟨by rw [CellU.CompS.kind hs]; exact fun hc => Kind.noConfusion hc,
             (CellU.CompS.wit hs).1⟩
  | mutMut a b v ρ ha hb P Q hP hQ => exact ⟨by simp, by simp⟩
  | mutOwn a v ρ ha P hP => exact ⟨by simp, rfl⟩
  | ownMut a v ρ ha P hP => exact absurd rfl hk
  | immOwn s v ρ h => exact ⟨by simp, rfl⟩
  | ownImm s v ρ h => exact absurd rfl hk
  | immMut s v ρ h b hb P hP => exact ⟨by simp, rfl⟩
  | mutImm s v ρ h b hb P hP => exact ⟨by simp, by simp⟩

theorem CellU.CompR.nonown_right {a b c : CellU Loc Val} (h : CellU.CompR a b c)
    (hk : b.kind ≠ Kind.own) : c.kind ≠ Kind.own ∧ c.wit = b.wit := by
  cases h with
  | same ψ => exact ⟨hk, rfl⟩
  | strict h =>
      have hs := CellU.compS_spec _ _ h
      exact ⟨by rw [CellU.CompS.kind hs]; exact fun hc => Kind.noConfusion hc,
             (CellU.CompS.wit hs).2⟩
  | mutMut a b v ρ ha hb P Q hP hQ => exact ⟨by simp, by simp⟩
  | mutOwn a v ρ ha P hP => exact absurd rfl hk
  | ownMut a v ρ ha P hP => exact ⟨by simp, rfl⟩
  | immOwn s v ρ h => exact absurd rfl hk
  | ownImm s v ρ h => exact ⟨by simp, rfl⟩
  | immMut s v ρ h b hb P hP => exact ⟨by simp, by simp⟩
  | mutImm s v ρ h b hb P hP => exact ⟨by simp, rfl⟩

theorem ResU.Comp.dom_left {R : CellU Loc Val → CellU Loc Val → Prop}
    {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop}
    {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.Comp R C ρ₁ ρ₂ ρ) {l : Loc}
    {ψ : CellU Loc Val} (hg : ρ₁.get l = some ψ) : ∃ φ, ρ.get l = some φ := by
  rcases h.get l with ⟨e₁, -, -⟩ | ⟨χ, -, -, f⟩ | ⟨χ, e₁, -, -⟩ | ⟨χ₁, χ₂, χ, -, -, f, -⟩
  · rw [hg] at e₁; exact absurd e₁ (by simp)
  · exact ⟨χ, f⟩
  · rw [hg] at e₁; exact absurd e₁ (by simp)
  · exact ⟨χ, f⟩

theorem ResU.Comp.dom_right {R : CellU Loc Val → CellU Loc Val → Prop}
    {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop}
    {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.Comp R C ρ₁ ρ₂ ρ) {l : Loc}
    {ψ : CellU Loc Val} (hg : ρ₂.get l = some ψ) : ∃ φ, ρ.get l = some φ := by
  rcases h.get l with ⟨-, e₂, -⟩ | ⟨χ, -, e₂, -⟩ | ⟨χ, -, -, f⟩ | ⟨χ₁, χ₂, χ, -, -, f, -⟩
  · rw [hg] at e₂; exact absurd e₂ (by simp)
  · rw [hg] at e₂; exact absurd e₂ (by simp)
  · exact ⟨χ, f⟩
  · exact ⟨χ, f⟩

/-- A location covered by one piece of `⨀` is covered by the fold. -/
theorem BigComp.dom {R : CellU Loc Val → CellU Loc Val → Prop}
    {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop}
    {σs : List (ResU Loc Val)} {b : ResU Loc Val} (h : BigComp R C σs b)
    {σ : ResU Loc Val} (hm : σ ∈ σs) {l : Loc} {ζ : CellU Loc Val}
    (hg : σ.get l = some ζ) : ∃ ζ', b.get l = some ζ' := by
  induction h with
  | nil => exact absurd hm (by simp)
  | @cons σ' τ ρ σs' hrest hc ih =>
      rcases List.mem_cons.mp hm with rfl | hm'
      · exact hc.dom_left hg
      · obtain ⟨ζ', hζ'⟩ := ih hm'
        exact hc.dom_right hζ'

/-- `dom(ρ′) ⊆ dom(ρ)` for `ρ′ ∈ reb_α(ρ)`: `[TR]`'s opening note at 6.53
(p. 18). -/
theorem ResU.reb_dom_subset {α : Life} {ρ ρ' : ResU Loc Val}
    (h : ResU.Reb α ρ ρ') {l : Loc} {ψ : CellU Loc Val}
    (hg : ρ'.get l = some ψ) : ∃ φ, ρ.get l = some φ := by
  obtain ⟨-, π, b, hdom, hbig, hle, hat⟩ := h
  obtain ⟨⟨l', p⟩, hpm, hl⟩ := List.mem_map.mp ((hdom.2 l).mpr ⟨ψ, hg⟩)
  cases hl
  obtain ⟨⟨ζ, hζ⟩, -, -, -⟩ := hat l' p hpm
  obtain ⟨ζ', hζ'⟩ := hbig.dom (List.mem_map.mpr ⟨(l', p), hpm, rfl⟩) hζ
  obtain ⟨τ, hτ⟩ := hle
  exact hτ.dom_left hζ'

/-- The `imm` clause of `reb_α` at one location: over an `imm` source cell the
image cell is `imm` over a nonempty subset of its lifetime set, at the same value
and witness (`docs/adjudications.md` §12.67).
`[about ours: the `imm` clause of our `Fig16.ResU.RebAt`, at one location]` -/
theorem ResU.reb_imm_cell_sub {α : Life} {ρ ρ' : ResU Loc Val} (h : ResU.Reb α ρ ρ')
    {l : Loc} {ψ : CellU Loc Val} (hg : ρ'.get l = some ψ)
    {s : LSet} {v : Val} {χ : ResU Loc Val} {hχ : χ.InStratum s.join}
    (hφ : ρ.get l = some (CellU.immOf s v χ hχ)) :
    ∃ (t : LSet) (ht : χ.InStratum t.join), (∀ x, t.mem x → s.mem x) ∧
      ψ = CellU.immOf t v χ ht := by
  obtain ⟨-, π, b, hdom, hbig, hle, hat⟩ := h
  obtain ⟨⟨l', p⟩, hpm, hl⟩ := List.mem_map.mp ((hdom.2 l).mpr ⟨ψ, hg⟩)
  cases hl
  obtain ⟨-, -, -, himm⟩ := hat l' p hpm
  obtain ⟨⟨t, ht, hts, he⟩, -⟩ := himm s v χ hχ hφ
  rw [hg] at he
  exact ⟨t, ht, hts, Option.some.inj he⟩

/-- Over an `imm` source cell the `reb_α` image cell is `imm`, at the same value
and witness, and in every stratum the source cell is in. -/
theorem ResU.reb_imm_cell_kw {α : Life} {ρ ρ' : ResU Loc Val} (h : ResU.Reb α ρ ρ')
    {l : Loc} {ψ φ : CellU Loc Val} (hg : ρ'.get l = some ψ)
    (hφ : ρ.get l = some φ) (hk : φ.kind = Kind.imm) :
    ψ.kind = Kind.imm ∧ ψ.erase = φ.erase ∧ ψ.wit = φ.wit ∧
      (∀ x, φ.InStratum x → ψ.InStratum x) := by
  obtain ⟨s, hs, he⟩ := CellU.imm_eta hk
  obtain ⟨t, ht, hts, rfl⟩ := ResU.reb_imm_cell_sub h hg (hφ.trans (congrArg some he))
  refine ⟨by simp, by simp, by simp, fun x hx => ?_⟩
  rw [he] at hx
  exact lt_of_lt_of_le hx (LSet.meet_mono_of_subset hts)

/-- The `own` and `mut` clauses of `reb_α`: over a non-`imm` cell of the source
the image carries `imm({α}, v, χ)` at the source's value, and its witness is the
source's own except at an `own` cell, where it is built from `π(ℓ)/ℓ`. -/
theorem ResU.reb_src {α : Life} {ρ ρ' : ResU Loc Val} (h : ResU.Reb α ρ ρ')
    {l : Loc} {ψ : CellU Loc Val} (hg : ρ'.get l = some ψ)
    {φ : CellU Loc Val} (hφ : ρ.get l = some φ) (hk : φ.kind ≠ Kind.imm) :
    ∃ (v : Val) (χ : ResU Loc Val) (hχ : χ.InStratum (LSet.singleton α).join),
      ψ = CellU.immOf (LSet.singleton α) v χ hχ ∧ φ.erase = v ∧
        (φ.kind = Kind.own ∨ φ.wit = χ) := by
  obtain ⟨-, π, b, hdom, hbig, hle, hat⟩ := h
  obtain ⟨⟨l', p⟩, hpm, hl⟩ := List.mem_map.mp ((hdom.2 l).mpr ⟨ψ, hg⟩)
  cases hl
  obtain ⟨-, hown, hmut, -⟩ := hat l' p hpm
  rcases CellU.rep φ with ⟨v, rfl⟩ | ⟨s, v, χ, hχ, rfl⟩ | ⟨b', v, χ, hχ, P, hw, rfl⟩
  · obtain ⟨hs, he⟩ := hown v hφ
    rw [hg] at he
    exact ⟨v, p.del l', hs, Option.some.inj he, rfl, Or.inl rfl⟩
  · exact absurd rfl hk
  · obtain ⟨⟨hs, he⟩, -⟩ := hmut b' v χ hχ P hw hφ
    rw [hg] at he
    exact ⟨v, χ, hs, Option.some.inj he, rfl, Or.inr (by simp)⟩

theorem ResU.sites_nil_of_none {ρ : ResU Loc Val} {k : Kind} {d : List Loc}
    (h : ResU.Sites ρ k d) (hno : ∀ l ψ, ρ.get l = some ψ → ψ.kind ≠ k) : d = [] := by
  cases d with
  | nil => rfl
  | cons a t =>
      obtain ⟨ψ, hg, hk⟩ := (h.2 a).mp List.mem_cons_self
      exact absurd hk (hno a ψ hg)

theorem ResU.sites_singleton_of {ρ : ResU Loc Val} {k : Kind} {d : List Loc} {l : Loc}
    (hs : ResU.Sites ρ k d)
    (hchar : ∀ x, (∃ ψ, ρ.get x = some ψ ∧ ψ.kind = k) ↔ x = l) : d = [l] := by
  have hm : ∀ x, x ∈ d ↔ x = l := fun x => (hs.2 x).trans (hchar x)
  cases d with
  | nil => exact absurd ((hm l).mpr rfl) (by simp)
  | cons a t =>
      obtain rfl : a = l := (hm a).mp List.mem_cons_self
      cases t with
      | nil => rfl
      | cons b t' =>
          obtain rfl : b = a := (hm b).mp (List.mem_cons_of_mem _ List.mem_cons_self)
          exact absurd List.mem_cons_self (List.nodup_cons.mp hs.1).1

theorem BigComp.nil_inv {R : CellU Loc Val → CellU Loc Val → Prop}
    {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop} {b : ResU Loc Val}
    (h : BigComp R C [] b) : b = PMap.empty := by cases h; rfl

/-- The exclusive walk carries a non-`imm` cell up with its value, and with its
witness when the cell is not `own`. -/
theorem ExR.get_of_ne_imm {ρ e : ResU Loc Val} (h : ExR ρ e) {l : Loc}
    {ψ : CellU Loc Val} (hg : ρ.get l = some ψ) (hk : ψ.kind ≠ Kind.imm) :
    ∃ χ, e.get l = some χ ∧ χ.erase = ψ.erase ∧
      (ψ.kind ≠ Kind.own → χ.wit = ψ.wit ∧ χ.kind ≠ Kind.own) := by
  cases h with
  | @mk ρ σ nm b w hsites hwits hbig hnm hfin =>
    have hnmeq : nm.get l = some ψ := by
      have h2 := hnm.2 l
      cases hkk : ψ.kind with
      | own =>
          rw [ResU.restrict_get_some hg hkk,
              ResU.restrict_get_ne hg (by rw [hkk]; exact fun hc => Kind.noConfusion hc)] at h2
          exact h2
      | imm => exact absurd hkk hk
      | «mut» =>
          rw [ResU.restrict_get_some hg hkk,
              ResU.restrict_get_ne hg (by rw [hkk]; exact fun hc => Kind.noConfusion hc)] at h2
          exact h2
    have h3 := hfin.2 l
    rw [hnmeq] at h3
    cases hb : b.get l with
    | none => rw [hb] at h3; exact ⟨ψ, h3, rfl, fun hno => ⟨rfl, hno⟩⟩
    | some bc =>
        rw [hb] at h3
        obtain ⟨χ, hχ, hcr⟩ := h3
        exact ⟨χ, hχ, CellU.CompR.erase_left hcr,
          fun hno => ⟨(CellU.CompR.nonown_left hcr hno).2,
                      (CellU.CompR.nonown_left hcr hno).1⟩⟩

/-- `ag` at a singleton `imm` cell, read backwards. -/
theorem AgW.single_imm_inv {l : Loc} {s : LSet} {v : Val} {χ : ResU Loc Val}
    {hstr : χ.InStratum s.join} {σ : ResU Loc Val}
    (h : AgW (ResU.single l (CellU.immOf s v χ hstr)) σ) :
    ∃ e a p, ExR χ e ∧ AgW χ a ∧ ResU.CompR e a p ∧
      ResU.CompR (ResU.single l (CellU.immOf s v χ hstr)) p σ := by
  have hk : (CellU.immOf s v χ hstr).kind = Kind.imm := CellU.kind_immOf _ _ _ _
  cases h with
  | mk hsm hsi hwm hwi hbm hbi ha hσ =>
      rename_i a bm bi wm wi
      obtain rfl : wm = [] := by
        have hnil : wm.map Prod.fst = [] :=
          ResU.sites_nil_of_none hsm (by
            intro m ψ hg
            obtain ⟨-, rfl⟩ := ResU.single_get_eq_some hg
            rw [hk]; exact fun e => Kind.noConfusion e)
        cases wm with
        | nil => rfl
        | cons q t => simp at hnil
      obtain rfl : bm = (PMap.empty : ResU Loc Val) := BigComp.nil_inv hbm
      obtain rfl : a = ResU.single l (CellU.immOf s v χ hstr) := by
        have h1 : a = (ResU.single l (CellU.immOf s v χ hstr)).restrict Kind.imm :=
          ResU.CompR.functional ha (ResU.comp_empty_right _)
        rw [h1, ResU.restrict_single_self hk]
      have hfst : wi.map Prod.fst = [l] := by
        refine ResU.sites_singleton_of hsi (fun x => ⟨?_, ?_⟩)
        · rintro ⟨ψ, hg, -⟩
          exact (ResU.single_get_eq_some hg).1
        · rintro rfl
          exact ⟨_, ResU.single_get_self _ _, hk⟩
      cases wi with
      | nil => simp at hfst
      | cons q t =>
          obtain ⟨x, p⟩ := q
          simp only [List.map_cons, List.cons.injEq] at hfst
          obtain ⟨hx, ht⟩ := hfst
          subst hx
          obtain rfl : t = [] := by
            cases t with
            | nil => rfl
            | cons b t' => simp at ht
          cases hwi with
          | cons ψ hψ hkψ e aw hex hag hp hw =>
              obtain rfl : ψ = CellU.immOf s v χ hstr :=
                Option.some.inj (hψ.symm.trans (ResU.single_get_self _ _))
              rw [CellU.wit_immOf] at hex hag
              obtain rfl : bi = p := by
                cases hbi with
                | cons hnil hcomp =>
                    rename_i τ
                    obtain rfl : τ = (PMap.empty : ResU Loc Val) := BigComp.nil_inv hnil
                    exact ResU.CompR.functional hcomp (ResU.comp_empty_right _)
              exact ⟨e, aw, _, hex, hag, hp, hσ⟩

/-- `⦇ρ′⦈` carries every cell of `ρ′` up with its value, and with its witness
when the cell is not `own` — 6.55's *"witnesses and values always stay the
same"* at the two clauses §12.41 records it as true of. -/
theorem ResU.witFlat_cell {ρ' ev av p : ResU Loc Val}
    (hev : ExR ρ' ev) (hav : AgW ρ' av) (hp : ResU.CompR ev av p)
    {l : Loc} {φ : CellU Loc Val} (hφ : ρ'.get l = some φ) :
    ∃ πl, p.get l = some πl ∧ πl.erase = φ.erase ∧
      (φ.kind ≠ Kind.own → πl.wit = φ.wit ∧ πl.kind ≠ Kind.own) := by
  have h2 := hp.2 l
  by_cases hk : φ.kind = Kind.imm
  · obtain ⟨χ, hχ, hχk, hχe, hχw⟩ := AgW.get_imm hav hφ hk
    have hχn : χ.kind ≠ Kind.own := by rw [hχk]; exact fun hc => Kind.noConfusion hc
    cases hevl : ev.get l with
    | none => rw [hevl, hχ] at h2; exact ⟨χ, h2, hχe, fun _ => ⟨hχw, hχn⟩⟩
    | some c =>
        rw [hevl, hχ] at h2
        obtain ⟨πl, hπ, hcr⟩ := h2
        refine ⟨πl, hπ, ?_, fun _ => ?_⟩
        · rw [CellU.CompR.erase_right hcr, hχe]
        · exact ⟨(CellU.CompR.nonown_right hcr hχn).2.trans hχw,
            (CellU.CompR.nonown_right hcr hχn).1⟩
  · obtain ⟨χ, hχ, hχe, hχn⟩ := ExR.get_of_ne_imm hev hφ hk
    cases havl : av.get l with
    | none => rw [hχ, havl] at h2; exact ⟨χ, h2, hχe, fun hno => hχn hno⟩
    | some c =>
        rw [hχ, havl] at h2
        obtain ⟨πl, hπ, hcr⟩ := h2
        refine ⟨πl, hπ, ?_, fun hno => ?_⟩
        · rw [CellU.CompR.erase_left hcr, hχe]
        · exact ⟨(CellU.CompR.nonown_left hcr (hχn hno).2).2.trans (hχn hno).1,
            (CellU.CompR.nonown_left hcr (hχn hno).2).1⟩

/-- From `✓(ρf ● ℓ ↦ imm(α, ρ′, v))`: a frame cell over `dom(ρ′)` is `imm`,
carries `ρ′`'s value, and carries `ρ′`'s witness wherever `ρ′`'s cell is not
`own`. -/
theorem ResU.frame_cell {ρf ρ' ρc : ResU Loc Val} {l₀ : Loc} {s : LSet} {v : Val}
    {hs : ρ'.InStratum s.join}
    (hcomp : ResU.CompS ρf (ResU.single l₀ (CellU.immOf s v ρ' hs)) ρc)
    (hval : ρc.Valid) {l : Loc} {ψf φ : CellU Loc Val}
    (hf : ρf.get l = some ψf) (hφ : ρ'.get l = some φ) :
    ψf.kind = Kind.imm ∧ ψf.erase = φ.erase ∧ (φ.kind ≠ Kind.own → ψf.wit = φ.wit) := by
  obtain ⟨σ, e, a, hex, hag, hcs⟩ := hval
  obtain ⟨e₁, e₂, hef, hei, he12⟩ := (ExS.split hcomp).mp hex
  obtain ⟨a₁, a₂, haf, hai, ha12⟩ := (AgW.split hcomp).mp hag
  obtain ⟨ev, av, p, hev, hav, hp, hpa⟩ := AgW.single_imm_inv hai
  obtain ⟨πl, hπ, hπe, hπn⟩ := ResU.witFlat_cell hev hav hp hφ
  have ha2 : ∃ α, a₂.get l = some α ∧ α.erase = φ.erase ∧
      (φ.kind ≠ Kind.own → α.wit = φ.wit ∧ α.kind ≠ Kind.own) := by
    have h2 := hpa.2 l
    cases hsl : (ResU.single l₀ (CellU.immOf s v ρ' hs)).get l with
    | none => rw [hsl, hπ] at h2; exact ⟨πl, h2, hπe, hπn⟩
    | some c =>
        rw [hsl, hπ] at h2
        obtain ⟨α, hα, hcr⟩ := h2
        refine ⟨α, hα, ?_, fun hno => ?_⟩
        · rw [CellU.CompR.erase_right hcr, hπe]
        · exact ⟨(CellU.CompR.nonown_right hcr (hπn hno).2).2.trans (hπn hno).1,
                 (CellU.CompR.nonown_right hcr (hπn hno).2).1⟩
  obtain ⟨α, hα, hαe, hαn⟩ := ha2
  have haget : ∃ α', a.get l = some α' := by
    have h2 := ha12.2 l
    cases h1 : a₁.get l with
    | none => rw [h1, hα] at h2; exact ⟨α, h2⟩
    | some χ => rw [h1, hα] at h2; obtain ⟨α', hα', _⟩ := h2; exact ⟨α', hα'⟩
  obtain ⟨α', hα'⟩ := haget
  have hkf : ψf.kind = Kind.imm := by
    by_contra hne
    have he1 : e₁.get l = some ψf := ExS.get_of_ne_imm hef hf hne
    have he2 : e₂.get l = none := by
      cases h : e₂.get l with
      | none => rfl
      | some ζ => exact absurd (CellU.CompatS.kind_left (he12.1 l ψf ζ he1 h)) hne
    have hel : e.get l = some ψf := by
      have h2 := he12.2 l; rw [he1, he2] at h2; exact h2
    exact hne (CellU.CompatS.kind_left (hcs.1 l ψf α' hel hα'))
  obtain ⟨χf, hχf, hχfk, hχfe, hχfw⟩ := AgW.get_imm haf hf hkf
  have h2 := ha12.2 l
  rw [hχf, hα] at h2
  obtain ⟨α'', hα'', hcr⟩ := h2
  refine ⟨hkf, ?_, fun hno => ?_⟩
  · rw [← hχfe, ← CellU.CompR.erase_left hcr, CellU.CompR.erase_right hcr, hαe]
  · have hχn : χf.kind ≠ Kind.own := by rw [hχfk]; exact fun hc => Kind.noConfusion hc
    have h1 := (CellU.CompR.nonown_left hcr hχn).2
    have h3 := (CellU.CompR.nonown_right hcr (hαn hno).2).2
    rw [← hχfw, ← h1, h3, (hαn hno).1]

end BoCa.Fig16

end
