import Support.Model.Tree.Port.RebDef

/-!
# The printed source over the tree-stratified carrier

`[spec §62]`. `Support/Model/Reborrow.lean`, read at `CellUT K`, by the printed proofs.
-/

noncomputable section

/-!
# Support — Model — Reborrow

`[about ours]`.  `reb_α` at one location, the frame read from `✓` alone, and the cells of a reborrow.
-/



namespace BoCa.Fig16.Tree
open BoCa.Fig16
variable {Loc Val : Type} {K : WCactus}
/-- A cell of kind `own` is `own(v)` at its own value. -/
theorem CellUT.eq_ownOf_of_kind {ψ : CellUT Loc Val K} (h : ψ.kind = Kind.own) :
    ψ = CellUT.ownOf ψ.erase := by
  rcases CellUT.rep' ψ with ⟨v, rfl⟩ | ⟨s, v, ρ, hs, rfl⟩ | ⟨b, _, v, ρ, hs, P, hw, rfl⟩
  · rfl
  · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- `▶◀` holds only between `imm` cells. -/
theorem CellUT.CompatS.kind_left {ψ₁ ψ₂ : CellUT Loc Val K} (h : ψ₁.CompatS ψ₂) :
    ψ₁.kind = Kind.imm := by
  obtain ⟨s₁, s₂, v, ρ, h₁, h₂, e₁, e₂⟩ := h
  rw [e₁]; rfl

/-- Two `imm` cells with equal value and witness are `▶◀`. -/
theorem CellUT.compatS_of {ψ₁ ψ₂ : CellUT Loc Val K} (k₁ : ψ₁.kind = Kind.imm)
    (k₂ : ψ₂.kind = Kind.imm) (hv : ψ₁.erase = ψ₂.erase) (hw : ψ₁.wit = ψ₂.wit) :
    ψ₁.CompatS ψ₂ := by
  obtain ⟨s₁, hs₁, e₁⟩ := CellUT.imm_eta k₁
  obtain ⟨s₂, hs₂, e₂⟩ := CellUT.imm_eta k₂
  revert hs₁ e₁
  rw [hv, hw]
  intro hs₁ e₁
  exact ⟨s₁, s₂, ψ₂.erase, ψ₂.wit, hs₁, hs₂, e₁, e₂⟩

theorem CellUT.CompR.erase_left {a b c : CellUT Loc Val K} (h : CellUT.CompR a b c) :
    c.erase = a.erase := by
  cases h with
  | strict h => obtain ⟨s₁, s₂, v, ρ, h₁, h₂, rfl, rfl⟩ := h; rfl
  | _ => rfl

theorem CellUT.CompR.erase_right {a b c : CellUT Loc Val K} (h : CellUT.CompR a b c) :
    c.erase = b.erase := by
  cases h with
  | strict h => obtain ⟨s₁, s₂, v, ρ, h₁, h₂, rfl, rfl⟩ := h; rfl
  | _ => rfl

theorem CellUT.CompR.nonown_left {a b c : CellUT Loc Val K} (h : CellUT.CompR a b c)
    (hk : a.kind ≠ Kind.own) : c.kind ≠ Kind.own ∧ c.wit = a.wit := by
  cases h with
  | same ψ => exact ⟨hk, rfl⟩
  | strict h =>
      have hs := CellUT.compS_spec _ _ h
      exact ⟨by rw [CellUT.CompS.kind hs]; exact fun hc => Kind.noConfusion hc,
             (CellUT.CompS.wit hs).1⟩
  | mutMut a b v ρ ha hb P Q hP hQ => exact ⟨by simp, by simp⟩
  | mutOwn a v ρ ha P hP => exact ⟨by simp, rfl⟩
  | ownMut a v ρ ha P hP => exact absurd rfl hk
  | immOwn s v ρ h => exact ⟨by simp, rfl⟩
  | ownImm s v ρ h => exact absurd rfl hk
  | immMut s v ρ h b hb P hP => exact ⟨by simp, rfl⟩
  | mutImm s v ρ h b hb P hP => exact ⟨by simp, by simp⟩

theorem CellUT.CompR.nonown_right {a b c : CellUT Loc Val K} (h : CellUT.CompR a b c)
    (hk : b.kind ≠ Kind.own) : c.kind ≠ Kind.own ∧ c.wit = b.wit := by
  cases h with
  | same ψ => exact ⟨hk, rfl⟩
  | strict h =>
      have hs := CellUT.compS_spec _ _ h
      exact ⟨by rw [CellUT.CompS.kind hs]; exact fun hc => Kind.noConfusion hc,
             (CellUT.CompS.wit hs).2⟩
  | mutMut a b v ρ ha hb P Q hP hQ => exact ⟨by simp, by simp⟩
  | mutOwn a v ρ ha P hP => exact absurd rfl hk
  | ownMut a v ρ ha P hP => exact ⟨by simp, rfl⟩
  | immOwn s v ρ h => exact absurd rfl hk
  | ownImm s v ρ h => exact ⟨by simp, rfl⟩
  | immMut s v ρ h b hb P hP => exact ⟨by simp, by simp⟩
  | mutImm s v ρ h b hb P hP => exact ⟨by simp, rfl⟩

theorem ResUT.Comp.dom_left {R : CellUT Loc Val K → CellUT Loc Val K → Prop}
    {C : CellUT Loc Val K → CellUT Loc Val K → CellUT Loc Val K → Prop}
    {ρ₁ ρ₂ ρ : ResUT Loc Val K} (h : ResUT.Comp R C ρ₁ ρ₂ ρ) {l : Loc}
    {ψ : CellUT Loc Val K} (hg : ρ₁.get l = some ψ) : ∃ φ, ρ.get l = some φ := by
  rcases ResUT.Comp.get h l with ⟨e₁, -, -⟩ | ⟨χ, -, -, f⟩ | ⟨χ, e₁, -, -⟩ | ⟨χ₁, χ₂, χ, -, -, f, -⟩
  · rw [hg] at e₁; exact absurd e₁ (by simp)
  · exact ⟨χ, f⟩
  · rw [hg] at e₁; exact absurd e₁ (by simp)
  · exact ⟨χ, f⟩

theorem ResUT.Comp.dom_right {R : CellUT Loc Val K → CellUT Loc Val K → Prop}
    {C : CellUT Loc Val K → CellUT Loc Val K → CellUT Loc Val K → Prop}
    {ρ₁ ρ₂ ρ : ResUT Loc Val K} (h : ResUT.Comp R C ρ₁ ρ₂ ρ) {l : Loc}
    {ψ : CellUT Loc Val K} (hg : ρ₂.get l = some ψ) : ∃ φ, ρ.get l = some φ := by
  rcases ResUT.Comp.get h l with ⟨-, e₂, -⟩ | ⟨χ, -, e₂, -⟩ | ⟨χ, -, -, f⟩ | ⟨χ₁, χ₂, χ, -, -, f, -⟩
  · rw [hg] at e₂; exact absurd e₂ (by simp)
  · rw [hg] at e₂; exact absurd e₂ (by simp)
  · exact ⟨χ, f⟩
  · exact ⟨χ, f⟩

/-- A location covered by one piece of `⨀` is covered by the fold. -/
theorem BigCompT.dom {R : CellUT Loc Val K → CellUT Loc Val K → Prop}
    {C : CellUT Loc Val K → CellUT Loc Val K → CellUT Loc Val K → Prop}
    {σs : List (ResUT Loc Val K)} {b : ResUT Loc Val K} (h : BigCompT R C σs b)
    {σ : ResUT Loc Val K} (hm : σ ∈ σs) {l : Loc} {ζ : CellUT Loc Val K}
    (hg : σ.get l = some ζ) : ∃ ζ', b.get l = some ζ' := by
  induction h with
  | nil => exact absurd hm (by simp)
  | @cons σ' τ ρ σs' hrest hc ih =>
      rcases List.mem_cons.mp hm with rfl | hm'
      · exact ResUT.Comp.dom_left hc hg
      · obtain ⟨ζ', hζ'⟩ := ih hm'
        exact ResUT.Comp.dom_right hc hζ'

/-- `dom(ρ′) ⊆ dom(ρ)` for `ρ′ ∈ reb_α(ρ)`: `[TR]`'s opening note at 6.53
(p. 18). -/
theorem ResUT.reb_dom_subset {α : Life} {ρ ρ' : ResUT Loc Val K}
    (h : ResUT.Reb α ρ ρ') {l : Loc} {ψ : CellUT Loc Val K}
    (hg : ρ'.get l = some ψ) : ∃ φ, ρ.get l = some φ := by
  obtain ⟨-, π, b, hdom, hbig, hle, hat⟩ := h
  obtain ⟨⟨l', p⟩, hpm, hl⟩ := List.mem_map.mp ((hdom.2 l).mpr ⟨ψ, hg⟩)
  cases hl
  obtain ⟨⟨ζ, hζ⟩, -, -, -⟩ := hat l' p hpm
  obtain ⟨ζ', hζ'⟩ := hbig.dom (List.mem_map.mpr ⟨(l', p), hpm, rfl⟩) hζ
  obtain ⟨τ, hτ⟩ := hle
  exact ResUT.Comp.dom_left hτ hζ'

/-- The `imm` clause of `reb_α` at one location: over an `imm` source cell the
image cell is `imm` over a nonempty subset of its lifetime set, at the same value
and witness (`docs/adjudications.md` §12.67).
`[about ours: the `imm` clause of our `Tree.ResUT.RebAt`, at one location]` -/
theorem ResUT.reb_imm_cell_sub {α : Life} {ρ ρ' : ResUT Loc Val K} (h : ResUT.Reb α ρ ρ')
    {l : Loc} {ψ : CellUT Loc Val K} (hg : ρ'.get l = some ψ)
    {s : TSet} {v : Val} {χ : ResUT Loc Val K} {hχ : χ.InStratum s}
    (hφ : ρ.get l = some (CellUT.immOf s v χ hχ)) :
    ∃ (t : TSet) (ht : χ.InStratum t), t.set ⊆ s.set ∧
      ψ = CellUT.immOf t v χ ht := by
  obtain ⟨-, π, b, hdom, hbig, hle, hat⟩ := h
  obtain ⟨⟨l', p⟩, hpm, hl⟩ := List.mem_map.mp ((hdom.2 l).mpr ⟨ψ, hg⟩)
  cases hl
  obtain ⟨-, -, -, himm⟩ := hat l' p hpm
  obtain ⟨⟨t, ht, hts, he⟩, -⟩ := himm s v χ hχ hφ
  rw [hg] at he
  exact ⟨t, ht, hts, Option.some.inj he⟩

/-- Over an `imm` source cell the `reb_α` image cell is `imm`, at the same value
and witness, and in every stratum the source cell is in. -/
theorem ResUT.reb_imm_cell_kw {α : Life} {ρ ρ' : ResUT Loc Val K} (h : ResUT.Reb α ρ ρ')
    {l : Loc} {ψ φ : CellUT Loc Val K} (hg : ρ'.get l = some ψ)
    (hφ : ρ.get l = some φ) (hk : φ.kind = Kind.imm) :
    ψ.kind = Kind.imm ∧ ψ.erase = φ.erase ∧ ψ.wit = φ.wit ∧
      (∀ x, φ.InStratum x → ψ.InStratum x) := by
  obtain ⟨s, hs, he⟩ := CellUT.imm_eta hk
  obtain ⟨t, ht, hts, rfl⟩ := ResUT.reb_imm_cell_sub h hg (hφ.trans (congrArg some he))
  refine ⟨by simp, by simp, by simp, fun x hx => ?_⟩
  rw [he] at hx
  exact fun a ha c hc => hx a ha c (hts hc)

/-- The `own` and `mut` clauses of `reb_α`: over a non-`imm` cell of the source
the image carries `imm({α}, v, χ)` at the source's value, and its witness is the
source's own except at an `own` cell, where it is built from `π(ℓ)/ℓ`. -/
theorem ResUT.reb_src {α : Life} {ρ ρ' : ResUT Loc Val K} (h : ResUT.Reb α ρ ρ')
    {l : Loc} {ψ : CellUT Loc Val K} (hg : ρ'.get l = some ψ)
    {φ : CellUT Loc Val K} (hφ : ρ.get l = some φ) (hk : φ.kind ≠ Kind.imm) :
    ∃ (v : Val) (χ : ResUT Loc Val K) (hχ : χ.InStratum (TSet.single α)),
      ψ = CellUT.immOf (TSet.single α) v χ hχ ∧ φ.erase = v ∧
        (φ.kind = Kind.own ∨ φ.wit = χ) := by
  obtain ⟨-, π, b, hdom, hbig, hle, hat⟩ := h
  obtain ⟨⟨l', p⟩, hpm, hl⟩ := List.mem_map.mp ((hdom.2 l).mpr ⟨ψ, hg⟩)
  cases hl
  obtain ⟨-, hown, hmut, -⟩ := hat l' p hpm
  rcases CellUT.rep' φ with ⟨v, rfl⟩ | ⟨s, v, χ, hχ, rfl⟩ | ⟨b', _, v, χ, hχ, P, hw, rfl⟩
  · obtain ⟨hs, he⟩ := hown v hφ
    rw [hg] at he
    exact ⟨v, p.del l', hs, Option.some.inj he, rfl, Or.inl rfl⟩
  · exact absurd rfl hk
  · obtain ⟨⟨hs, he⟩, -⟩ := hmut b' v χ hχ P hw hφ
    rw [hg] at he
    exact ⟨v, χ, hs, Option.some.inj he, rfl, Or.inr (by simp)⟩

/-- The exclusive walk carries a non-`imm` cell up with its value, and with its
witness when the cell is not `own`. -/
theorem ExRT.get_of_ne_imm {ρ e : ResUT Loc Val K} (h : ExRT ρ e) {l : Loc}
    {ψ : CellUT Loc Val K} (hg : ρ.get l = some ψ) (hk : ψ.kind ≠ Kind.imm) :
    ∃ χ, e.get l = some χ ∧ χ.erase = ψ.erase ∧
      (ψ.kind ≠ Kind.own → χ.wit = ψ.wit ∧ χ.kind ≠ Kind.own) := by
  cases h with
  | @mk ρ σ nm b w hsites hwits hbig hnm hfin =>
    have hnmeq : nm.get l = some ψ := by
      have h2 := hnm.2 l
      cases hkk : ψ.kind with
      | own =>
          rw [ResUT.restrict_get_some hg hkk,
              ResUT.restrict_get_ne hg (by rw [hkk]; exact fun hc => Kind.noConfusion hc)] at h2
          exact h2
      | imm => exact absurd hkk hk
      | «mut» =>
          rw [ResUT.restrict_get_some hg hkk,
              ResUT.restrict_get_ne hg (by rw [hkk]; exact fun hc => Kind.noConfusion hc)] at h2
          exact h2
    have h3 := hfin.2 l
    rw [hnmeq] at h3
    cases hb : b.get l with
    | none => rw [hb] at h3; exact ⟨ψ, h3, rfl, fun hno => ⟨rfl, hno⟩⟩
    | some bc =>
        rw [hb] at h3
        obtain ⟨χ, hχ, hcr⟩ := h3
        exact ⟨χ, hχ, CellUT.CompR.erase_left hcr,
          fun hno => ⟨(CellUT.CompR.nonown_left hcr hno).2,
                      (CellUT.CompR.nonown_left hcr hno).1⟩⟩

/-- `ag` at a singleton `imm` cell, read backwards. -/
theorem AgWT.single_imm_inv {l : Loc} {s : TSet} {v : Val} {χ : ResUT Loc Val K}
    {hstr : χ.InStratum s} {σ : ResUT Loc Val K}
    (h : AgWT (ResUT.single l (CellUT.immOf s v χ hstr)) σ) :
    ∃ e a p, ExRT χ e ∧ AgWT χ a ∧ ResUT.CompR e a p ∧
      ResUT.CompR (ResUT.single l (CellUT.immOf s v χ hstr)) p σ := by
  have hk : (CellUT.immOf s v χ hstr).kind = Kind.imm := CellUT.kind_immOf _ _ _ _
  cases h with
  | mk hsm hsi hwm hwi hbm hbi ha hσ =>
      rename_i a bm bi wm wi
      obtain rfl : wm = [] := by
        have hnil : wm.map Prod.fst = [] :=
          ResUT.sites_nil_of_none hsm (by
            intro m ψ hg
            obtain ⟨-, rfl⟩ := ResUT.single_get_eq_some hg
            rw [hk]; exact fun e => Kind.noConfusion e)
        cases wm with
        | nil => rfl
        | cons q t => simp at hnil
      obtain rfl : bm = (PMap.empty : ResUT Loc Val K) := BigCompT.nil_inv hbm
      obtain rfl : a = ResUT.single l (CellUT.immOf s v χ hstr) := by
        have h1 : a = (G.restrict CellUT.kind (ResUT.single l (CellUT.immOf s v χ hstr)) Kind.imm) :=
          ResUT.CompR.functional ha (ResUT.comp_empty_right _)
        rw [h1, ResUT.restrict_single_self hk]
      have hfst : wi.map Prod.fst = [l] := by
        refine ResUT.sites_singleton_of hsi (fun x => ⟨?_, ?_⟩)
        · rintro ⟨ψ, hg, -⟩
          exact (ResUT.single_get_eq_some hg).1
        · rintro rfl
          exact ⟨_, ResUT.single_get_self _ _, hk⟩
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
              obtain rfl : ψ = CellUT.immOf s v χ hstr :=
                Option.some.inj (hψ.symm.trans (ResUT.single_get_self _ _))
              rw [CellUT.wit_immOf] at hex hag
              obtain rfl : bi = p := by
                cases hbi with
                | cons hnil hcomp =>
                    rename_i τ
                    obtain rfl : τ = (PMap.empty : ResUT Loc Val K) := BigCompT.nil_inv hnil
                    exact ResUT.CompR.functional hcomp (ResUT.comp_empty_right _)
              exact ⟨e, aw, _, hex, hag, hp, hσ⟩

/-- `⦇ρ′⦈` carries every cell of `ρ′` up with its value, and with its witness
when the cell is not `own` — 6.55's *"witnesses and values always stay the
same"* at the two clauses §12.41 records it as true of. -/
theorem ResUT.witFlat_cell {ρ' ev av p : ResUT Loc Val K}
    (hev : ExRT ρ' ev) (hav : AgWT ρ' av) (hp : ResUT.CompR ev av p)
    {l : Loc} {φ : CellUT Loc Val K} (hφ : ρ'.get l = some φ) :
    ∃ πl, p.get l = some πl ∧ πl.erase = φ.erase ∧
      (φ.kind ≠ Kind.own → πl.wit = φ.wit ∧ πl.kind ≠ Kind.own) := by
  have h2 := hp.2 l
  by_cases hk : φ.kind = Kind.imm
  · obtain ⟨χ, hχ, hχk, hχe, hχw⟩ := AgWT.get_imm hav hφ hk
    have hχn : χ.kind ≠ Kind.own := by rw [hχk]; exact fun hc => Kind.noConfusion hc
    cases hevl : ev.get l with
    | none => rw [hevl, hχ] at h2; exact ⟨χ, h2, hχe, fun _ => ⟨hχw, hχn⟩⟩
    | some c =>
        rw [hevl, hχ] at h2
        obtain ⟨πl, hπ, hcr⟩ := h2
        refine ⟨πl, hπ, ?_, fun _ => ?_⟩
        · rw [CellUT.CompR.erase_right hcr, hχe]
        · exact ⟨(CellUT.CompR.nonown_right hcr hχn).2.trans hχw,
            (CellUT.CompR.nonown_right hcr hχn).1⟩
  · obtain ⟨χ, hχ, hχe, hχn⟩ := ExRT.get_of_ne_imm hev hφ hk
    cases havl : av.get l with
    | none => rw [hχ, havl] at h2; exact ⟨χ, h2, hχe, fun hno => hχn hno⟩
    | some c =>
        rw [hχ, havl] at h2
        obtain ⟨πl, hπ, hcr⟩ := h2
        refine ⟨πl, hπ, ?_, fun hno => ?_⟩
        · rw [CellUT.CompR.erase_left hcr, hχe]
        · exact ⟨(CellUT.CompR.nonown_left hcr (hχn hno).2).2.trans (hχn hno).1,
            (CellUT.CompR.nonown_left hcr (hχn hno).2).1⟩

/-- From `✓(ρf ● ℓ ↦ imm(α, ρ′, v))`: a frame cell over `dom(ρ′)` is `imm`,
carries `ρ′`'s value, and carries `ρ′`'s witness wherever `ρ′`'s cell is not
`own`. -/
theorem ResUT.frame_cell {ρf ρ' ρc : ResUT Loc Val K} {l₀ : Loc} {s : TSet} {v : Val}
    {hs : ρ'.InStratum s}
    (hcomp : ResUT.CompS ρf (ResUT.single l₀ (CellUT.immOf s v ρ' hs)) ρc)
    (hval : ρc.Valid) {l : Loc} {ψf φ : CellUT Loc Val K}
    (hf : ρf.get l = some ψf) (hφ : ρ'.get l = some φ) :
    ψf.kind = Kind.imm ∧ ψf.erase = φ.erase ∧ (φ.kind ≠ Kind.own → ψf.wit = φ.wit) := by
  obtain ⟨σ, e, a, hex, hag, hcs⟩ := hval
  obtain ⟨e₁, e₂, hef, hei, he12⟩ := (ExST.split hcomp).mp hex
  obtain ⟨a₁, a₂, haf, hai, ha12⟩ := (AgWT.split hcomp).mp hag
  obtain ⟨ev, av, p, hev, hav, hp, hpa⟩ := AgWT.single_imm_inv hai
  obtain ⟨πl, hπ, hπe, hπn⟩ := ResUT.witFlat_cell hev hav hp hφ
  have ha2 : ∃ α, a₂.get l = some α ∧ α.erase = φ.erase ∧
      (φ.kind ≠ Kind.own → α.wit = φ.wit ∧ α.kind ≠ Kind.own) := by
    have h2 := hpa.2 l
    cases hsl : (ResUT.single l₀ (CellUT.immOf s v ρ' hs)).get l with
    | none => rw [hsl, hπ] at h2; exact ⟨πl, h2, hπe, hπn⟩
    | some c =>
        rw [hsl, hπ] at h2
        obtain ⟨α, hα, hcr⟩ := h2
        refine ⟨α, hα, ?_, fun hno => ?_⟩
        · rw [CellUT.CompR.erase_right hcr, hπe]
        · exact ⟨(CellUT.CompR.nonown_right hcr (hπn hno).2).2.trans (hπn hno).1,
                 (CellUT.CompR.nonown_right hcr (hπn hno).2).1⟩
  obtain ⟨α, hα, hαe, hαn⟩ := ha2
  have haget : ∃ α', a.get l = some α' := by
    have h2 := ha12.2 l
    cases h1 : a₁.get l with
    | none => rw [h1, hα] at h2; exact ⟨α, h2⟩
    | some χ => rw [h1, hα] at h2; obtain ⟨α', hα', _⟩ := h2; exact ⟨α', hα'⟩
  obtain ⟨α', hα'⟩ := haget
  have hkf : ψf.kind = Kind.imm := by
    by_contra hne
    have he1 : e₁.get l = some ψf := ExST.get_of_ne_imm hef hf hne
    have he2 : e₂.get l = none := by
      cases h : e₂.get l with
      | none => rfl
      | some ζ => exact absurd (CellUT.CompatS.kind_left (he12.1 l ψf ζ he1 h)) hne
    have hel : e.get l = some ψf := by
      have h2 := he12.2 l; rw [he1, he2] at h2; exact h2
    exact hne (CellUT.CompatS.kind_left (hcs.1 l ψf α' hel hα'))
  obtain ⟨χf, hχf, hχfk, hχfe, hχfw⟩ := AgWT.get_imm haf hf hkf
  have h2 := ha12.2 l
  rw [hχf, hα] at h2
  obtain ⟨α'', hα'', hcr⟩ := h2
  refine ⟨hkf, ?_, fun hno => ?_⟩
  · rw [← hχfe, ← CellUT.CompR.erase_left hcr, CellUT.CompR.erase_right hcr, hαe]
  · have hχn : χf.kind ≠ Kind.own := by rw [hχfk]; exact fun hc => Kind.noConfusion hc
    have h1 := (CellUT.CompR.nonown_left hcr hχn).2
    have h3 := (CellUT.CompR.nonown_right hcr (hαn hno).2).2
    rw [← hχfw, ← h1, h3, (hαn hno).1]

end BoCa.Fig16.Tree

end
