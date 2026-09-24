import Paper.S5_Model.Definitions
import Paper.S6_1_StandardLemmas.Lemmas
import Paper.S6_2_NonStandardLemmas.Definitions
import Support.Model.Algebra
import Support.Model.AlgebraInstances
import Support.Model.Ancestors
import Support.Model.Compatibility
import Support.Model.Composition
import Support.Model.FlatteningCells
import Support.Model.Prelude
import Support.Model.Reborrow
import Support.Model.Singletons
import Support.Model.Update
import Support.Model.WalkSplitting
import Support.Model.Walks

/-!
# Support — Model — ReborrowFrame

`[about ours]`.  The steps of Lemmas 6.53–6.55 and 6.61 that the printed proofs name.
-/

noncomputable section

namespace BoCa.Fig16
variable {Loc Val : Type}

/-- `ρ_f # ρ_i` gives `ag(ρ_f)`.
`[about ours: the `ag(ρ_f)` of `[TR]` p. 18's displays, from the printed `#`]` -/
theorem ResU.agW_of_hash_left {ρf ρi ρc : ResU Loc Val}
    (hcomp : ResU.CompS ρf ρi ρc) (hval : ρc.Valid) : ∃ a, AgW ρf a := by
  obtain ⟨σ, e, a, hex, hag, hcs⟩ := hval
  obtain ⟨a₁, a₂, haf, -, -⟩ := (AgW.split hcomp).mp hag
  exact ⟨a₁, haf⟩

/-- `[TR]` p. 18, in the proof of 6.55: *"`ρ` and `ρ′` differ only by
potentially changing from own or mut to imm, but witnesses and values always stay
the same"*, at `reb_α`'s `own` clause (`docs/adjudications.md` §12.41).  Over an
`own` cell of the source `χ`, a cell of the image `ρ` and a cell of `σ` at that
location carry the same witness whenever neither is `own`.
`[about ours: a named hypothesis for the sentence `[TR]` p. 18 asserts]` -/
def EscrowAgree (χ ρ σ : ResU Loc Val) : Prop :=
  ∀ (l : Loc) (v : Val) (ψ ψf : CellU Loc Val),
    χ.get l = some (CellU.ownOf v) → ρ.get l = some ψ → σ.get l = some ψf →
      ψ.kind ≠ Kind.own → ψf.kind ≠ Kind.own → ψf.wit = ψ.wit

/-- `EscrowAgree` holds at a source with no `own` cell (§12.41).
`[about ours: the added hypothesis is empty off the `own` clause]` -/
theorem escrowAgree_of_no_own {χ : ResU Loc Val}
    (h : ∀ l ψ, χ.get l = some ψ → ψ.kind ≠ Kind.own) (ρ σ : ResU Loc Val) :
    EscrowAgree χ ρ σ := by
  intro l v ψ ψf hχ _ _ _ _
  exact absurd rfl (h l _ hχ)

/-- The image of `reb_α` carries `imm` cells only: the `ρ|own,mut = ∅` 6.52's
and 6.53's proofs open with. -/
theorem ResU.reb_imm_image {α : Life} {ρ ρ' : ResU Loc Val} (h : ResU.Reb α ρ ρ')
    {l : Loc} {ψ : CellU Loc Val} (hg : ρ'.get l = some ψ) : ψ.kind = Kind.imm := by
  obtain ⟨φ, hφ⟩ := ResU.reb_dom_subset h hg
  by_cases hk : φ.kind = Kind.imm
  · exact (ResU.reb_imm_cell_kw h hg hφ hk).1
  · obtain ⟨v, χ, hχ, hψ, -, -⟩ := ResU.reb_src h hg hφ hk
    rw [hψ]; exact CellU.kind_immOf _ _ _ _

/-- `ρ = ρ/ℓ ● ℓ ↦ ρ(ℓ)`.
`[about ours: `[TR]` p. 5's `/` against `●`, at one location]` -/
theorem ResU.del_compS {ρ : ResU Loc Val} {l : Loc} {ψ : CellU Loc Val}
    (hg : ρ.get l = some ψ) : ResU.CompS (ρ.del l) (ResU.single l ψ) ρ := by
  classical
  refine ⟨ResU.Compat.of_disjoint (fun m => ?_), fun m => ?_⟩
  · by_cases hm : m = l
    · exact Or.inl (by rw [hm]; exact ResU.del_get_self ρ l)
    · exact Or.inr (ResU.single_get_ne ψ hm)
  · by_cases hm : m = l
    · subst hm
      show OptComp CellU.CompS ((ρ.del m).get m) ((ResU.single m ψ).get m) (ρ.get m)
      rw [ResU.del_get_self, ResU.single_get_self]
      exact hg
    · show OptComp CellU.CompS ((ρ.del l).get m) ((ResU.single l ψ).get m) (ρ.get m)
      rw [ResU.del_get_ne ρ hm, ResU.single_get_ne ψ hm]
      cases e : ρ.get m with
      | none => rfl
      | some χ => rfl

/-- At `reb_α`'s `own` clause the witness is `≤` the source: the first disjunct
of `[TR]` 6.54's third bullet, *"either `ρ″ ≤ ρ′`, or `ρ′(ℓ) = mut(_, ρ″, _, _)"*.
`[about ours: `[TR]` 6.54's *"`ρ″ ≤ ρ′`"* (p. 18), read off `reb_α`'s own
clauses]` -/
theorem ResU.reb_own_le {α : Life} {ρ ρ' : ResU Loc Val} (h : ResU.Reb α ρ ρ')
    {l : Loc} {ψ : CellU Loc Val} (hg : ρ'.get l = some ψ) {v : Val}
    (hφ : ρ.get l = some (CellU.ownOf v)) : ∃ τ, ResU.CompS ψ.wit τ ρ := by
  have hR : ∀ ψ₁ ψ₂ ψ : CellU Loc Val, CellU.CompS ψ₁ ψ₂ ψ → CellU.CompatS ψ₁ ψ₂ :=
    fun _ _ _ hc => CellU.CompS.compat hc
  obtain ⟨-, π, b, hdom, hbig, hle, hat⟩ := h
  obtain ⟨⟨l', p⟩, hpm, hl⟩ := List.mem_map.mp ((hdom.2 l).mpr ⟨ψ, hg⟩)
  cases hl
  obtain ⟨⟨ζ, hζ⟩, hown, -, -⟩ := hat l' p hpm
  obtain ⟨hstr, he⟩ := hown v hφ
  rw [hg] at he
  obtain rfl := Option.some.inj he
  rw [CellU.wit_immOf]
  obtain ⟨z, hz⟩ :=
    BigComp.mem_factor hR ResU.compLawsS hbig p (List.mem_map.mpr ⟨(l', p), hpm, rfl⟩)
  obtain ⟨z₁, hz₁⟩ :=
    ResU.Comp.factor_trans hR ResU.compLawsS (ResU.del_compS hζ) hz
  obtain ⟨τ₀, hτ₀⟩ := hle
  obtain ⟨z₂, hz₂⟩ := ResU.Comp.factor_trans hR ResU.compLawsS hz₁ hτ₀
  exact ⟨z₂, hz₂⟩

/-- *"Every cell of `ρ` is in `f`"*: at every location `ρ` carries a cell, `f`
carries one over the same value, and over the same witness wherever `ρ`'s cell
is not `own`.
`[about ours: `[TR]` 6.54's closing line (p. 18) at one resource]` -/
def ResU.Under (f ρ : ResU Loc Val) : Prop :=
  ∀ l ζ, ρ.get l = some ζ → ∃ φ, f.get l = some φ ∧ ζ.erase = φ.erase ∧
    (ζ.kind ≠ Kind.own → φ.kind ≠ Kind.own ∧ ζ.wit = φ.wit)

/-- A `○`-factor lies under the composite. -/
theorem ResU.Under.of_factor {X z f : ResU Loc Val} (h : ResU.CompR X z f) :
    ResU.Under f X := by
  intro l ζ hζ
  rcases h.get l with ⟨e₁, -, -⟩ | ⟨χ, e₁, -, e⟩ | ⟨-, e₁, -, -⟩ | ⟨χ₁, χ₂, χ, e₁, -, e, hC⟩
  · rw [hζ] at e₁; exact absurd e₁ (by simp)
  · rw [hζ] at e₁; cases Option.some.inj e₁; exact ⟨ζ, e, rfl, fun hne => ⟨hne, rfl⟩⟩
  · rw [hζ] at e₁; exact absurd e₁ (by simp)
  · rw [hζ] at e₁
    cases Option.some.inj e₁
    exact ⟨χ, e, (CellU.CompR.erase_left hC).symm,
      fun hne => ⟨(CellU.CompR.nonown_left hC hne).1,
                  (CellU.CompR.nonown_left hC hne).2.symm⟩⟩

/-- Lying under `f` survives `○`. -/
theorem ResU.Under.compR {X Y Z f : ResU Loc Val} (h : ResU.CompR X Y Z)
    (hX : ResU.Under f X) (hY : ResU.Under f Y) : ResU.Under f Z := by
  intro l ζ hζ
  rcases h.get l with ⟨-, -, e⟩ | ⟨χ, e₁, -, e⟩ | ⟨χ, -, e₂, e⟩ | ⟨χ₁, χ₂, χ, e₁, e₂, e, hC⟩
  · rw [e] at hζ; exact absurd hζ (by simp)
  · rw [e] at hζ; cases Option.some.inj hζ; exact hX l ζ e₁
  · rw [e] at hζ; cases Option.some.inj hζ; exact hY l ζ e₂
  · rw [e] at hζ
    cases Option.some.inj hζ
    obtain ⟨φ, hφ, he₁, hw₁⟩ := hX l χ₁ e₁
    refine ⟨φ, hφ, (CellU.CompR.erase_left hC).trans he₁, fun hne => ?_⟩
    rcases CellU.CompR.wit_of_ne_own hC hne with ⟨hn₁, hwe⟩ | ⟨hn₂, hwe⟩
    · exact ⟨(hw₁ hn₁).1, hwe.trans (hw₁ hn₁).2⟩
    · obtain ⟨φ', hφ', -, hw₂⟩ := hY l χ₂ e₂
      rw [hφ] at hφ'
      cases Option.some.inj hφ'
      exact ⟨(hw₂ hn₂).1, hwe.trans (hw₂ hn₂).2⟩

/-- Lying under `f` survives `⨀`. -/
theorem ResU.Under.bigComp {σs : List (ResU Loc Val)} {b f : ResU Loc Val} :
    BigComp CellU.CompatR CellU.CompR σs b → (∀ σ ∈ σs, ResU.Under f σ) →
      ResU.Under f b := by
  induction σs generalizing b with
  | nil => intro h _; cases h; intro l ζ hζ; exact absurd hζ (by simp)
  | cons σ σs' ih =>
      intro h hs
      cases h with
      | cons hrest hc =>
          exact ResU.Under.compR hc (hs σ List.mem_cons_self)
            (ih hrest (fun τ hm => hs τ (List.mem_cons_of_mem _ hm)))

/-- `dom(ex(ρ″)_○) ⊆ dom(ex(ρ′)_○)` at cells, as `ResU.Under`.
`[about ours: the domain inclusion of `[TR]` 6.54's closing line, at cells]` -/
theorem ExW.under_le {X ρ' eX eS aS f : ResU Loc Val}
    (hXY : ∀ m ψ, X.get m = some ψ → ψ.kind ≠ Kind.imm → ρ'.get m = some ψ)
    (hX : ExR X eX) (heS : ExR ρ' eS) (haS : AgW ρ' aS)
    (hf : ResU.CompR eS aS f) : ResU.Under f eX := by
  have hR : ∀ ψ₁ ψ₂ ψ : CellU Loc Val, CellU.CompR ψ₁ ψ₂ ψ → CellU.CompatR ψ₁ ψ₂ :=
    fun _ _ ψ hc => ⟨ψ, hc⟩
  cases hX with
  | mk hs hw hb hnm hσ =>
      rename_i nm bb w
      have hnmU : ResU.Under f nm := by
        intro l ζ hζ
        have hfrom : ∀ ζ₁ : CellU Loc Val, X.get l = some ζ₁ → ζ₁.kind ≠ Kind.imm →
            nm.get l = some ζ₁ → ∃ φ, f.get l = some φ ∧ ζ.erase = φ.erase ∧
              (ζ.kind ≠ Kind.own → φ.kind ≠ Kind.own ∧ ζ.wit = φ.wit) := by
          intro ζ₁ hx hne hnml
          rw [hζ] at hnml
          cases Option.some.inj hnml
          obtain ⟨πl, hπ, hπe, hπn⟩ :=
            ResU.witFlat_cell heS haS hf (hXY l ζ hx hne)
          exact ⟨πl, hπ, hπe.symm, fun hno => ⟨(hπn hno).2, (hπn hno).1.symm⟩⟩
        rcases hnm.get l with ⟨-, -, e⟩ | ⟨ζ₁, e₁, -, e⟩ | ⟨ζ₁, -, e₂, e⟩ |
            ⟨ζ₁, ζ₂, ζ₃, e₁, e₂, -, -⟩
        · rw [e] at hζ; exact absurd hζ (by simp)
        · obtain ⟨hx, hk⟩ := ResU.restrict_eq_some.mp e₁
          exact hfrom ζ₁ hx (by rw [hk]; exact fun c => Kind.noConfusion c) e
        · obtain ⟨hx, hk⟩ := ResU.restrict_eq_some.mp e₂
          exact hfrom ζ₁ hx (by rw [hk]; exact fun c => Kind.noConfusion c) e
        · obtain ⟨hx₁, hk₁⟩ := ResU.restrict_eq_some.mp e₁
          obtain ⟨hx₂, hk₂⟩ := ResU.restrict_eq_some.mp e₂
          rw [hx₁] at hx₂
          cases Option.some.inj hx₂
          exact absurd (hk₁.symm.trans hk₂) (by simp)
      have hbU : ResU.Under f bb := by
        refine ResU.Under.bigComp hb (fun σ hmem => ?_)
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hmem
        obtain ⟨ψq, hψq, hexq⟩ := ExWits.mem hw q hq
        obtain ⟨ψ', h', hk'⟩ := (hs.2 q.1).mp (List.mem_map.mpr ⟨q, hq, rfl⟩)
        rw [hψq] at h'
        cases Option.some.inj h'
        have hne : ψq.kind ≠ Kind.imm := by rw [hk']; exact fun c => Kind.noConfusion c
        obtain ⟨ev, z, hev, hz⟩ :=
          ExW.wit_le hR ResU.compLawsR heS (hXY q.1 ψq hψq hne) hk'
        obtain rfl : ev = q.2 := ExW.functional hR ResU.compLawsR hev hexq
        obtain ⟨z', hz'⟩ := ResU.Comp.factor_trans hR ResU.compLawsR hz hf
        exact ResU.Under.of_factor hz'
      exact ResU.Under.compR hσ hnmU hbU

/-- `[TR]` Lemma 6.54 at its closing line: every cell of `ag(ρ)` sits in
`⦇ρ′⦈_○` at its own location over the same value, and, where it is not `own`,
over the same witness, except where the source carries an `own` cell (`reb_α`'s
`own` clause).
`[about ours: `[TR]` 6.54's closing line (p. 18) at cells, as its first bullet's
*"every immutable borrow in `ρ` is in `⦇ρ′⦈_○`"* states it]` -/
theorem ResU.ag_cell_of_reb {β : Life} {ρ' ρ A f : ResU Loc Val}
    (hreb : ResU.Reb β ρ' ρ) (hagρ : AgW ρ A) (hfl : ResU.FlatR ρ' f)
    {l : Loc} {ψ : CellU Loc Val} (hg : A.get l = some ψ) :
    ∃ φ, f.get l = some φ ∧ ψ.erase = φ.erase ∧
      (ψ.kind ≠ Kind.own →
        (φ.kind ≠ Kind.own ∧ ψ.wit = φ.wit) ∨
        (∃ (v : Val) (χ : CellU Loc Val), ρ'.get l = some (CellU.ownOf v) ∧
          ρ.get l = some χ ∧ ψ.wit = χ.wit)) := by
  have hR : ∀ ψ₁ ψ₂ ψ : CellU Loc Val, CellU.CompR ψ₁ ψ₂ ψ → CellU.CompatR ψ₁ ψ₂ :=
    fun _ _ ψ hc => ⟨ψ, hc⟩
  obtain ⟨aS, eS, hagS, hexS, hcS⟩ := hfl
  have hrho : ∀ (m : Loc) (χ : CellU Loc Val), ρ.get m = some χ →
      ∃ φ, f.get m = some φ ∧ χ.erase = φ.erase ∧
        ((φ.kind ≠ Kind.own ∧ χ.wit = φ.wit) ∨
          ∃ v : Val, ρ'.get m = some (CellU.ownOf v)) := by
    intro m χ hχ
    obtain ⟨φ', hφ'⟩ := ResU.reb_dom_subset hreb hχ
    obtain ⟨πl, hπ, hπe, hπn⟩ :=
      ResU.witFlat_cell hexS hagS (ResU.CompR.comm hcS) hφ'
    by_cases hk : φ'.kind = Kind.imm
    · obtain ⟨-, hke, hkw, -⟩ := ResU.reb_imm_cell_kw hreb hχ hφ' hk
      have hno : φ'.kind ≠ Kind.own := by rw [hk]; exact fun c => Kind.noConfusion c
      exact ⟨πl, hπ, hke.trans hπe.symm, Or.inl ⟨(hπn hno).2, hkw.trans (hπn hno).1.symm⟩⟩
    · obtain ⟨vv, χw, hχs, hψeq, hvv, hor⟩ := ResU.reb_src hreb hχ hφ' hk
      by_cases hown : φ'.kind = Kind.own
      · refine ⟨πl, hπ, ?_, Or.inr ⟨φ'.erase, hφ'.trans (congrArg some
          (CellU.eq_ownOf_of_kind hown))⟩⟩
        rw [hψeq, CellU.erase_immOf]
        exact (hπe.trans hvv).symm
      · have hwm' : φ'.wit = χw := hor.resolve_left hown
        refine ⟨πl, hπ, by rw [hψeq, CellU.erase_immOf]; exact (hπe.trans hvv).symm,
          Or.inl ⟨(hπn hown).2, ?_⟩⟩
        rw [hψeq, CellU.wit_immOf, ← hwm', (hπn hown).1]
  cases hagρ with
  | mk hsm hsi hwm hwi hbm hbi ha hσ =>
      rename_i aa bm bi wm wi
      have hwmnil : wm = [] := by
        have h0 : wm.map Prod.fst = [] :=
          ResU.sites_nil_of_none hsm (fun m χ hχ => by
            rw [ResU.reb_imm_image hreb hχ]; exact fun c => Kind.noConfusion c)
        cases wm with
        | nil => rfl
        | cons q t => simp at h0
      subst hwmnil
      obtain rfl : bm = (PMap.empty : ResU Loc Val) := BigComp.nil_inv hbm
      -- The `imm` family lies under `⦇ρ′⦈_○` outright.
      have hbiU : ResU.Under f bi := by
        refine ResU.Under.bigComp hbi (fun σ hmem => ?_)
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hmem
        obtain ⟨χq, ev, avv, hχq, hexq, hagq, hcq⟩ := AgWitsI.mem hwi q hq
        obtain ⟨φq, hφq⟩ := ResU.reb_dom_subset hreb hχq
        by_cases hk : φq.kind = Kind.imm
        · obtain ⟨-, -, hkw, -⟩ := ResU.reb_imm_cell_kw hreb hχq hφq hk
          rw [hkw] at hexq hagq
          obtain ⟨ev', av', p', z', hex', hag', hc', hz'⟩ := AgW.imm_wit_le hagS hφq hk
          obtain rfl : ev' = ev := ExR.functional hex' hexq
          obtain rfl : av' = avv := AgW.functional hag' hagq
          obtain rfl : p' = q.2 := ResU.CompR.functional hc' hcq
          obtain ⟨z'', hz''⟩ := ResU.Comp.factor_trans hR ResU.compLawsR hz' hcS
          exact ResU.Under.of_factor hz''
        · obtain ⟨vv, χw, hχs, hψeq, hvv, hor⟩ := ResU.reb_src hreb hχq hφq hk
          have hwq : χq.wit = χw := by rw [hψeq, CellU.wit_immOf]
          rw [hwq] at hexq hagq
          by_cases hown : φq.kind = Kind.own
          · have hφo : ρ'.get q.1 = some (CellU.ownOf φq.erase) :=
              hφq.trans (congrArg some (CellU.eq_ownOf_of_kind hown))
            obtain ⟨τ₀, hτ₀⟩ := ResU.reb_own_le hreb hχq hφo
            rw [hwq] at hτ₀
            obtain ⟨σ₁, σ₂, hσ₁, -, hc₁₂⟩ := (AgW.split hτ₀).mp hagS
            obtain rfl : σ₁ = avv := AgW.functional hσ₁ hagq
            obtain ⟨zA, hzA⟩ := ResU.Comp.factor_trans hR ResU.compLawsR hc₁₂ hcS
            exact ResU.Under.compR hcq
              (ExW.under_le (fun m ζ hx hne =>
                  (ResU.CompS.get_left_of_ne_imm hτ₀ hx hne).2)
                hexq hexS hagS (ResU.CompR.comm hcS))
              (ResU.Under.of_factor hzA)
          · have hkm : φq.kind = Kind.mut := by
              cases hkk : φq.kind with
              | own => exact absurd hkk hown
              | imm => exact absurd hkk hk
              | «mut» => rfl
            have hwm' : φq.wit = χw := hor.resolve_left hown
            obtain ⟨ev₀, z₀, hev₀, hz₀⟩ := ExW.wit_le hR ResU.compLawsR hexS hφq hkm
            rw [hwm'] at hev₀
            obtain rfl : ev₀ = ev := ExR.functional hev₀ hexq
            obtain ⟨zE, hzE⟩ :=
              ResU.Comp.factor_trans hR ResU.compLawsR hz₀ (ResU.CompR.comm hcS)
            obtain ⟨av₀, z₁, hav₀, hz₁⟩ := AgW.mut_wit_le hagS hφq hkm
            rw [hwm'] at hav₀
            obtain rfl : av₀ = avv := AgW.functional hav₀ hagq
            obtain ⟨zA, hzA⟩ := ResU.Comp.factor_trans hR ResU.compLawsR hz₁ hcS
            exact ResU.Under.compR hcq (ResU.Under.of_factor hzE)
              (ResU.Under.of_factor hzA)
      -- `aa = ρ|imm`, and the image is all `imm`.
      have haaρ : ∀ (m : Loc) (χ : CellU Loc Val), aa.get m = some χ →
          ρ.get m = some χ := by
        intro m χ hχ
        rcases ha.get m with ⟨-, -, e⟩ | ⟨ζ, e₁, -, e⟩ | ⟨ζ, -, e₂, -⟩ |
            ⟨ζ₁, ζ₂, ζ₃, e₁, e₂, -, -⟩
        · rw [e] at hχ; exact absurd hχ (by simp)
        · rw [show χ = ζ from Option.some.inj (hχ.symm.trans e)]
          exact (ResU.restrict_eq_some.mp e₁).1
        · exact absurd e₂ (by simp)
        · exact absurd e₂ (by simp)
      rcases hσ.get l with ⟨-, -, e⟩ | ⟨ζ, e₁, -, e⟩ | ⟨ζ, -, e₂, e⟩ |
          ⟨ζ₁, ζ₂, ζ₃, e₁, e₂, e, hC⟩
      · rw [e] at hg; exact absurd hg (by simp)
      · rw [show ψ = ζ from Option.some.inj (hg.symm.trans e)]
        obtain ⟨φ, hφ, he, hw⟩ := hrho l ζ (haaρ l ζ e₁)
        refine ⟨φ, hφ, he, fun hne => ?_⟩
        rcases hw with h | ⟨vv, hown⟩
        · exact Or.inl h
        · exact Or.inr ⟨vv, ζ, hown, haaρ l ζ e₁, rfl⟩
      · rw [show ψ = ζ from Option.some.inj (hg.symm.trans e)]
        obtain ⟨φ, hφ, he, hw⟩ := hbiU l ζ e₂
        exact ⟨φ, hφ, he, fun hne => Or.inl (hw hne)⟩
      · rw [show ψ = ζ₃ from Option.some.inj (hg.symm.trans e)]
        obtain ⟨φ, hφ, he, hw⟩ := hrho l ζ₁ (haaρ l ζ₁ e₁)
        refine ⟨φ, hφ, (CellU.CompR.erase_left hC).trans he, fun hne => ?_⟩
        rcases CellU.CompR.wit_of_ne_own hC hne with ⟨hn₁, hwe⟩ | ⟨hn₂, hwe⟩
        · rcases hw with ⟨hφn, hwq⟩ | ⟨vv, hown⟩
          · exact Or.inl ⟨hφn, hwe.trans hwq⟩
          · exact Or.inr ⟨vv, ζ₁, hown, haaρ l ζ₁ e₁, hwe⟩
        · obtain ⟨φ', hφ', -, hw₂⟩ := hbiU l ζ₂ e₂
          rw [hφ] at hφ'
          cases Option.some.inj hφ'
          exact Or.inl ⟨(hw₂ hn₂).1, hwe.trans (hw₂ hn₂).2⟩

/-- `[TR]` Lemma 6.54's displayed conclusion, against a named `⦇ρ′⦈_○`.
`[about ours: `[TR]` 6.54's displayed conclusion with `⦇ρ′⦈_○` and `ag(ρ)` named
by their graphs (G4)]` -/
theorem ResU.ag_dom_of_reb {β : Life} {ρ' ρ A f : ResU Loc Val}
    (hreb : ResU.Reb β ρ' ρ) (hagρ : AgW ρ A) (hfl : ResU.FlatR ρ' f)
    {l : Loc} {ψ : CellU Loc Val} (hg : A.get l = some ψ) :
    ∃ φ, f.get l = some φ := by
  obtain ⟨φ, hφ, -, -⟩ := ResU.ag_cell_of_reb hreb hagρ hfl hg
  exact ⟨φ, hφ⟩

/-- `✓(ℓ ↦ imm(α, ρ′, v))` gives `⦇ρ′⦈_○`.
`[about ours: the presupposition of `[TR]` 6.54's conclusion, read off its
printed hypothesis]` -/
theorem ResU.flatR_of_valid_single_imm {l : Loc} {s : LSet} {v : Val}
    {χ : ResU Loc Val} {hs : χ.InStratum s.join}
    (h : ResU.Valid (ResU.single l (CellU.immOf s v χ hs))) : ∃ f, ResU.FlatR χ f := by
  obtain ⟨σ, e, a, hex, hag, hcs⟩ := h
  obtain ⟨ev, av, p, hev, hav, hp, -⟩ := AgW.single_imm_inv hag
  exact ⟨p, av, ev, hav, hev, ResU.CompR.comm hp⟩

/-- `ex(ρ)_◐ = ∅` when `ρ` carries `imm` cells only: the *"noting
`dom(ρ|own,mut) = ∅`"* of 6.55's second display.
`[about ours: the walk at an argument with no own or mut cell]` -/
theorem ExW.empty_of_all_imm {R : CellU Loc Val → CellU Loc Val → Prop}
    {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop} {ρ : ResU Loc Val}
    (h : ∀ l ψ, ρ.get l = some ψ → ψ.kind = Kind.imm) :
    ExW R C ρ PMap.empty := by
  have hres : ∀ k, k ≠ Kind.imm → ρ.restrict k = (PMap.empty : ResU Loc Val) := by
    intro k hk
    refine PMap.ext fun l => ?_
    cases e : ρ.get l with
    | none => rw [ResU.restrict_get_none e]; rfl
    | some ψ =>
        rw [ResU.restrict_get_ne e (by rw [h l ψ e]; exact fun c => hk c.symm)]
        rfl
  refine ExW.mk (w := []) (b := PMap.empty) (nm := PMap.empty)
    ⟨List.nodup_nil, fun l => ⟨fun hm => absurd hm (by simp), ?_⟩⟩
    ExWits.nil BigComp.nil ?_ (ResU.comp_empty_right _)
  · rintro ⟨ψ, hg, hkk⟩
    exact absurd (hkk.symm.trans (h l ψ hg)) (by simp)
  · rw [hres Kind.own (by simp), hres Kind.mut (by simp)]
    exact ResU.comp_empty_right _

/-- 6.55's first display, and 6.30 with 6.36 on it.  From
`ρ_f # ℓ ↦ imm(α, ρ′, v)`: `⦇ρ_f ● ρ_i⦈ = ex(ρ_f)● ● (ag(ρ_f) ○ ρ_i ○ ⦇ρ′⦈_○)`,
whence `ex(ρ_f)● ▸◂ ag(ρ_f)`, `ex(ρ_f)● ▸◂ ⦇ρ′⦈_○` and `ag(ρ_f) ▷◁ ⦇ρ′⦈_○` (the
first bullet's *"We have `ag(ρ_f) ▷◁ ⦇ρ′⦈_○`"*).
`[about ours: `[TR]` 6.55's first display (p. 18), objects as graphs]` -/
theorem ResU.frame_flat_facts {ρf ρ' ρc : ResU Loc Val} {l₀ : Loc} {s : LSet}
    {v : Val} {hs : ρ'.InStratum s.join}
    (hcomp : ResU.CompS ρf (ResU.single l₀ (CellU.immOf s v ρ' hs)) ρc)
    (hval : ρc.Valid) :
    ∃ e₁ a₁ f, ExS ρf e₁ ∧ AgW ρf a₁ ∧ ResU.FlatR ρ' f ∧
      ResU.CompatS e₁ a₁ ∧ ResU.CompatS e₁ f ∧ ResU.CompatR a₁ f := by
  obtain ⟨σ, e, a, hex, hag, hcs⟩ := hval
  obtain ⟨e₁, e₂, hef, hei, he12⟩ := (ExS.split hcomp).mp hex
  obtain ⟨a₁, a₂, haf, hai, ha12⟩ := (AgW.split hcomp).mp hag
  obtain ⟨ev, av, p, hev, hav, hp, hpa⟩ := AgW.single_imm_inv hai
  -- `✓ρ_f` — 6.10 — and with it `ex(ρ_f)● ▸◂ ag(ρ_f)`.
  obtain ⟨σf, ef, af, hef', haf', hcf⟩ := (ResU.Valid.split hcomp ⟨σ, e, a, hex, hag, hcs⟩).1
  rw [ExS.functional hef' hef, AgW.functional haf' haf] at hcf
  -- 6.36, then 6.30 twice: `ex(ρ_f)● ▸◂ ag(ρ_i)`, then `ex(ρ_f)● ▸◂ ⦇ρ′⦈_○`.
  have himm : e₁.restrict Kind.imm = (PMap.empty : ResU Loc Val) :=
    (ResU.restrict_imm_empty_iff e₁).mpr (ExS.immFree hef)
  have h1 : ResU.CompatS e₁ a :=
    (ResU.CompatS.of_compS_left_immFree (ExS.immFree hex) he12 hcs.1).1
  have h2 : ResU.CompatS e₁ a₂ := (ResU.CompatS.of_compR_left himm ha12 h1).2
  have h3 : ResU.CompatS e₁ p := (ResU.CompatS.of_compR_left himm hpa h2).2
  -- 6.3 at `○`: `ag(ρ_f) ○ (⦇ρ′⦈_○ ○ ρ_i)` regrouped as `(ag(ρ_f) ○ ⦇ρ′⦈_○) ○ ρ_i`.
  obtain ⟨υ, hυ, -⟩ :=
    (ResU.CompR.assoc a₁ p (ResU.single l₀ (CellU.immOf s v ρ' hs)) a).mp
      ⟨a₂, ResU.CompR.comm hpa, ha12⟩
  exact ⟨e₁, a₁, p, hef, haf, ⟨av, ev, hav, hev, ResU.CompR.comm hp⟩,
    hcf.1, h3, hυ.1⟩

/-- 6.55's second bullet: `ex(ρ_f)● ▸◂ ag(ρ)`.

*"Since `ex(ρ_f)● ▸◂ ⦇ρ′⦈_○`, and `ex(ρ_f)●|imm = ∅`, we have that
`dom(ex(ρ_f)●) ∩ dom(⦇ρ′⦈_○) = ∅`.  By unfolding the definition of `▸◂`, it
suffices to show `dom(ex(ρ_f)●) ∩ dom(ag(ρ)) = ∅`, which is implied by
`dom(ag(ρ)) ⊆ dom(⦇ρ′⦈_○)`."*
`[about ours: `[TR]` 6.55's second bullet (p. 18), with `dom` written
pointwise]` -/
theorem ResU.frame_compatS_ag {β : Life} {ρ' ρ ρf e₁ f A : ResU Loc Val}
    (hreb : ResU.Reb β ρ' ρ) (hex : ExS ρf e₁) (hfl : ResU.FlatR ρ' f)
    (hcompat : ResU.CompatS e₁ f) (hagρ : AgW ρ A) : ResU.CompatS e₁ A := by
  refine ResU.Compat.of_disjoint (fun l => ?_)
  rcases ResU.CompatS.disjoint_of_immFree (ExS.immFree hex) hcompat l with h | h
  · exact Or.inl h
  · refine Or.inr ?_
    cases hA : A.get l with
    | none => rfl
    | some ψ =>
        obtain ⟨φ, hφ⟩ := ResU.ag_dom_of_reb hreb hagρ hfl hA
        rw [h] at hφ
        exact absurd hφ (by simp)

/-- 6.55's first bullet: `ag(ρ_f) ▷◁ ag(ρ)`.

*"For any location `ℓ ∈ dom(ag(ρ_f)) ∩ dom(ag(ρ))`, it suffices to show
`ag(ρ_f)(ℓ) ▷◁ ag(ρ)(ℓ)`.  We have `ag(ρ_f) ▷◁ ⦇ρ′⦈_○`.  This follows by
unfolding reb, and noting `ρ` and `ρ′` differ only by potentially changing from
own or mut to imm, but witnesses and values always stay the same."*
At a location where `ρ′` has an `own` cell the last sentence is `EscrowAgree`.
`[about ours: `[TR]` 6.55's first bullet (p. 18), with `ag(ρ_f)`, `ag(ρ)` and
`⦇ρ′⦈_○` named by their graphs]` -/
theorem ResU.frame_compatR_ag {β : Life} {ρ' ρ A aF f : ResU Loc Val}
    (hreb : ResU.Reb β ρ' ρ) (hagρ : AgW ρ A) (hfl : ResU.FlatR ρ' f)
    (hAF : ResU.CompatR aF f) (hesc : EscrowAgree ρ' ρ aF) :
    ResU.CompatR aF A := by
  intro l ψ₁ ψ₂ h₁ h₂
  obtain ⟨φ, hφ, he, hw⟩ := ResU.ag_cell_of_reb hreb hagρ hfl h₂
  obtain ⟨he₁, hw₁⟩ := CellU.compatR_iff.mp (hAF l ψ₁ φ h₁ hφ)
  refine CellU.compatR_iff.mpr ⟨he₁.trans he.symm, fun k₁ k₂ => ?_⟩
  rcases hw k₂ with ⟨hφn, hwe⟩ | ⟨vv, χ, hown, hρ, hwe⟩
  · exact (hw₁ k₁ hφn).trans hwe.symm
  · have hχn : χ.kind ≠ Kind.own := by
      rw [ResU.reb_imm_image hreb hρ]; exact fun c => Kind.noConfusion c
    exact (hesc l vv χ ψ₁ hown hρ h₁ hχn k₁).trans hwe.symm

/-- `●` keeps the left operand's value where that operand is defined. -/
theorem ResU.CompS.erase_left {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ)
    {l : Loc} {ψ₁ ψ : CellU Loc Val} (e₁ : ρ₁.get l = some ψ₁)
    (e : ρ.get l = some ψ) : ψ.erase = ψ₁.erase := by
  rcases ResU.Comp.get h l with ⟨f₁, -, -⟩ | ⟨χ, f₁, -, f⟩ | ⟨χ, f₁, -, -⟩ |
      ⟨χ₁, χ₂, χ, f₁, -, f, hC⟩
  · rw [e₁] at f₁; exact absurd f₁ (by simp)
  · rw [e₁] at f₁
    obtain rfl := Option.some.inj f₁
    rw [e] at f
    obtain rfl := Option.some.inj f
    rfl
  · rw [e₁] at f₁; exact absurd f₁ (by simp)
  · rw [e₁] at f₁
    obtain rfl := Option.some.inj f₁
    rw [e] at f
    obtain rfl := Option.some.inj f
    exact (CellU.CompS.erase hC).1

/-- `▸◂` passes to `●`-factors.
`[about ours: the step `[TR]` 6.61's proof takes when it composes `⨀π₁` with
`⨀π₂` under `ρ₁ ▸◂ ρ₂`]` -/
theorem ResU.CompatS.of_factors {b₁ z₁ ρ₁ b₂ z₂ ρ₂ : ResU Loc Val}
    (h₁ : ResU.CompS b₁ z₁ ρ₁) (h₂ : ResU.CompS b₂ z₂ ρ₂)
    (h : ResU.CompatS ρ₁ ρ₂) : ResU.CompatS b₁ b₂ := by
  intro l ζ₁ ζ₂ e₁ e₂
  obtain ⟨φ₁, hφ₁⟩ := h₁.dom_left e₁
  obtain ⟨φ₂, hφ₂⟩ := h₂.dom_left e₂
  obtain ⟨k₁, w₁⟩ := ResU.CompS.kind_wit_left h₁ e₁ hφ₁
  obtain ⟨k₂, w₂⟩ := ResU.CompS.kind_wit_left h₂ e₂ hφ₂
  obtain ⟨m₁, m₂, hv, hw⟩ := CellU.compatS_iff.mp (h l φ₁ φ₂ hφ₁ hφ₂)
  refine CellU.compatS_of (k₁.symm.trans m₁) (k₂.symm.trans m₂) ?_ ?_
  · rw [← ResU.CompS.erase_left h₁ e₁ hφ₁, ← ResU.CompS.erase_left h₂ e₂ hφ₂, hv]
  · rw [← w₁, ← w₂, hw]

/-- `Res_α` is closed under `●`. -/
theorem ResU.CompS.inStratum {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ)
    {α : Life} (h₁ : ρ₁.InStratum α) (h₂ : ρ₂.InStratum α) : ρ.InStratum α := by
  intro l ψ e
  rcases ResU.Comp.get h l with ⟨-, -, f⟩ | ⟨χ, f₁, -, f⟩ | ⟨χ, -, f₂, f⟩ |
      ⟨χ₁, χ₂, χ, f₁, f₂, f, hC⟩
  · rw [f] at e; exact absurd e (by simp)
  · rw [f] at e; cases Option.some.inj e; exact h₁ l _ f₁
  · rw [f] at e; cases Option.some.inj e; exact h₂ l _ f₂
  · rw [f] at e
    cases Option.some.inj e
    exact (CellU.CompS.inStratum hC α).mpr ⟨h₁ l _ f₁, h₂ l _ f₂⟩

/-- A sub-list of a `⨀` folds, to a factor of it.
`[about ours: `[TR]` 6.2 and 6.3 along the fold, at a sub-list]` -/
theorem BigComp.sublist_factor {R : CellU Loc Val → CellU Loc Val → Prop}
    {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop}
    (hR : ∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → R ψ₁ ψ₂) (hC : ResU.CompLaws C) :
    ∀ {L L' : List (ResU Loc Val)} {b : ResU Loc Val}, L'.Sublist L →
      BigComp R C L b → ∃ b' z, BigComp R C L' b' ∧ ResU.Comp R C b' z b := by
  intro L
  induction L with
  | nil =>
      intro L' b hsub h
      cases h
      cases hsub
      exact ⟨PMap.empty, PMap.empty, BigComp.nil, ResU.comp_empty_right _⟩
  | cons x L₀ ih =>
      intro L' b hsub h
      cases h with
      | cons hrest hcx =>
          cases hsub with
          | cons _ hsub' =>
              obtain ⟨b', z, hb', hz⟩ := ih hsub' hrest
              obtain ⟨z', hz'⟩ :=
                ResU.Comp.factor_trans hR hC hz (ResU.Comp.comm_of_laws hR hC hcx)
              exact ⟨b', z', hb', hz'⟩
          | cons_cons _ hsub' =>
              obtain ⟨b'', z, hb'', hz⟩ := ih hsub' hrest
              obtain ⟨y, hy, hyz⟩ :=
                (ResU.Comp.assoc hR hC.assoc x b'' z b).mp ⟨_, hz, hcx⟩
              exact ⟨y, z, BigComp.cons hb'' hy, hyz⟩

/-- `[TR]` 6.61's proof: *"Any overlapping locations of `ρ′₁` and `ρ′₂` are in
`(ρ₁ ● ρ₂)|imm`."*
`[about ours: the step `[TR]` 6.61's proof takes at an overlap]` -/
theorem ResU.reb_overlap {α : Life} {ρ₁ ρ₂ ρ'₁ ρ'₂ : ResU Loc Val}
    (hreb₁ : ResU.Reb α ρ₁ ρ'₁) (hreb₂ : ResU.Reb α ρ₂ ρ'₂)
    (hcompat : ResU.CompatS ρ₁ ρ₂) {l : Loc} {ψ₁ ψ₂ : CellU Loc Val}
    (h₁ : ρ'₁.get l = some ψ₁) (h₂ : ρ'₂.get l = some ψ₂) :
    CellU.CompatS ψ₁ ψ₂ := by
  obtain ⟨φ₁, hφ₁⟩ := ResU.reb_dom_subset hreb₁ h₁
  obtain ⟨φ₂, hφ₂⟩ := ResU.reb_dom_subset hreb₂ h₂
  have hcc := hcompat l φ₁ φ₂ hφ₁ hφ₂
  obtain ⟨k₁, k₂⟩ := CellU.CompatS.kinds hcc
  obtain ⟨-, -, he, hw⟩ := CellU.compatS_iff.mp hcc
  obtain ⟨a₁, b₁, c₁, -⟩ := ResU.reb_imm_cell_kw hreb₁ h₁ hφ₁ k₁
  obtain ⟨a₂, b₂, c₂, -⟩ := ResU.reb_imm_cell_kw hreb₂ h₂ hφ₂ k₂
  exact CellU.compatS_iff.mpr ⟨a₁, a₂, b₁.trans (he.trans b₂.symm), c₁.trans (hw.trans c₂.symm)⟩

/-- One operand's image at an `imm` location of the composite.  If
`ρ₁ ● ρ₂ = ρ` carries `imm(s̄, v, χ)` at `ℓ` and `ρ′₁ ∈ reb_α(ρ₁)` carries `ψ₁`
there, then `ψ₁` is `imm(t̄, v, χ)` for some `t̄ ⊆ s̄`. -/
theorem ResU.six61_side {α : Life} {ρ₁ ρ₂ ρ ρ'₁ : ResU Loc Val}
    (hreb₁ : ResU.Reb α ρ₁ ρ'₁) (hc : ResU.CompS ρ₁ ρ₂ ρ) {l : Loc}
    {s : LSet} {v : Val} {χ : ResU Loc Val} {h : χ.InStratum s.join}
    (he : ρ.get l = some (CellU.immOf s v χ h)) {ψ₁ : CellU Loc Val}
    (hψ₁ : ρ'₁.get l = some ψ₁) :
    ∃ (t : LSet) (ht : χ.InStratum t.join), (∀ x, t.mem x → s.mem x) ∧
      ψ₁ = CellU.immOf t v χ ht := by
  obtain ⟨φ₁, hφ₁⟩ := ResU.reb_dom_subset hreb₁ hψ₁
  rcases ResU.Comp.get hc l with ⟨f₁, -, -⟩ | ⟨φ, f₁, -, f⟩ | ⟨φ, f₁, -, -⟩ |
      ⟨φa, φb, φ, f₁, -, f, hC⟩
  · rw [hφ₁] at f₁; exact absurd f₁ (by simp)
  · rw [he] at f
    rw [hφ₁] at f₁
    obtain rfl := Option.some.inj f₁
    obtain rfl := Option.some.inj f
    exact ResU.reb_imm_cell_sub hreb₁ hψ₁ hφ₁
  · rw [hφ₁] at f₁; exact absurd f₁ (by simp)
  · rw [hφ₁] at f₁
    obtain rfl := Option.some.inj f₁
    rw [he] at f
    obtain rfl := Option.some.inj f
    obtain ⟨s₁, s₂, w, ζ, h₁, h₂, h₃, e₁, -, e₃⟩ := hC
    obtain ⟨rfl, rfl, rfl⟩ := CellU.immOf_inj e₃
    rw [e₁] at hφ₁
    obtain ⟨t, ht, hts, e⟩ := ResU.reb_imm_cell_sub hreb₁ hψ₁ hφ₁
    exact ⟨t, ht, fun x hx => Or.inl (hts x hx), e⟩

/-- The step `[TR]` 6.61's proof takes at an `imm` location of the composite:
`(ρ′₁ ● ρ′₂)(ℓ)` is `imm` over a subset of `(ρ₁ ● ρ₂)(ℓ)`'s lifetime set, at its
value and witness, at every location the image covers.
`[about ours: "`(ρ′₁ ● ρ′₂)(ℓ) = (ρ₁ ● ρ₂)(ℓ)`" read at `reb_α`'s `imm` clause]` -/
theorem ResU.six61_imm_at {α : Life} {ρ₁ ρ₂ ρ ρ'₁ ρ'₂ ρ' : ResU Loc Val}
    (hreb₁ : ResU.Reb α ρ₁ ρ'₁) (hreb₂ : ResU.Reb α ρ₂ ρ'₂)
    (hc : ResU.CompS ρ₁ ρ₂ ρ) (hρ' : ResU.CompS ρ'₁ ρ'₂ ρ') {l : Loc}
    {s : LSet} {v : Val} {χ : ResU Loc Val} {h : χ.InStratum s.join}
    (he : ρ.get l = some (CellU.immOf s v χ h)) (hin : ∃ ψ, ρ'.get l = some ψ) :
    ∃ (t : LSet) (ht : χ.InStratum t.join), (∀ x, t.mem x → s.mem x) ∧
      ρ'.get l = some (CellU.immOf t v χ ht) := by
  obtain ⟨ψ, hψ⟩ := hin
  rcases ResU.Comp.get hρ' l with ⟨-, -, f⟩ | ⟨ψ₁, g₁, -, f⟩ | ⟨ψ₂, -, g₂, f⟩ |
      ⟨ψ₁, ψ₂, ψ', g₁, g₂, f, hC⟩
  · rw [hψ] at f; exact absurd f (by simp)
  · obtain ⟨t, ht, hts, rfl⟩ := ResU.six61_side hreb₁ hc he g₁
    exact ⟨t, ht, hts, f⟩
  · obtain ⟨t, ht, hts, rfl⟩ := ResU.six61_side hreb₂ (ResU.CompS.comm hc) he g₂
    exact ⟨t, ht, hts, f⟩
  · obtain ⟨t₁, ht₁, hts₁, rfl⟩ := ResU.six61_side hreb₁ hc he g₁
    obtain ⟨t₂, ht₂, hts₂, rfl⟩ := ResU.six61_side hreb₂ (ResU.CompS.comm hc) he g₂
    obtain ⟨u₁, u₂, w, ζ, k₁, k₂, k₃, e₁, e₂, rfl⟩ := hC
    obtain ⟨rfl, rfl, rfl⟩ := CellU.immOf_inj e₁
    obtain ⟨rfl, -, -⟩ := CellU.immOf_inj e₂
    exact ⟨t₁ ∪ t₂, k₃, fun x hx => hx.elim (hts₁ x) (hts₂ x), f⟩

end BoCa.Fig16

end
