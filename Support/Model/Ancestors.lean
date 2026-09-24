import Paper.S5_Model.Definitions
import Paper.S6_1_StandardLemmas.Lemmas
import Support.Model.Algebra
import Support.Model.AlgebraInstances
import Support.Model.CellFacts
import Support.Model.Cells
import Support.Model.Composition
import Support.Model.FlatteningCells
import Support.Model.Prelude
import Support.Model.RelaxedWalks
import Support.Model.Update
import Support.Model.WalkSplitting
import Support.Model.Walks

/-!
# Support — Model — Ancestors

`[about ours]`.  The immutable ancestor of a cell of the aliasable walk: every cell of `ag(ρ)` sits beneath an `imm` cell, carried across `↭` — the step of Lemma 6.48's printed proof that 6.59 reaches for.
-/

noncomputable section

namespace BoCa.Fig16
variable {Loc Val : Type}

/-- A cell of kind `imm` is `imm(ᾱ, v, ρ)` at its own value and witness. -/
theorem CellU.imm_eta {ψ : CellU Loc Val} (h : ψ.kind = Kind.imm) :
    ∃ (s : LSet) (hs : ψ.wit.InStratum s.join),
      ψ = CellU.immOf s ψ.erase ψ.wit hs := by
  rcases CellU.rep ψ with ⟨v, rfl⟩ | ⟨s, v, ρ, hs, rfl⟩ | ⟨b, v, ρ, hs, P, hw, rfl⟩
  · exact absurd h (by simp)
  · exact ⟨s, by simpa using hs, by simp⟩
  · exact absurd h (by simp)

/-- `ex(χ)_○ ○ ag(χ)` is a factor of `ag(ρ)` wherever `ρ(ℓ) = imm(_, _, χ)`. -/
theorem AgW.imm_wit_le {ρ σ : ResU Loc Val} (h : AgW ρ σ) {l : Loc}
    {ψ : CellU Loc Val} (e : ρ.get l = some ψ) (hk : ψ.kind = Kind.imm) :
    ∃ ev av p z, ExR ψ.wit ev ∧ AgW ψ.wit av ∧ ResU.CompR ev av p ∧
      ResU.CompR p z σ := by
  have hR : ∀ ψ₁ ψ₂ ψ : CellU Loc Val, CellU.CompR ψ₁ ψ₂ ψ → CellU.CompatR ψ₁ ψ₂ :=
    fun _ _ ψ hc => ⟨ψ, hc⟩
  cases h with
  | mk hsm hsi hwm hwi hbm hbi ha hσ =>
      obtain ⟨q, hq, hq₁⟩ := List.mem_map.mp ((hsi.2 l).mpr ⟨ψ, e, hk⟩)
      obtain ⟨χ, ev, av, hχ, hex, hag, hc⟩ := AgWitsI.mem hwi q hq
      rw [hq₁, e] at hχ
      cases Option.some.inj hχ
      obtain ⟨z, hz⟩ :=
        BigComp.mem_factor hR ResU.compLawsR hbi q.2 (List.mem_map.mpr ⟨q, hq, rfl⟩)
      obtain ⟨z', hz'⟩ :=
        ResU.Comp.factor_trans hR ResU.compLawsR hz
          (ResU.Comp.comm_of_laws hR ResU.compLawsR hσ)
      exact ⟨ev, av, q.2, z', hex, hag, hc, hz'⟩

/-- If a `○` composite is `imm(ᾱ, v, χ)`, one operand is an `imm` cell over the
same value and witness.
`[about ours: `[TR]` p. 5's `○` read backwards at an `imm` result]` -/
theorem CellU.CompR.imm_source {ψ₁ ψ₂ ψ : CellU Loc Val} (h : CellU.CompR ψ₁ ψ₂ ψ)
    {s : LSet} {u : Val} {χ : ResU Loc Val} {hh : χ.InStratum s.join}
    (e : ψ = CellU.immOf s u χ hh) :
    (∃ (s₁ : LSet) (h₁ : χ.InStratum s₁.join), ψ₁ = CellU.immOf s₁ u χ h₁) ∨
    (∃ (s₂ : LSet) (h₂ : χ.InStratum s₂.join), ψ₂ = CellU.immOf s₂ u χ h₂) := by
  cases h with
  | same ζ => exact Or.inl ⟨s, hh, e⟩
  | strict k =>
      obtain ⟨s₁, s₂, v, ρ, k₁, k₂, k₃, e₁, e₂, e₃⟩ := CellU.compS_spec _ _ k
      rw [e₃] at e
      obtain ⟨-, hv, hρ⟩ := CellU.immOf_inj e
      subst hv; subst hρ
      exact Or.inl ⟨s₁, k₁, e₁⟩
  | mutMut a b v ρ ha hb P Q hP hQ => exact absurd e.symm CellU.immOf_ne_mutOf
  | mutOwn a v ρ ha P hP => exact absurd e.symm CellU.immOf_ne_mutOf
  | ownMut a v ρ ha P hP => exact absurd e.symm CellU.immOf_ne_mutOf
  | immOwn s' v ρ h =>
      obtain ⟨-, hv, hρ⟩ := CellU.immOf_inj e
      subst hv; subst hρ
      exact Or.inl ⟨s', h, rfl⟩
  | ownImm s' v ρ h =>
      obtain ⟨-, hv, hρ⟩ := CellU.immOf_inj e
      subst hv; subst hρ
      exact Or.inr ⟨s', h, rfl⟩
  | immMut s' v ρ h b hb P hP =>
      obtain ⟨-, hv, hρ⟩ := CellU.immOf_inj e
      subst hv; subst hρ
      exact Or.inl ⟨s', h, rfl⟩
  | mutImm s' v ρ h b hb P hP =>
      obtain ⟨-, hv, hρ⟩ := CellU.immOf_inj e
      subst hv; subst hρ
      exact Or.inr ⟨s', h, rfl⟩

/-- The same at a location of a `○`. -/
theorem ResU.CompR.imm_source {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompR ρ₁ ρ₂ ρ)
    {m : Loc} {s : LSet} {u : Val} {χ : ResU Loc Val} {hh : χ.InStratum s.join}
    (hg : ρ.get m = some (CellU.immOf s u χ hh)) :
    (∃ (s₁ : LSet) (h₁ : χ.InStratum s₁.join),
        ρ₁.get m = some (CellU.immOf s₁ u χ h₁)) ∨
    (∃ (s₂ : LSet) (h₂ : χ.InStratum s₂.join),
        ρ₂.get m = some (CellU.immOf s₂ u χ h₂)) := by
  rcases ResU.Comp.get h m with ⟨-, -, f⟩ | ⟨ξ, f₁, -, f⟩ | ⟨ξ, -, f₂, f⟩ |
      ⟨ξ₁, ξ₂, ξ, f₁, f₂, f, hC⟩
  · rw [f] at hg; exact absurd hg (by simp)
  · exact Or.inl ⟨s, hh, f₁.trans (congrArg some (Option.some.inj (f.symm.trans hg)))⟩
  · exact Or.inr ⟨s, hh, f₂.trans (congrArg some (Option.some.inj (f.symm.trans hg)))⟩
  · rcases CellU.CompR.imm_source hC (Option.some.inj (f.symm.trans hg)) with
      ⟨s₁, h₁, he⟩ | ⟨s₂, h₂, he⟩
    · exact Or.inl ⟨s₁, h₁, f₁.trans (congrArg some he)⟩
    · exact Or.inr ⟨s₂, h₂, f₂.trans (congrArg some he)⟩

/-- An `imm` cell of a `⨀` comes from a member of the family, over the same
value and witness. -/
theorem BigComp.imm_source :
    ∀ {L : List (ResU Loc Val)} {b : ResU Loc Val},
      BigComp CellU.CompatR CellU.CompR L b →
      ∀ {m : Loc} {s : LSet} {u : Val} {χ : ResU Loc Val}
        {hh : χ.InStratum s.join},
        b.get m = some (CellU.immOf s u χ hh) →
        ∃ σ ∈ L, ∃ (s' : LSet) (h' : χ.InStratum s'.join),
          σ.get m = some (CellU.immOf s' u χ h') := by
  intro L
  induction L with
  | nil => intro b h m s u χ hh hg; cases h; exact absurd hg (by simp)
  | cons σ L' ih =>
      intro b h m s u χ hh hg
      cases h with
      | cons hrest hc =>
          rcases ResU.CompR.imm_source hc hg with ⟨s₁, h₁, e⟩ | ⟨s₂, h₂, e⟩
          · exact ⟨σ, List.mem_cons_self, s₁, h₁, e⟩
          · obtain ⟨τ, hm, s', h', e'⟩ := ih hrest e
            exact ⟨τ, List.mem_cons_of_mem _ hm, s', h', e'⟩

/-- If a `○` composite is not `imm`, one operand is not `imm`, over the same
value and witness.
`[about ours: `[TR]` p. 5's `○` read backwards at a non-`imm` result]` -/
theorem CellU.CompR.nonimm_source {ψ₁ ψ₂ ψ : CellU Loc Val}
    (h : CellU.CompR ψ₁ ψ₂ ψ) (hk : ψ.kind ≠ Kind.imm) :
    (ψ₁.kind ≠ Kind.imm ∧ ψ₁.wit = ψ.wit ∧ ψ₁.erase = ψ.erase) ∨
    (ψ₂.kind ≠ Kind.imm ∧ ψ₂.wit = ψ.wit ∧ ψ₂.erase = ψ.erase) := by
  have hmut : ∀ (b : Life) (v : Val) (ρ : ResU Loc Val) (hb : ρ.InStratum b)
      (P : Val → SPropS Loc Val b) (hP : P v ⟨ρ, hb⟩),
      (CellU.mutOf b v ρ hb P hP).kind ≠ Kind.imm := by
    intro b v ρ hb P hP
    rw [CellU.kind_mutOf]
    exact fun c => Kind.noConfusion c
  cases h with
  | same ζ => exact Or.inl ⟨hk, rfl, rfl⟩
  | strict k => exact absurd (CellU.CompS.kind (CellU.compS_spec _ _ k)) hk
  | mutMut a b v ρ ha hb P Q hP hQ =>
      exact Or.inl ⟨hmut _ _ _ _ _ _, by simp, by simp⟩
  | mutOwn a v ρ ha P hP => exact Or.inl ⟨hmut _ _ _ _ _ _, rfl, rfl⟩
  | ownMut a v ρ ha P hP => exact Or.inr ⟨hmut _ _ _ _ _ _, rfl, rfl⟩
  | immOwn s v ρ hh => exact absurd (CellU.kind_immOf s v ρ hh) hk
  | ownImm s v ρ hh => exact absurd (CellU.kind_immOf s v ρ hh) hk
  | immMut s v ρ hh b hb P hP => exact absurd (CellU.kind_immOf s v ρ hh) hk
  | mutImm s v ρ hh b hb P hP => exact absurd (CellU.kind_immOf s v ρ hh) hk

/-- The same at a location of a `○`. -/
theorem ResU.CompR.nonimm_source {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompR ρ₁ ρ₂ ρ)
    {m : Loc} {ψ : CellU Loc Val} (hg : ρ.get m = some ψ)
    (hk : ψ.kind ≠ Kind.imm) :
    (∃ ξ, ρ₁.get m = some ξ ∧ ξ.kind ≠ Kind.imm ∧ ξ.wit = ψ.wit ∧
        ξ.erase = ψ.erase) ∨
    (∃ ξ, ρ₂.get m = some ξ ∧ ξ.kind ≠ Kind.imm ∧ ξ.wit = ψ.wit ∧
        ξ.erase = ψ.erase) := by
  rcases ResU.Comp.get h m with ⟨-, -, f⟩ | ⟨ξ, f₁, -, f⟩ | ⟨ξ, -, f₂, f⟩ |
      ⟨ξ₁, ξ₂, ξ, f₁, f₂, f, hC⟩
  · rw [f] at hg; exact absurd hg (by simp)
  · rw [show ξ = ψ from Option.some.inj (f.symm.trans hg)] at f₁
    exact Or.inl ⟨ψ, f₁, hk, rfl, rfl⟩
  · rw [show ξ = ψ from Option.some.inj (f.symm.trans hg)] at f₂
    exact Or.inr ⟨ψ, f₂, hk, rfl, rfl⟩
  · rw [show ξ = ψ from Option.some.inj (f.symm.trans hg)] at hC
    rcases CellU.CompR.nonimm_source hC hk with ⟨k₁, w₁, e₁⟩ | ⟨k₂, w₂, e₂⟩
    · exact Or.inl ⟨ξ₁, f₁, k₁, w₁, e₁⟩
    · exact Or.inr ⟨ξ₂, f₂, k₂, w₂, e₂⟩

/-- The same along `⨀`. -/
theorem BigComp.nonimm_source :
    ∀ {L : List (ResU Loc Val)} {b : ResU Loc Val},
      BigComp CellU.CompatR CellU.CompR L b →
      ∀ {m : Loc} {ψ : CellU Loc Val}, b.get m = some ψ → ψ.kind ≠ Kind.imm →
      ∃ σ ∈ L, ∃ ξ, σ.get m = some ξ ∧ ξ.kind ≠ Kind.imm ∧ ξ.wit = ψ.wit ∧
        ξ.erase = ψ.erase := by
  intro L
  induction L with
  | nil => intro b h m ψ hg hk; cases h; exact absurd hg (by simp)
  | cons σ L' ih =>
      intro b h m ψ hg hk
      cases h with
      | cons hrest hc =>
          rcases ResU.CompR.nonimm_source hc hg hk with
            ⟨ξ, e, k, w, er⟩ | ⟨ξ, e, k, w, er⟩
          · exact ⟨σ, List.mem_cons_self, ξ, e, k, w, er⟩
          · obtain ⟨τ, hm, ξ', e', k', w', er'⟩ := ih hrest e k
            exact ⟨τ, List.mem_cons_of_mem _ hm, ξ', e',
              k', w'.trans w, er'.trans er⟩

/-- An `imm` operand of `○` gives an `imm` composite over the same value and
witness. -/
theorem CellU.CompR.imm_left_eq {ψ₁ ψ₂ ψ : CellU Loc Val} (h : CellU.CompR ψ₁ ψ₂ ψ)
    {s : LSet} {u : Val} {χ : ResU Loc Val} {hh : χ.InStratum s.join}
    (e : ψ₁ = CellU.immOf s u χ hh) :
    ∃ (s' : LSet) (h' : χ.InStratum s'.join), ψ = CellU.immOf s' u χ h' := by
  cases h with
  | same ζ => exact ⟨s, hh, e⟩
  | strict k =>
      obtain ⟨s₁, s₂, v, ρ, k₁, k₂, k₃, e₁, e₂, e₃⟩ := CellU.compS_spec _ _ k
      rw [e₁] at e
      obtain ⟨-, hv, hρ⟩ := CellU.immOf_inj e.symm
      subst hv; subst hρ
      exact ⟨s₁ ∪ s₂, k₃, e₃⟩
  | mutMut a b v ρ ha hb P Q hP hQ => exact absurd e.symm CellU.immOf_ne_mutOf
  | mutOwn a v ρ ha P hP => exact absurd e.symm CellU.immOf_ne_mutOf
  | ownMut a v ρ ha P hP => exact absurd e CellU.ownOf_ne_immOf
  | immOwn s' v ρ hh' =>
      obtain ⟨-, hv, hρ⟩ := CellU.immOf_inj e.symm
      subst hv; subst hρ
      exact ⟨s', hh', rfl⟩
  | ownImm s' v ρ hh' => exact absurd e CellU.ownOf_ne_immOf
  | immMut s' v ρ hh' b hb P hP =>
      obtain ⟨-, hv, hρ⟩ := CellU.immOf_inj e.symm
      subst hv; subst hρ
      exact ⟨s', hh', rfl⟩
  | mutImm s' v ρ hh' b hb P hP => exact absurd e.symm CellU.immOf_ne_mutOf

/-- The same at a location of a `○`. -/
theorem ResU.CompR.imm_left_get {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompR ρ₁ ρ₂ ρ)
    {m : Loc} {s : LSet} {u : Val} {χ : ResU Loc Val} {hh : χ.InStratum s.join}
    (hg : ρ₁.get m = some (CellU.immOf s u χ hh)) :
    ∃ (s' : LSet) (h' : χ.InStratum s'.join),
      ρ.get m = some (CellU.immOf s' u χ h') := by
  rcases ResU.Comp.get h m with ⟨f₁, -, -⟩ | ⟨ξ, f₁, -, f⟩ | ⟨ξ, f₁, -, -⟩ |
      ⟨ξ₁, ξ₂, ξ, f₁, f₂, f, hC⟩
  · rw [hg] at f₁; exact absurd f₁ (by simp)
  · exact ⟨s, hh, f.trans (congrArg some (Option.some.inj (f₁.symm.trans hg)))⟩
  · rw [hg] at f₁; exact absurd f₁ (by simp)
  · obtain ⟨s', h', he⟩ :=
      CellU.CompR.imm_left_eq hC (Option.some.inj (f₁.symm.trans hg))
    exact ⟨s', h', f.trans (congrArg some he)⟩

/-- If `ag(ρ)(m) = imm(ᾱ, v, χ)` then `⦇χ⦈_○` is a `○`-factor of `ag(ρ)`.
`[about ours: `AgW.imm_wit_le` at a cell of the walk rather than a cell of
`ρ`]` -/
theorem AgW.flat_imm_wit_le {ρ σ : ResU Loc Val} (h : AgW ρ σ) :
    ∀ (m : Loc) (s : LSet) (u : Val) (χ : ResU Loc Val) (hh : χ.InStratum s.join),
      σ.get m = some (CellU.immOf s u χ hh) →
      ∃ ev av p z, ExR χ ev ∧ AgW χ av ∧ ResU.CompR ev av p ∧ ResU.CompR p z σ := by
  have hR : ∀ ψ₁ ψ₂ ψ : CellU Loc Val, CellU.CompR ψ₁ ψ₂ ψ → CellU.CompatR ψ₁ ψ₂ :=
    fun _ _ ψ hc => ⟨ψ, hc⟩
  refine AgW.rec
    (motive_1 := fun ρ σ _ => ∀ (m : Loc) (s : LSet) (u : Val) (χ : ResU Loc Val)
        (hh : χ.InStratum s.join), σ.get m = some (CellU.immOf s u χ hh) →
        ∃ ev av p z, ExR χ ev ∧ AgW χ av ∧ ResU.CompR ev av p ∧ ResU.CompR p z σ)
    (motive_2 := fun ρ w _ => ∀ q ∈ w, ∀ (m : Loc) (s : LSet) (u : Val)
        (χ : ResU Loc Val) (hh : χ.InStratum s.join),
        q.2.get m = some (CellU.immOf s u χ hh) →
        ∃ ev av p z, ExR χ ev ∧ AgW χ av ∧ ResU.CompR ev av p ∧ ResU.CompR p z q.2)
    (motive_3 := fun ρ w _ => ∀ q ∈ w, ∀ (m : Loc) (s : LSet) (u : Val)
        (χ : ResU Loc Val) (hh : χ.InStratum s.join),
        q.2.get m = some (CellU.immOf s u χ hh) →
        ∃ ev av p z, ExR χ ev ∧ AgW χ av ∧ ResU.CompR ev av p ∧ ResU.CompR p z q.2)
    ?mk ?nilM ?consM ?nilI ?consI h
  case mk =>
    intro ρ' σ' a bm bi wm wi hsm hsi hwm hwi hbm hbi ha hσ ihm ihi m s u χ hh hg
    rcases ResU.CompR.imm_source hσ hg with ⟨s₁, h₁, e⟩ | ⟨s₂, h₂, e⟩
    · rcases ResU.CompR.imm_source ha e with ⟨s₃, h₃, e₃⟩ | ⟨s₄, h₄, e₄⟩
      · obtain ⟨hgρ, -⟩ := ResU.restrict_eq_some.mp e₃
        have hfac := AgW.imm_wit_le (AgW.mk hsm hsi hwm hwi hbm hbi ha hσ) hgρ
          (CellU.kind_immOf _ _ _ _)
        rwa [CellU.wit_immOf] at hfac
      · obtain ⟨τ, hm, s', h', e'⟩ := BigComp.imm_source hbm e₄
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
        obtain ⟨ev, av, pp, z, hev, hav, hcc, hz⟩ := ihm q hq m s' u χ h' e'
        obtain ⟨z₁, hz₁⟩ := BigComp.mem_factor hR ResU.compLawsR hbm q.2
          (List.mem_map.mpr ⟨q, hq, rfl⟩)
        obtain ⟨y₁, hy₁⟩ := ResU.Comp.factor_trans hR ResU.compLawsR hz hz₁
        obtain ⟨y₂, hy₂⟩ :=
          ResU.Comp.factor_trans hR ResU.compLawsR hy₁ (ResU.CompR.comm ha)
        obtain ⟨y₃, hy₃⟩ := ResU.Comp.factor_trans hR ResU.compLawsR hy₂ hσ
        exact ⟨ev, av, pp, y₃, hev, hav, hcc, hy₃⟩
    · obtain ⟨τ, hm, s', h', e'⟩ := BigComp.imm_source hbi e
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
      obtain ⟨ev, av, pp, z, hev, hav, hcc, hz⟩ := ihi q hq m s' u χ h' e'
      obtain ⟨z₁, hz₁⟩ := BigComp.mem_factor hR ResU.compLawsR hbi q.2
        (List.mem_map.mpr ⟨q, hq, rfl⟩)
      obtain ⟨y₁, hy₁⟩ := ResU.Comp.factor_trans hR ResU.compLawsR hz hz₁
      obtain ⟨y₂, hy₂⟩ :=
        ResU.Comp.factor_trans hR ResU.compLawsR hy₁ (ResU.CompR.comm hσ)
      exact ⟨ev, av, pp, y₂, hev, hav, hcc, hy₂⟩
  case nilM => intro ρ' q hq; exact absurd hq (by simp)
  case consM =>
    intro ρ' e l w ψ hψ hk he hw ihe ihw q hq
    rcases List.mem_cons.mp hq with rfl | hq'
    · exact ihe
    · exact ihw q hq'
  case nilI => intro ρ' q hq; exact absurd hq (by simp)
  case consI =>
    intro ρ' pe l w ψ hψ hk e a hex hag hc hw iha ihw q hq
    rcases List.mem_cons.mp hq with rfl | hq'
    · intro m s u χ hh hg
      rcases ResU.CompR.imm_source hc hg with ⟨s₁, h₁, e₁⟩ | ⟨s₂, h₂, e₂⟩
      · exact absurd (CellU.kind_immOf _ _ _ _) (ExR.immFree hex m _ e₁)
      · obtain ⟨ev, av, pp, z, hev, hav, hcc, hz⟩ := iha m s₂ u χ h₂ e₂
        obtain ⟨y, hy⟩ :=
          ResU.Comp.factor_trans hR ResU.compLawsR hz (ResU.CompR.comm hc)
        exact ⟨ev, av, pp, y, hev, hav, hcc, hy⟩
    · exact ihw q hq'

/-- `⦇ρ⦈`'s `imm` cell at `m` is `ag(ρ)`'s.
`[about ours: `⦇ρ⦈ ≜ ex(ρ)● ● ag(ρ)` at an `imm` cell]` -/
theorem ResU.ag_eq_flat_at_imm {ρ e a σ : ResU Loc Val} (he : ExS ρ e)
    (hc : ResU.CompS e a σ) {m : Loc} {ψ : CellU Loc Val}
    (hg : σ.get m = some ψ) (hk : ψ.kind = Kind.imm) : a.get m = some ψ := by
  have hen : e.get m = none := by
    cases f : e.get m with
    | none => rfl
    | some ξ =>
        exfalso
        rcases ResU.Comp.get hc m with ⟨f₁, -, -⟩ | ⟨ζ, f₁, -, f'⟩ |
            ⟨ζ, f₁, -, -⟩ | ⟨ζ₁, ζ₂, ζ, f₁, f₂, f', hC⟩
        · rw [f] at f₁; exact absurd f₁ (by simp)
        · refine ExS.immFree he m ζ f₁ ?_
          rw [← show ψ = ζ from Option.some.inj (hg.symm.trans f')]; exact hk
        · rw [f] at f₁; exact absurd f₁ (by simp)
        · exact ExS.immFree he m ζ₁ f₁ (CellU.CompatS.kinds (hc.1 m ζ₁ ζ₂ f₁ f₂)).1
  rcases ResU.Comp.get hc m with ⟨-, f₂, f'⟩ | ⟨ζ, f₁, -, -⟩ | ⟨ζ, -, f₂, f'⟩ |
      ⟨ζ₁, ζ₂, ζ, f₁, -, -, -⟩
  · rw [f'] at hg; exact absurd hg (by simp)
  · rw [hen] at f₁; exact absurd f₁ (by simp)
  · exact f₂.trans (congrArg some (Option.some.inj (f'.symm.trans hg)))
  · rw [hen] at f₁; exact absurd f₁ (by simp)

/-- If `⦇ρ⦈` carries `imm(ᾱ, v, χ)` at `m` then `⦇χ⦈_○` is a `○`-factor of
`ag(ρ)`.
`[about ours: `AgW.flat_imm_wit_le` reached from `⦇ρ⦈` rather than from
`ag(ρ)`]` -/
theorem ResU.flat_imm_wit_factor {ρ e a σ : ResU Loc Val} (he : ExS ρ e)
    (ha : AgW ρ a) (hc : ResU.CompS e a σ)
    {m : Loc} {s : LSet} {u : Val} {χ : ResU Loc Val} {hh : χ.InStratum s.join}
    (hg : σ.get m = some (CellU.immOf s u χ hh)) :
    ∃ ev av p z, ExR χ ev ∧ AgW χ av ∧ ResU.CompR ev av p ∧ ResU.CompR p z a :=
  AgW.flat_imm_wit_le ha m s u χ hh
    (ResU.ag_eq_flat_at_imm he hc hg (CellU.kind_immOf _ _ _ _))

/-- The ancestor transfer: if `ag(ρ₂)` carries `imm(ᾱ, u, χ)` at `m` and
`ρ₂ ↭ ρ₃`, then `ag(ρ₃)` factors through `⦇χ⦈_○` at the same witness `χ`.
`[about ours: `[TR]` 6.48's proof, the sentence *"by the update hypothesis, we
also have `ag(ρ₃)(ℓ′) = ag(ρ₂)(ℓ′)`"*]` -/
theorem ResU.upd_ag_imm_wit_factor {ρ₂ ρ₃ e₂ a₂ σ₂ e₃ a₃ σ₃ : ResU Loc Val}
    (h : ResU.Upd ρ₂ ρ₃)
    (he₂ : ExS ρ₂ e₂) (ha₂ : AgW ρ₂ a₂) (hc₂ : ResU.CompS e₂ a₂ σ₂)
    (he₃ : ExS ρ₃ e₃) (ha₃ : AgW ρ₃ a₃) (hc₃ : ResU.CompS e₃ a₃ σ₃)
    {m : Loc} {s : LSet} {u : Val} {χ : ResU Loc Val} {hh : χ.InStratum s.join}
    (hg : a₂.get m = some (CellU.immOf s u χ hh)) :
    ∃ ev av p z, ExR χ ev ∧ AgW χ av ∧ ResU.CompR ev av p ∧ ResU.CompR p z a₃ := by
  have hex : e₂.get m = none := by
    cases f : e₂.get m with
    | none => rfl
    | some ξ =>
        exact absurd (CellU.CompatS.kinds (hc₂.1 m ξ _ f hg)).1 (ExS.immFree he₂ m ξ f)
  have hσ₂ : σ₂.get m = some (CellU.immOf s u χ hh) := by
    rcases ResU.Comp.get hc₂ m with ⟨-, f₂, -⟩ | ⟨ζ, -, f₂, -⟩ | ⟨ζ, -, f₂, f⟩ |
        ⟨ζ₁, ζ₂, ζ, f₁, -, -, -⟩
    · rw [hg] at f₂; exact absurd f₂ (by simp)
    · rw [hg] at f₂; exact absurd f₂ (by simp)
    · exact f.trans (congrArg some (Option.some.inj (f₂.symm.trans hg)))
    · rw [hex] at f₁; exact absurd f₁ (by simp)
  have hσ₃ : σ₃.get m = some (CellU.immOf s u χ hh) :=
    (ResU.flatAt_iff ⟨e₃, a₃, he₃, ha₃, hc₃⟩ m _).mp
      ((h.1 m s u χ hh).mp ((ResU.flatAt_iff ⟨e₂, a₂, he₂, ha₂, hc₂⟩ m _).mpr hσ₂))
  exact ResU.flat_imm_wit_factor he₃ ha₃ hc₃ hσ₃

/-- `◐` at one location is a function of the two operands. -/
theorem OptComp.functional {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop}
    (hC : ∀ ψ₁ ψ₂ ψ ψ', C ψ₁ ψ₂ ψ → C ψ₁ ψ₂ ψ' → ψ = ψ')
    {x y o o' : Option (CellU Loc Val)}
    (h : OptComp C x y o) (h' : OptComp C x y o') : o = o' := by
  match x, y with
  | none, none => exact h.trans h'.symm
  | some _, none => exact h.trans h'.symm
  | none, some _ => exact h.trans h'.symm
  | some ψ₁, some ψ₂ =>
      obtain ⟨ψ, e, hc⟩ := h
      obtain ⟨ψ', e', hc'⟩ := h'
      rw [e, e', hC ψ₁ ψ₂ ψ ψ' hc hc']

/-- `S ○ own(v) = S` at `S.kind = own`, the form of `[TR]` 6.48's `own` bullet.
`[about ours: `CellU.compR_own_right` at a tag rather than a cell]` -/
theorem CellU.compR_own_kind_right {A S y : CellU Loc Val} (h : CellU.CompR A S y)
    (hk : S.kind = Kind.own) : y = A := by
  rcases CellU.rep S with ⟨u, rfl⟩ | ⟨s, u, τ, m, rfl⟩ | ⟨c, u, τ, m, Q, k, rfl⟩
  · exact CellU.compR_own_right h
  · simp at hk
  · simp at hk

end BoCa.Fig16

end
