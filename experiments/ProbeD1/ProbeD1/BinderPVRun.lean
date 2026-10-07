import ProbeD1.BinderPV

/-!
# ProbeD1 — PlaceViews in W: the guard along a run, and along a future (`BINDER.md` §2.4)

* **The cells of a resource and its flattening.** A cell under no `imm` ancestor that is not `imm`
  is the exclusive walk's cell at its place, and conversely (`ExAt.ex_get`, `ExS.exAt`). An `imm`
  cell under no `imm` ancestor is a copy of the aliasable walk's (`ExAt.ag_get`). Every lifetime of
  an `imm` cell of the aliasable walk is a lifetime of some copy at that place, at some depth, over
  the same value and witness (`AgW.imm_mem_deep`). A cell under an `imm` ancestor is beneath an
  `imm` cell under no `imm` ancestor (`DeepAt.split_imm`).
* **`PVLUpd` at a stack whose places are distinct** (`pvlUpdN`). It is [TR] 6.48's case analysis
  at the local part: a `mut` cell of the exclusive walk by `↭`'s `mut` clause, the case where the
  old flattening's `mut` cell sits beneath an `imm` ancestor excluded by the ancestor transfer
  (`ResU.upd_ag_nonimm_transfer`, the step 6.48's proof spends at the aliasable walk); an `imm`
  cell by `↭`'s `imm` clause and the copies it is made of; a cell under an `imm` ancestor through
  that ancestor, which `↭`'s `imm` clause keeps whole. The places are distinct so that every copy
  at a place is the view of its one entry. `PVLUpd` as stated, at any stack, is not derived: with
  two entries lending one place, a copy of the outer entry's frozen view and the inner entry's
  view compose to one flattening cell, and a resource `↭`-related to it may hold the composite
  where the inner entry's view must be.
* **`PVLRuns`** at distinct places (`pvlRunsN`): `PVLUpd` through `wpG`'s run-end conjunct.
* **`PVLFut`** at payloads the old reading scopes (`pvlFutS`): an inserted variable is new to the
  reading, so a payload type that mentions it is not one the old reading reads. `PVLFut` as
  stated is not derived: at a payload type under a thunk whose `∀` bound mentions an inserted
  variable, the old reading's relation is the vacuous one and the new reading's is not.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace ProbeD1
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open GhostEnd (LEnt LStack LKind extS vwE vwS vis stratS ReLend TabAtS)

/-! ### Cells at any depth -/

theorem DeepAt.trans {ρ : WRes} {m l : BoCa.Loc} {φ ψ : CellU BoCa.Loc Val} (h₁ : DeepAt ρ m φ)
    (h₂ : DeepAt φ.wit l ψ) : DeepAt ρ l ψ := by
  induction h₁ with
  | top e => exact DeepAt.wit e h₂
  | wit em _ ih => exact DeepAt.wit em (ih h₂)

/-- **A cell at any depth is under no `imm` ancestor, or beneath an `imm` cell that is.** -/
theorem DeepAt.split_imm {ρ : WRes} {l : BoCa.Loc} {ψ : CellU BoCa.Loc Val} (h : DeepAt ρ l ψ) :
    ExAt ρ l ψ ∨ ∃ m φ, ExAt ρ m φ ∧ φ.kind = Kind.imm ∧ DeepAt φ.wit l ψ := by
  induction h with
  | top e => exact Or.inl (ExAt.top e)
  | @wit ρ m l φ ψ em hw ih =>
      rcases CellU.rep φ with ⟨u, rfl⟩ | ⟨S, u, χ, hχ, rfl⟩ | ⟨b, u, χ, hχ, Q, hQ, rfl⟩
      · rw [CellU.wit_ownOf] at hw
        cases hw with
        | top e => exact absurd e (by simp)
        | wit e _ => exact absurd e (by simp)
      · exact Or.inr ⟨m, _, ExAt.top em, rfl, hw⟩
      · rcases ih with hx | ⟨m', φ', hx, hk, hd⟩
        · exact Or.inl (ExAt.wit em rfl hx)
        · exact Or.inr ⟨m', φ', ExAt.wit em rfl hx, hk, hd⟩

/-! ### The exclusive walk -/

/-- **A cell under no `imm` ancestor that is not `imm` is the exclusive walk's cell.** -/
theorem ExAt.ex_get {ρ : WRes} {l : BoCa.Loc} {ψ : CellU BoCa.Loc Val} (h : ExAt ρ l ψ)
    (hk : ψ.kind ≠ Kind.imm) : ∀ {e : WRes}, ExS ρ e → e.get l = some ψ := by
  induction h with
  | top e' => intro e he; exact ExS.get_of_ne_imm he e' hk
  | wit em hkm _ ih =>
      intro e he
      obtain ⟨ev, z, hev, hz⟩ :=
        ExW.wit_le (fun _ _ _ hc => CellU.CompS.compat hc) ResU.compLawsS he em hkm
      exact (ResU.CompS.get_left_of_ne_imm hz (ih hk hev) hk).2

/-- A non-`imm` cell of a `⨀_●` is a member's. -/
theorem BigCompS.nonimm_source :
    ∀ {L : List WRes} {b : WRes}, BigComp CellU.CompatS CellU.CompS L b →
      ∀ {l : BoCa.Loc} {φ : CellU BoCa.Loc Val}, b.get l = some φ → φ.kind ≠ Kind.imm →
      ∃ x ∈ L, x.get l = some φ := by
  intro L
  induction L with
  | nil => intro b h l φ e _; cases h; exact absurd e (by simp)
  | cons σ L ih =>
      intro b h l φ e hk
      cases h with
      | cons hrest hc =>
          rcases ResU.CompS.get_split_of_ne_imm hc e hk with ⟨f, -⟩ | ⟨-, f⟩
          · exact ⟨σ, List.mem_cons_self, f⟩
          · obtain ⟨x, hx, fx⟩ := ih hrest f hk
            exact ⟨x, List.mem_cons_of_mem _ hx, fx⟩

/-- **A cell of the exclusive walk is a cell under no `imm` ancestor.** -/
theorem ExS.exAt {ρ e : WRes} (h : ExS ρ e) : ∀ {l : BoCa.Loc} {φ : CellU BoCa.Loc Val},
    e.get l = some φ → ExAt ρ l φ := by
  refine ExW.rec
    (motive_1 := fun ρ e _ => ∀ {l : BoCa.Loc} {φ : CellU BoCa.Loc Val},
      e.get l = some φ → ExAt ρ l φ)
    (motive_2 := fun ρ w _ => ∀ p ∈ w, ∀ {l : BoCa.Loc} {φ : CellU BoCa.Loc Val},
      p.2.get l = some φ → ∃ ψ, ρ.get p.1 = some ψ ∧ ψ.kind = Kind.mut ∧ ExAt ψ.wit l φ)
    ?mk ?nil ?cons h
  case mk =>
    intro ρ' σ' nm b w hs hw hb hnm hσ ihw l φ e
    have hfree : σ'.ImmFree := ExS.immFree (ExW.mk hs hw hb hnm hσ)
    have hk : φ.kind ≠ Kind.imm := hfree l φ e
    rcases ResU.CompS.get_split_of_ne_imm hσ e hk with ⟨f, -⟩ | ⟨-, f⟩
    · rcases ResU.CompS.get_split_of_ne_imm hnm f hk with ⟨f', -⟩ | ⟨-, f'⟩
      · exact ExAt.top (ResU.restrict_eq_some.mp f').1
      · exact ExAt.top (ResU.restrict_eq_some.mp f').1
    · obtain ⟨x, hx, fx⟩ := BigCompS.nonimm_source hb f hk
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
      obtain ⟨ψ, hψ, hkψ, hwψ⟩ := ihw p hp fx
      exact ExAt.wit hψ hkψ hwψ
  case nil => intro ρ' p hp; exact absurd hp (by simp)
  case cons =>
    intro ρ' e' l' w ψ hψ hk he hw ihe ihw p hp l φ ep
    rcases List.mem_cons.mp hp with rfl | hp'
    · exact ⟨ψ, hψ, hk, ihe ep⟩
    · exact ihw p hp' ep

/-! ### The aliasable walk -/

/-- An `imm` operand of `○` gives an `imm` composite over the same value and witness, with its
lifetimes among the composite's. -/
theorem CellU.CompR.imm_left_sub {S : LSet} {v : Val} {χ : WRes} {h : χ.InStratum S.join}
    {ψ₂ ψ : CellU BoCa.Loc Val} (hc : CellU.CompR (CellU.immOf S v χ h) ψ₂ ψ) :
    ∃ (S' : LSet) (h' : χ.InStratum S'.join), ψ = CellU.immOf S' v χ h' ∧
      ∀ x, S.mem x → S'.mem x := by
  generalize hl : CellU.immOf S v χ h = ψ₁ at hc
  cases hc with
  | same ζ => exact ⟨S, h, hl.symm, fun _ hx => hx⟩
  | strict k =>
      obtain ⟨s₁, s₂, v', ρ, k₁, k₂, k₃, e₁, e₂, e₃⟩ := CellU.compS_spec _ _ k
      rw [← hl] at e₁
      obtain ⟨rfl, rfl, rfl⟩ := CellU.immOf_inj e₁
      exact ⟨S ∪ s₂, k₃, e₃, fun x hx => Or.inl hx⟩
  | mutMut a b v' ρ ha hb P Q hP hQ => exact absurd hl CellU.immOf_ne_mutOf
  | mutOwn a v' ρ ha P hP => exact absurd hl CellU.immOf_ne_mutOf
  | ownMut a v' ρ ha P hP => exact absurd hl.symm CellU.ownOf_ne_immOf
  | immOwn s' v' ρ hh' =>
      obtain ⟨rfl, rfl, rfl⟩ := CellU.immOf_inj hl
      exact ⟨S, h, rfl, fun _ hx => hx⟩
  | ownImm s' v' ρ hh' => exact absurd hl.symm CellU.ownOf_ne_immOf
  | immMut s' v' ρ hh' b hb P hP =>
      obtain ⟨rfl, rfl, rfl⟩ := CellU.immOf_inj hl
      exact ⟨S, h, rfl, fun _ hx => hx⟩
  | mutImm s' v' ρ hh' b hb P hP => exact absurd hl CellU.immOf_ne_mutOf

theorem ResU.CompR.imm_left_sub {ρ₁ ρ₂ ρ : WRes} (hc : ResU.CompR ρ₁ ρ₂ ρ) {l : BoCa.Loc}
    {S : LSet} {v : Val} {χ : WRes} {h : χ.InStratum S.join}
    (e : ρ₁.get l = some (CellU.immOf S v χ h)) :
    ∃ (S' : LSet) (h' : χ.InStratum S'.join), ρ.get l = some (CellU.immOf S' v χ h') ∧
      ∀ x, S.mem x → S'.mem x := by
  rcases ResU.Comp.get hc l with ⟨f₁, -, -⟩ | ⟨ξ, f₁, -, f⟩ | ⟨ξ, f₁, -, -⟩ |
      ⟨ξ₁, ξ₂, ξ, f₁, -, f, hC⟩
  · rw [e] at f₁; exact absurd f₁ (by simp)
  · rw [e] at f₁; obtain rfl := Option.some.inj f₁; exact ⟨S, h, f, fun _ hx => hx⟩
  · rw [e] at f₁; exact absurd f₁ (by simp)
  · rw [e] at f₁; obtain rfl := Option.some.inj f₁
    obtain ⟨S', h', rfl, hsub⟩ := CellU.CompR.imm_left_sub hC
    exact ⟨S', h', f, hsub⟩

/-- **An `imm` cell under no `imm` ancestor is a copy of the aliasable walk's cell.** -/
theorem ExAt.ag_get {ρ : WRes} {l : BoCa.Loc} {ψ : CellU BoCa.Loc Val} (h : ExAt ρ l ψ) :
    ∀ {S : LSet} {v : Val} {χ : WRes} {hS : χ.InStratum S.join}, ψ = CellU.immOf S v χ hS →
    ∀ {a : WRes}, AgW ρ a → ∃ (S' : LSet) (h' : χ.InStratum S'.join),
      a.get l = some (CellU.immOf S' v χ h') ∧ ∀ x, S.mem x → S'.mem x := by
  induction h with
  | top e' =>
      intro S v χ hS hψ a ha
      subst hψ
      cases ha with
      | mk hsm hsi hwm hwi hbm hbi ha' hσ =>
          obtain ⟨S₁, h₁, f₁, hs₁⟩ := ResU.CompR.imm_left_sub ha'
            (ResU.restrict_eq_some.mpr ⟨e', rfl⟩)
          obtain ⟨S₂, h₂, f₂, hs₂⟩ := ResU.CompR.imm_left_sub hσ f₁
          exact ⟨S₂, h₂, f₂, fun x hx => hs₂ x (hs₁ x hx)⟩
  | wit em hkm _ ih =>
      intro S v χ hS hψ a ha
      obtain ⟨av, z, hav, hz⟩ := AgW.mut_wit_le ha em hkm
      obtain ⟨S₁, h₁, f₁, hs₁⟩ := ih hψ hav
      obtain ⟨S₂, h₂, f₂, hs₂⟩ := ResU.CompR.imm_left_sub hz f₁
      exact ⟨S₂, h₂, f₂, fun x hx => hs₂ x (hs₁ x hx)⟩

/-- A lifetime of an `imm` cell of a `○` composite is a lifetime of an operand's cell there. -/
theorem ResU.CompR.imm_mem {ρ₁ ρ₂ ρ : WRes} (hc : ResU.CompR ρ₁ ρ₂ ρ) {l : BoCa.Loc}
    {S : LSet} {v : Val} {χ : WRes} {h : χ.InStratum S.join}
    (e : ρ.get l = some (CellU.immOf S v χ h)) {x : Life} (hx : S.mem x) :
    (∃ (S₁ : LSet) (h₁ : χ.InStratum S₁.join), ρ₁.get l = some (CellU.immOf S₁ v χ h₁) ∧
        S₁.mem x) ∨
      (∃ (S₂ : LSet) (h₂ : χ.InStratum S₂.join), ρ₂.get l = some (CellU.immOf S₂ v χ h₂) ∧
        S₂.mem x) := by
  rcases ResU.Comp.get hc l with ⟨-, -, f⟩ | ⟨ξ, f₁, -, f⟩ | ⟨ξ, -, f₂, f⟩ |
      ⟨ξ₁, ξ₂, ξ, f₁, f₂, f, hC⟩
  · rw [e] at f; exact absurd f (by simp)
  · rw [e] at f; obtain rfl := Option.some.inj f; exact Or.inl ⟨S, h, f₁, hx⟩
  · rw [e] at f; obtain rfl := Option.some.inj f; exact Or.inr ⟨S, h, f₂, hx⟩
  · rw [e] at f; obtain rfl := Option.some.inj f
    generalize hres : CellU.immOf S v χ h = ζ at hC
    cases hC with
    | same ζ' =>
        subst hres
        exact Or.inl ⟨S, h, f₁, hx⟩
    | strict k =>
        obtain ⟨s₁, s₂, v', ρ', k₁, k₂, k₃, e₁, e₂, e₃⟩ := CellU.compS_spec _ _ k
        rw [← hres] at e₃
        obtain ⟨rfl, rfl, rfl⟩ := CellU.immOf_inj e₃
        rcases hx with hx | hx
        · exact Or.inl ⟨s₁, k₁, f₁.trans (congrArg some e₁), hx⟩
        · exact Or.inr ⟨s₂, k₂, f₂.trans (congrArg some e₂), hx⟩
    | mutMut a b v' ρ' ha hb P Q hP hQ => exact absurd hres CellU.immOf_ne_mutOf
    | mutOwn a v' ρ' ha P hP => exact absurd hres CellU.immOf_ne_mutOf
    | ownMut a v' ρ' ha P hP => exact absurd hres CellU.immOf_ne_mutOf
    | immOwn s' v' ρ' hh' => exact Or.inl ⟨S, h, f₁.trans (congrArg some hres.symm), hx⟩
    | ownImm s' v' ρ' hh' => exact Or.inr ⟨S, h, f₂.trans (congrArg some hres.symm), hx⟩
    | immMut s' v' ρ' hh' b hb P hP => exact Or.inl ⟨S, h, f₁.trans (congrArg some hres.symm), hx⟩
    | mutImm s' v' ρ' hh' b hb P hP => exact Or.inr ⟨S, h, f₂.trans (congrArg some hres.symm), hx⟩

theorem BigCompR.imm_mem :
    ∀ {L : List WRes} {b : WRes}, BigComp CellU.CompatR CellU.CompR L b →
      ∀ {l : BoCa.Loc} {S : LSet} {v : Val} {χ : WRes} {h : χ.InStratum S.join},
      b.get l = some (CellU.immOf S v χ h) → ∀ {x : Life}, S.mem x →
      ∃ σ ∈ L, ∃ (S₁ : LSet) (h₁ : χ.InStratum S₁.join),
        σ.get l = some (CellU.immOf S₁ v χ h₁) ∧ S₁.mem x := by
  intro L
  induction L with
  | nil => intro b hb l S v χ h e; cases hb; exact absurd e (by simp)
  | cons σ L ih =>
      intro b hb l S v χ h e x hx
      cases hb with
      | cons hrest hc =>
          rcases ResU.CompR.imm_mem hc e hx with ⟨S₁, h₁, f₁, hx₁⟩ | ⟨S₂, h₂, f₂, hx₂⟩
          · exact ⟨σ, List.mem_cons_self, S₁, h₁, f₁, hx₁⟩
          · obtain ⟨τ, hτ, S₃, h₃, f₃, hx₃⟩ := ih hrest f₂ hx₂
            exact ⟨τ, List.mem_cons_of_mem _ hτ, S₃, h₃, f₃, hx₃⟩

/-- **Every lifetime of an `imm` cell of the aliasable walk is one of a copy at that place, at
some depth, over the same value and witness.** -/
theorem AgW.imm_mem_deep {ρ a : WRes} (h : AgW ρ a) : ∀ {l : BoCa.Loc} {S : LSet} {v : Val}
    {χ : WRes} {hS : χ.InStratum S.join}, a.get l = some (CellU.immOf S v χ hS) →
    ∀ {x : Life}, S.mem x → ∃ (S₀ : LSet) (h₀ : χ.InStratum S₀.join),
      DeepAt ρ l (CellU.immOf S₀ v χ h₀) ∧ S₀.mem x := by
  refine AgW.rec
    (motive_1 := fun ρ a _ => ∀ {l : BoCa.Loc} {S : LSet} {v : Val} {χ : WRes}
      {hS : χ.InStratum S.join}, a.get l = some (CellU.immOf S v χ hS) →
      ∀ {x : Life}, S.mem x → ∃ (S₀ : LSet) (h₀ : χ.InStratum S₀.join),
        DeepAt ρ l (CellU.immOf S₀ v χ h₀) ∧ S₀.mem x)
    (motive_2 := fun ρ w _ => ∀ q ∈ w, ∀ {l : BoCa.Loc} {S : LSet} {v : Val} {χ : WRes}
      {hS : χ.InStratum S.join}, q.2.get l = some (CellU.immOf S v χ hS) →
      ∀ {x : Life}, S.mem x → ∃ (S₀ : LSet) (h₀ : χ.InStratum S₀.join),
        DeepAt ρ l (CellU.immOf S₀ v χ h₀) ∧ S₀.mem x)
    (motive_3 := fun ρ w _ => ∀ q ∈ w, ∀ {l : BoCa.Loc} {S : LSet} {v : Val} {χ : WRes}
      {hS : χ.InStratum S.join}, q.2.get l = some (CellU.immOf S v χ hS) →
      ∀ {x : Life}, S.mem x → ∃ (S₀ : LSet) (h₀ : χ.InStratum S₀.join),
        DeepAt ρ l (CellU.immOf S₀ v χ h₀) ∧ S₀.mem x)
    ?mk ?nilM ?consM ?nilI ?consI h
  case mk =>
    intro ρ' σ' a' bm bi wm wi hsm hsi hwm hwi hbm hbi ha hσ ihm ihi l S v χ hS e x hx
    rcases ResU.CompR.imm_mem hσ e hx with ⟨S₁, h₁, f₁, hx₁⟩ | ⟨S₂, h₂, f₂, hx₂⟩
    · rcases ResU.CompR.imm_mem ha f₁ hx₁ with ⟨S₃, h₃, f₃, hx₃⟩ | ⟨S₄, h₄, f₄, hx₄⟩
      · exact ⟨S₃, h₃, DeepAt.top (ResU.restrict_eq_some.mp f₃).1, hx₃⟩
      · obtain ⟨τ, hτ, S₅, h₅, f₅, hx₅⟩ := BigCompR.imm_mem hbm f₄ hx₄
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hτ
        exact ihm q hq f₅ hx₅
    · obtain ⟨τ, hτ, S₅, h₅, f₅, hx₅⟩ := BigCompR.imm_mem hbi f₂ hx₂
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hτ
      exact ihi q hq f₅ hx₅
  case nilM => intro ρ' q hq; exact absurd hq (by simp)
  case consM =>
    intro ρ' e' l' w ψ hψ hk he hw ihe ihw q hq l S v χ hS eq x hx
    rcases List.mem_cons.mp hq with rfl | hq'
    · obtain ⟨S₀, h₀, hd, hx₀⟩ := ihe eq hx
      exact ⟨S₀, h₀, DeepAt.wit hψ hd, hx₀⟩
    · exact ihw q hq' eq hx
  case nilI => intro ρ' q hq; exact absurd hq (by simp)
  case consI =>
    intro ρ' pe l' w ψ hψ hk e' a' hex hag hc hw iha ihw q hq l S v χ hS eq x hx
    rcases List.mem_cons.mp hq with rfl | hq'
    · rcases ResU.CompR.imm_mem hc eq hx with ⟨S₁, h₁, f₁, -⟩ | ⟨S₂, h₂, f₂, hx₂⟩
      · exact absurd (CellU.kind_immOf _ _ _ _) (ExR.immFree hex l _ f₁)
      · obtain ⟨S₀, h₀, hd, hx₀⟩ := iha f₂ hx₂
        exact ⟨S₀, h₀, DeepAt.wit hψ hd, hx₀⟩
    · exact ihw q hq' eq hx

/-! ### `PVLUpd` at distinct places -/

/-- **`PVLUpd` at a stack whose places are distinct.** Every lend makes its place new to the stack
(`LendMut`, `LendImm`, `OwnOK.place`, `FutOK.places`), so the stacks a run reaches have distinct
places; `StackOK` does not ask it. -/
def PVLUpdN : Prop :=
  ∀ (s : LSub) (σ : LStack) (αs : List Life) (ls : List SRec) (ρ π : WRes), StackOK σ αs →
    (σ.map LEnt.l).Nodup → PlaceViewsL s σ αs ls ρ → ResU.UpdV ρ π → PlaceViewsL s σ αs ls π

/-- **`PVLRuns` at a stack whose places are distinct.** -/
def PVLRunsN : Prop :=
  ∀ (s : LSub) (σ : LStack) (αs : List Life) (ls : List SRec) (e : Expr)
    (Q : List SRec → Expr → WProp) (ρ : WRes), StackOK σ αs → (σ.map LEnt.l).Nodup →
    PlaceViewsL s σ αs ls ρ → wpG (ℍ := ℍ) ls e Q ρ →
      wpG (ℍ := ℍ) ls e (fun ls' t ρ' => PlaceViewsL s σ αs ls' ρ' ∧ Q ls' t ρ') ρ

/-- At distinct places, one entry lends a place. -/
theorem zip_unique_l : ∀ {σ : LStack} {αs : List Life}, (σ.map LEnt.l).Nodup →
    ∀ {e e' : LEnt} {α α' : Life}, (e, α) ∈ σ.zip αs → (e', α') ∈ σ.zip αs → e.l = e'.l →
      e = e' ∧ α = α'
  | [], _, _, _, _, _, _, h, _, _ => by simp at h
  | _ :: _, [], _, _, _, _, _, h, _, _ => by simp at h
  | x :: σ, a :: αs, hnd, e, e', α, α', h, h', hl => by
      rw [List.zip_cons_cons] at h h'
      simp only [List.map_cons, List.nodup_cons] at hnd
      have hxσ : ∀ e₀ α₀, (e₀, α₀) ∈ σ.zip αs → x.l ≠ e₀.l := fun e₀ α₀ hm he₀ =>
        hnd.1 (he₀ ▸ List.mem_map_of_mem (List.of_mem_zip hm).1)
      rcases List.mem_cons.mp h with he | ht
      · rcases List.mem_cons.mp h' with he' | ht'
        · rw [Prod.mk.inj he |>.1, Prod.mk.inj he |>.2, Prod.mk.inj he' |>.1, Prod.mk.inj he' |>.2]
          exact ⟨rfl, rfl⟩
        · exact absurd (by rw [← (Prod.mk.inj he).1]; exact hl) (hxσ e' α' ht')
      · rcases List.mem_cons.mp h' with he' | ht'
        · exact absurd (by rw [← (Prod.mk.inj he').1]; exact hl.symm) (hxσ e α ht)
        · exact zip_unique_l hnd.2 ht ht' hl

/-- A view at a `mut` entry reads a cell only through its lifetime and stored invariant. -/
theorem vwEW_mut_same {s : LSub} {e : LEnt} {α : Life} {ls : List SRec} {l : BoCa.Loc}
    {b : Life} {v v' : Val} {χ χ' : WRes} {h : χ.InStratum b} {h' : χ'.InStratum b}
    {P : Val → SPropS BoCa.Loc Val b} {hw : P v ⟨χ, h⟩} {hw' : P v' ⟨χ', h'⟩}
    (hv : vwEW s e true α ls (ResU.single l (CellU.mutOf b v' χ' h' P hw'))) :
    vwEW s e true α ls (ResU.single l (CellU.mutOf b v χ h P hw)) := by
  obtain ⟨el, ex, eT, ek, ecr⟩ := e
  cases ek with
  | «mut» =>
      obtain ⟨⟨b₀, u, σ₀, hσ₀, Q, hwQ, ls₀, hα, hρ, hQ, hls₀, hsupp⟩, hat⟩ := hv
      have hg := congrArg (fun r => PMap.get r l) hρ
      simp only [ResU.single_get_self] at hg
      have hl : l = el := by
        by_contra hne
        rw [ResU.single_get_ne _ hne] at hg
        exact absurd hg (by simp)
      subst hl
      rw [ResU.single_get_self] at hg
      have hcell := Option.some.inj hg
      have hb : b = b₀ := CellU.mutOf_at hcell
      subst hb
      obtain ⟨-, -, hPQ⟩ := CellU.mutOf_inj hcell
      subst hPQ
      have hat' := hat _ (ResU.single_get_self _ _)
      refine ⟨⟨b, v, χ, h, P, hw, ls₀, hα, rfl, hQ, hls₀, hsupp⟩, fun ψ hψ => ?_⟩
      rw [ResU.single_get_self] at hψ
      obtain rfl := Option.some.inj hψ
      exact ⟨hat'.1, fun t ht => by simp at ht⟩
  | imm u₀ =>
      exfalso
      obtain ⟨-, S, v₀, χ₀, h₀, he, -⟩ := (vwEW_imm_iff (e := ⟨el, ex, eT, .imm u₀, ecr⟩) rfl).mp hv
      exact CellU.immOf_ne_mutOf he.symm

/-- **The guard's views along `↭`, at distinct places**: [TR] 6.48's cases at the local part. -/
theorem pvlUpdN : PVLUpdN := by
  intro s σ αs ls ρ π hok hnd h hu
  obtain ⟨hupd, ⟨σρ, eρ, aρ, heρ, haρ, hcρ⟩, ⟨σπ, eπ, aπ, heπ, haπ, hcπ⟩⟩ := hu
  have hfρ : ResU.Flat ρ σρ := ⟨eρ, aρ, heρ, haρ, hcρ⟩
  have hfπ : ResU.Flat π σπ := ⟨eπ, aπ, heπ, haπ, hcπ⟩
  -- the copies at a bound place are the views of its one entry
  have hcopy : ∀ l e α, innerAt σ αs l = some (e, α) → ∀ (S : LSet) (v : Val) (χ : WRes)
      (hS : χ.InStratum S.join), aρ.get l = some (CellU.immOf S v χ hS) →
      (∀ x, S.mem x → x = α) ∧ ∃ (S₀ : LSet) (h₀ : χ.InStratum S₀.join),
        DeepAt ρ l (CellU.immOf S₀ v χ h₀) ∧
        vwEW s e true α ls (ResU.single l (CellU.immOf S₀ v χ h₀)) := by
    intro l e α hi S v χ hS ha
    obtain ⟨hm, hel⟩ := innerAt_mem hi
    have hl : l ∈ σ.map LEnt.l := mem_places_of_innerAt hi
    have view : ∀ (S₀ : LSet) (h₀ : χ.InStratum S₀.join), DeepAt ρ l (CellU.immOf S₀ v χ h₀) →
        vwEW s e true α ls (ResU.single l (CellU.immOf S₀ v χ h₀)) := by
      intro S₀ h₀ hd
      obtain ⟨e', α', hm', hel', hv'⟩ := h.2 l _ hd (by simp) hl
      obtain ⟨rfl, rfl⟩ := zip_unique_l hnd hm' hm (hel'.trans hel.symm)
      exact hv'
    refine ⟨fun x hx => ?_, ?_⟩
    · obtain ⟨S₀, h₀, hd, hx₀⟩ := AgW.imm_mem_deep haρ ha hx
      exact (vwEW_atExactly hel (view S₀ h₀ hd)).2 S₀ rfl x hx₀
    · obtain ⟨S₀, h₀, hd, -⟩ := AgW.imm_mem_deep haρ ha S.meet_mem
      exact ⟨S₀, h₀, hd, view S₀ h₀ hd⟩
  -- the first conjunct: a cell under no `imm` ancestor
  have caseA : ∀ l ψ, ExAt π l ψ → ψ.kind ≠ Kind.own → ∀ e α, innerAt σ αs l = some (e, α) →
      vwEW s e true α ls (ResU.single l ψ) := by
    intro l ψ hx ho e α hi
    rcases CellU.rep ψ with ⟨u, rfl⟩ | ⟨S, v, χ, hS, rfl⟩ | ⟨b, v, χ, hχ, P, hw, rfl⟩
    · exact absurd rfl ho
    · -- an `imm` cell: a copy of the flattening's, which `↭`'s `imm` clause keeps
      obtain ⟨S', h', ha', hsub⟩ := ExAt.ag_get hx rfl haπ
      have hσπ : σπ.get l = some (CellU.immOf S' v χ h') :=
        ResU.CompS.get_right_of_immFree hcπ (ExS.immFree heπ) ha'
      have hσρ : σρ.get l = some (CellU.immOf S' v χ h') :=
        (ResU.flatAt_iff hfρ l _).mp ((hupd.1 l S' v χ h').mpr ((ResU.flatAt_iff hfπ l _).mpr hσπ))
      have haρl := ResU.ag_eq_flat_at_imm heρ hcρ hσρ (CellU.kind_immOf _ _ _ _)
      obtain ⟨hall, S₀, h₀, -, hv₀⟩ := hcopy l e α hi S' v χ h' haρl
      exact vwEW_immSub hv₀ (Or.inr ⟨S, S₀, v, χ, hS, h₀, rfl, rfl, fun x hx' => by
        rw [hall x (hsub x hx')]
        have hmem₀ := (vwEW_atExactly (innerAt_mem hi).2 hv₀)
        have := hmem₀.2 S₀ rfl S₀.meet S₀.meet_mem
        rw [← this]; exact S₀.meet_mem⟩)
    · -- a `mut` cell: the flattening's, which `↭`'s `mut` clause keeps
      have hk : (CellU.mutOf b v χ hχ P hw).kind ≠ Kind.imm := by simp
      have heπl : eπ.get l = some (CellU.mutOf b v χ hχ P hw) := ExAt.ex_get hx hk heπ
      have hσπ : σπ.get l = some (CellU.mutOf b v χ hχ P hw) :=
        (ResU.CompS.get_left_of_ne_imm hcπ heπl hk).2
      obtain ⟨v', χ', hχ', hw', hfa⟩ :=
        (hupd.2 l b P).mpr ⟨v, χ, hχ, hw, (ResU.flatAt_iff hfπ l _).mpr hσπ⟩
      have hσρ : σρ.get l = some (CellU.mutOf b v' χ' hχ' P hw') := (ResU.flatAt_iff hfρ l _).mp hfa
      have hk' : (CellU.mutOf b v' χ' hχ' P hw').kind ≠ Kind.imm := by simp
      rcases ResU.CompS.get_split_of_ne_imm hcρ hσρ hk' with ⟨feρ, -⟩ | ⟨-, faρ⟩
      · exact vwEW_mut_same (h.1 l _ (ExS.exAt heρ feρ) (by simp) e α hi)
      · exfalso
        obtain ⟨-, -, -, p, z, ξ, -, -, -, hz, hpn, -, -, -⟩ :=
          ResU.upd_ag_nonimm_transfer hupd heρ haρ hcρ heπ haπ hcπ faρ hk'
        obtain ⟨ζ, hζ⟩ : ∃ ζ, aπ.get l = some ζ := by
          rcases ResU.Comp.get hz l with ⟨f₁, -, -⟩ | ⟨ψ', -, -, f⟩ | ⟨ψ', f₁, -, -⟩ |
              ⟨ψ₁, ψ₂, ψ', -, -, f, -⟩
          · rw [hpn] at f₁; exact absurd f₁ (by simp)
          · exact ⟨ψ', f⟩
          · rw [hpn] at f₁; exact absurd f₁ (by simp)
          · exact ⟨ψ', f⟩
        exact hk (CellU.CompatS.kinds (hcπ.1 l _ ζ heπl hζ)).1
  refine ⟨caseA, fun l ψ hd ho hl => ?_⟩
  rcases DeepAt.split_imm hd with hx | ⟨m, φ, hxm, hkm, hdw⟩
  · obtain ⟨e, α, hi⟩ := innerAt_isSome hok.1 hl
    obtain ⟨hm, hel⟩ := innerAt_mem hi
    exact ⟨e, α, hm, hel, caseA l ψ hx ho e α hi⟩
  · -- beneath an `imm` ancestor, which `↭`'s `imm` clause keeps whole
    rcases CellU.rep φ with ⟨u, rfl⟩ | ⟨S, v, χ, hS, rfl⟩ | ⟨b, v, χ, hχ, P, hw, rfl⟩
    · simp at hkm
    · obtain ⟨S', h', ha', -⟩ := ExAt.ag_get hxm rfl haπ
      have hσπ : σπ.get m = some (CellU.immOf S' v χ h') :=
        ResU.CompS.get_right_of_immFree hcπ (ExS.immFree heπ) ha'
      have hσρ : σρ.get m = some (CellU.immOf S' v χ h') :=
        (ResU.flatAt_iff hfρ m _).mp ((hupd.1 m S' v χ h').mpr ((ResU.flatAt_iff hfπ m _).mpr hσπ))
      have haρm := ResU.ag_eq_flat_at_imm heρ hcρ hσρ (CellU.kind_immOf _ _ _ _)
      obtain ⟨S₀, h₀, hd₀, -⟩ := AgW.imm_mem_deep haρ haρm S'.meet_mem
      rw [CellU.wit_immOf] at hdw
      have hdρ : DeepAt ρ l ψ := hd₀.trans (by rw [CellU.wit_immOf]; exact hdw)
      exact h.2 l ψ hdρ ho hl
    · simp at hkm

/-- A view reads its list only through the members longer-lived than its cell. -/
theorem vwEW_list_congr {s : LSub} {e : LEnt} {α : Life} {ls ls' : List SRec} {ρ : WRes}
    (hl : ∀ x, x ∈ ls ↔ x ∈ ls') {d : Bool} (h : vwEW s e d α ls ρ) : vwEW s e d α ls' ρ := by
  refine ⟨?_, h.2⟩
  cases d with
  | false => exact h.1
  | true =>
      obtain ⟨el, ex, eT, ek, ecr⟩ := e
      cases ek with
      | «mut» =>
          obtain ⟨b, u, σ₀, hσ₀, Q, hw, ls₀, hα, hρ, hQ, hls₀, hsupp⟩ := h.1
          exact ⟨b, u, σ₀, hσ₀, Q, hw, ls₀, hα, hρ, hQ, fun x => by rw [hls₀, hl], hsupp⟩
      | imm v =>
          obtain ⟨S, u, σ₀, hσ₀, ls₀, hρ, hP, hα, hls₀⟩ := h.1
          exact ⟨S, u, σ₀, hσ₀, ls₀, hρ, hP, hα, fun x => by rw [hls₀, hl]⟩

theorem placeViewsL_list_congr {s : LSub} {σ : LStack} {αs : List Life} {ls ls' : List SRec}
    {ρ : WRes} (hl : ∀ x, x ∈ ls ↔ x ∈ ls') (h : PlaceViewsL s σ αs ls ρ) :
    PlaceViewsL s σ αs ls' ρ :=
  ⟨fun l ψ hx ho e α hi => vwEW_list_congr hl (h.1 l ψ hx ho e α hi),
    fun l ψ hd ho hlm => by
      obtain ⟨e, α, hm, hel, hv⟩ := h.2 l ψ hd ho hlm
      exact ⟨e, α, hm, hel, vwEW_list_congr hl hv⟩⟩

/-- **Every run keeps the guard's views, at distinct places.** -/
theorem pvlRunsN : PVLRunsN (ℍ := ℍ) := by
  intro s σ αs ls e Q ρ hok hnd h hw ρf fρ ps hh hc hT htg A k
  obtain ⟨ρ', ρp, fρ', fρ'p, π, t, μ, μ', ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀,
    h₁₁, h₁₂, h₁₃, h₁₄, hQ⟩ := hw ρf fρ ps hh hc hT htg A k
  have hπ : PlaceViewsL s σ αs ls π := pvlUpdN s σ αs ls ρ π hok hnd h h₉
  have hρ' : PlaceViewsL s σ αs ls ρ' := placeViewsL_left h₈ hπ
  exact ⟨ρ', ρp, fρ', fρ'p, π, t, μ, μ', ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀,
    h₁₁, h₁₂, h₁₃, h₁₄, placeViewsL_list_congr (fun x => (h₁₄ x).symm) hρ', hQ⟩

end ProbeD1

end
