import Support.Model.Tree.World.UpdA
import Support.Model.Tree.World.UpdXInv

/-!
# `UpdA` beside a frame, along the walks  `[spec §62]`

`[TR]` 6.48 (`updV_frame`, `Tree/Port/Six48.lean`) at `UpdA` (`World/UpdA.lean`). The printed
proof splits `⦇ρ₁ ● ρⱼ⦈` into the two exclusive walks and the aliasable one, and in the aliasable
case accounts for a `mut` cell of `ag(ρ₂)` by the `imm` cell it sits beneath. `UpdA.frame` does
the same at `UpdA`'s cells:

* **The ancestor of a `mut` cell of the aliasable walk** (`AgW.mut_beneath`): in a world with one
  `mut` cell per location, a `mut` cell of `ag(ρ)` sits beneath an `imm` cell of `ag(ρ)` whose
  witness's `⦇−⦈_○` carries that very cell. It is `AgWT.nonimm_beneath_imm`'s induction with `○`
  keeping `mut` cells (`mutKeep_compR`).
* **An `imm` composite and its operands** (`ImmLe`, `CellUT.CompR.immLe_left/right`,
  `CellUT.CompR.imm_ls_le`): `○` makes an `imm` cell over the value and witness of its `imm`
  operands, at the union of their lifetime sets. So the end world absorbs an `imm` composite when
  it absorbs each `imm` operand (`cellAbs_compR`), and an `imm` composite is absorbed by a start
  cell when each `imm` operand is (`cellSub_compR`).
* **A `Beneath` lifts along `○`** (`Beneath.lift`): the composite at the ancestor's location has
  the ancestor's witness.
-/

noncomputable section

namespace BoCa.Fig16.Tree.Wp
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree

variable {K K' : WCactus}

/-! ### `mut` cells of a `○` -/

/-- A `mut` cell of `ρ₁ ○ ρ₂` is a cell of an operand, when both operands' `mut` cells are in a
family with one `mut` cell per location. -/
theorem compR_mut_source {A : BoCa.Loc → TCell K → Prop} (hA : MutUniq A) {ρ₁ ρ₂ ρ : TRes K}
    (h : ResUT.CompR ρ₁ ρ₂ ρ) (h₁ : MutIn A ρ₁) (h₂ : MutIn A ρ₂) {n : BoCa.Loc} {φ : TCell K}
    (e : ρ.get n = some φ) (hk : φ.kind = Kind.mut) :
    ρ₁.get n = some φ ∨ ρ₂.get n = some φ := by
  rcases G.Comp.get h n with ⟨-, -, e'⟩ | ⟨ζ, e₁, -, e'⟩ | ⟨ζ, -, e₂, e'⟩ |
      ⟨ζ₁, ζ₂, ζ, e₁, e₂, e', hc⟩
  · rw [e'] at e; cases e
  · rw [e'] at e; cases e; exact Or.inl e₁
  · rw [e'] at e; cases e; exact Or.inr e₂
  · rw [e'] at e; cases e
    rcases mutKeep_compR _ _ _ hc hk (fun k₁ k₂ => hA n _ _ (h₁ n _ e₁ k₁) (h₂ n _ e₂ k₂) k₁ k₂)
      with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact Or.inl e₁
    · exact Or.inr e₂

/-- The same along `⨀`. -/
theorem bigCompR_mut_source {A : BoCa.Loc → TCell K → Prop} (hA : MutUniq A) :
    ∀ {xs : List (TRes K)} {b : TRes K}, G.BigComp CellUT.CompatR CellUT.CompR xs b →
      (∀ x ∈ xs, MutIn A x) → ∀ {n : BoCa.Loc} {φ : TCell K}, b.get n = some φ →
      φ.kind = Kind.mut → ∃ x ∈ xs, x.get n = some φ := by
  intro xs b h
  induction h with
  | nil => intro _ n φ e; simp at e
  | cons hrest hc ih =>
      intro hx n φ e hk
      have hrest' := MutIn.bigComp mutKeep_compR hA hrest
        (fun x hx' => hx x (List.mem_cons_of_mem _ hx'))
      rcases compR_mut_source hA hc (hx _ List.mem_cons_self) hrest' e hk with e₁ | e₂
      · exact ⟨_, List.mem_cons_self, e₁⟩
      · obtain ⟨x, hx', ex⟩ := ih (fun x hx' => hx x (List.mem_cons_of_mem _ hx')) e₂ hk
        exact ⟨x, List.mem_cons_of_mem _ hx', ex⟩

/-! ### `Beneath` along `○` -/

/-- **A `Beneath` lifts to a `○`-composite**: the composite's cell at the ancestor's location is
`imm` with the ancestor's witness. -/
theorem Beneath.lift {p z σ : TRes K} (hc : ResUT.CompR p z σ) {m n : BoCa.Loc} {ζ ξ : TCell K}
    (h : Beneath p m ζ n ξ) :
    ∃ ζ', σ.get m = some ζ' ∧ ζ'.kind = Kind.imm ∧ ζ'.wit = ζ.wit ∧ ζ'.erase = ζ.erase ∧
      Beneath σ m ζ' n ξ := by
  obtain ⟨e, hk, ev, av, q, hev, hav, hq, hn⟩ := h
  obtain ⟨s, hs, heta⟩ := CellUT.imm_eta hk
  rw [heta] at e
  obtain ⟨s', h', hσ⟩ := ResUT.CompR.imm_left_get hc e
  have hw : (CellUT.immOf s' ζ.erase ζ.wit h').wit = ζ.wit := CellUT.wit_immOf ..
  exact ⟨_, hσ, CellUT.kind_immOf .., hw, by simp, hσ, CellUT.kind_immOf .., ev, av, q,
    by rw [CellUT.wit_immOf]; exact hev, by rw [CellUT.wit_immOf]; exact hav, hq, hn⟩

/-- The same as the right operand. -/
theorem Beneath.lift_right {p z σ : TRes K} (hc : ResUT.CompR z p σ) {m n : BoCa.Loc}
    {ζ ξ : TCell K} (h : Beneath p m ζ n ξ) :
    ∃ ζ', σ.get m = some ζ' ∧ ζ'.kind = Kind.imm ∧ ζ'.wit = ζ.wit ∧ ζ'.erase = ζ.erase ∧
      Beneath σ m ζ' n ξ :=
  Beneath.lift (ResUT.CompR.comm hc) h

/-! ### The ancestor of a `mut` cell of the aliasable walk -/

/-- **Every `mut` cell of `ag(ρ)` sits beneath an `imm` cell of `ag(ρ)` whose witness's `⦇−⦈_○`
carries it**, when `ρ`'s `mut` cells at depth are cells of a world with one `mut` cell per
location. `AgWT.nonimm_beneath_imm`'s induction, `○` keeping `mut` cells (`mutKeep_compR`): the
`mut` cell is followed into the operand that carries it, not to a cell with its value and
witness. -/
theorem AgW.mut_beneath {W : TRes K} (hW : MutOne W) {ρ σ : TRes K} (h : AgWT ρ σ)
    (hsub : ∀ y φ, CellAt ρ y φ → φ.kind = Kind.mut → CellAt W y φ) :
    ∀ n φ, σ.get n = some φ → φ.kind = Kind.mut → ∃ m ζ, Beneath σ m ζ n φ := by
  have hR : ∀ ψ₁ ψ₂ ψ : TCell K, CellUT.CompR ψ₁ ψ₂ ψ → CellUT.CompatR ψ₁ ψ₂ :=
    fun _ _ ψ hc => ⟨ψ, hc⟩
  refine (G.AgW.rec
    (motive_1 := fun ρ σ _ => (∀ y φ, CellAt ρ y φ → φ.kind = Kind.mut → CellAt W y φ) →
      MutIn (CellAt ρ) σ ∧
        ∀ n φ, σ.get n = some φ → φ.kind = Kind.mut → ∃ m ζ, Beneath σ m ζ n φ)
    (motive_2 := fun ρ w _ => (∀ y φ, CellAt ρ y φ → φ.kind = Kind.mut → CellAt W y φ) →
      ∀ q ∈ w, MutIn (CellAt ρ) q.2 ∧
        ∀ n φ, q.2.get n = some φ → φ.kind = Kind.mut → ∃ m ζ, Beneath q.2 m ζ n φ)
    (motive_3 := fun ρ w _ => (∀ y φ, CellAt ρ y φ → φ.kind = Kind.mut → CellAt W y φ) →
      ∀ q ∈ w, MutIn (CellAt ρ) q.2 ∧ ∃ ζ, ρ.get q.1 = some ζ ∧ ζ.kind = Kind.imm ∧
        ∃ ev av, ExRT ζ.wit ev ∧ AgWT ζ.wit av ∧ ResUT.CompR ev av q.2)
    ?mk ?nilM ?consM ?nilI ?consI h hsub).2
  case mk =>
    intro ρ₀ σ₀ a bm bi wm wi _ _ _ _ hbm hbi ha hσ ihm ihi hsub
    have hu := MutUniq.of_sub hW hsub
    have hm : ∀ x ∈ wm.map Prod.snd, MutIn (CellAt ρ₀) x := fun x hx => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
      exact (ihm hsub q hq).1
    have hi : ∀ x ∈ wi.map Prod.snd, MutIn (CellAt ρ₀) x := fun x hx => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
      exact (ihi hsub q hq).1
    have hbm' : MutIn (CellAt ρ₀) bm := MutIn.bigComp mutKeep_compR hu hbm hm
    have hbi' : MutIn (CellAt ρ₀) bi := MutIn.bigComp mutKeep_compR hu hbi hi
    have hr' := MutIn.restrict ρ₀ Kind.imm
    have ha' : MutIn (CellAt ρ₀) a := MutIn.comp mutKeep_compR hu ha hr' hbm'
    refine ⟨MutIn.comp mutKeep_compR hu hσ ha' hbi', fun n φ e hk => ?_⟩
    rcases compR_mut_source hu hσ ha' hbi' e hk with ea | eb
    · rcases compR_mut_source hu ha hr' hbm' ea hk with er | em
      · rw [(ResUT.restrict_eq_some.mp er).2] at hk; cases hk
      · obtain ⟨x, hx, ex⟩ := bigCompR_mut_source hu hbm hm em hk
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
        obtain ⟨m, ζ, hb⟩ := (ihm hsub q hq).2 n φ ex hk
        obtain ⟨z, hz⟩ := BigCompT.mem_factor hR ResUT.compLawsR hbm q.2 hx
        obtain ⟨y₁, hy₁⟩ := ResUT.Comp.factor_trans hR ResUT.compLawsR hz (ResUT.CompR.comm ha)
        obtain ⟨y₂, hy₂⟩ := ResUT.Comp.factor_trans hR ResUT.compLawsR hy₁ hσ
        obtain ⟨ζ', -, -, -, -, hb'⟩ := hb.lift hy₂
        exact ⟨m, ζ', hb'⟩
    · obtain ⟨x, hx, ex⟩ := bigCompR_mut_source hu hbi hi eb hk
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
      obtain ⟨-, ζ, eζ, hkζ, ev, av, hev, hav, hp⟩ := ihi hsub q hq
      have hb : Beneath (G.restrict CellUT.kind ρ₀ Kind.imm) q.1 ζ n φ :=
        ⟨ResUT.restrict_get_some eζ hkζ, hkζ, ev, av, q.2, hev, hav, hp, ex⟩
      obtain ⟨ζ₁, -, -, hw₁, -, hb₁⟩ := hb.lift ha
      obtain ⟨ζ₂, -, -, hw₂, -, hb₂⟩ := hb₁.lift hσ
      exact ⟨q.1, ζ₂, hb₂⟩
  case nilM => intro _ _ q hq; cases hq
  case consM =>
    intro ρ₀ e l w ψ hψ _ _ _ ihe ihw hsub q hq
    rcases List.mem_cons.mp hq with rfl | hq'
    · obtain ⟨h₁, h₂⟩ := ihe fun y φ h k => hsub y φ (.nest hψ h) k
      exact ⟨h₁.mono fun _ _ h => .nest hψ h, h₂⟩
    · exact ihw hsub q hq'
  case nilI => intro _ _ q hq; cases hq
  case consI =>
    intro ρ₀ p l w ψ hψ hk e a hex hag hp _ iha ihw hsub q hq
    rcases List.mem_cons.mp hq with rfl | hq'
    · have hsub' : ∀ y φ, CellAt ψ.wit y φ → φ.kind = Kind.mut → CellAt W y φ :=
        fun y φ h k => hsub y φ (.nest hψ h) k
      have hu := MutUniq.of_sub hW hsub'
      exact ⟨(MutIn.comp mutKeep_compR hu hp (ExW.mutIn mutKeep_compR hW hex hsub')
        (iha hsub').1).mono fun _ _ h => .nest hψ h, ψ, hψ, hk, e, a, hex, hag, hp⟩
    · exact ihw hsub q hq'

/-! ### An `imm` composite and its operands -/

/-- `ψ` is an `imm` cell over `φ`'s value and witness, at a lifetime set at least `φ`'s. -/
def ImmLe (φ ψ : TCell K) : Prop :=
  φ.kind = Kind.imm ∧ ψ.kind = Kind.imm ∧ ψ.erase = φ.erase ∧ ψ.wit = φ.wit ∧
    ∃ s t, φ.lsOf = some s ∧ ψ.lsOf = some t ∧ s.set ⊆ t.set

theorem lsOf_of_imm {ψ : TCell K} (h : ψ.kind = Kind.imm) : ∃ s, ψ.lsOf = some s := by
  cases ψ with
  | own v => simp [CellUT.kind] at h
  | imm i => exact ⟨i.ls, rfl⟩
  | «mut» m => simp [CellUT.kind] at h

/-- **An `imm` operand of `○` is below the composite.** -/
theorem CellUT.CompR.immLe_left {φ₁ φ₂ ψ : TCell K} (h : CellUT.CompR φ₁ φ₂ ψ)
    (hk : φ₁.kind = Kind.imm) : ImmLe φ₁ ψ := by
  obtain ⟨s, hs⟩ := lsOf_of_imm hk
  have hl := h.lsOf_eq
  rw [hk, hs] at hl
  have hkψ : ψ.kind = Kind.imm := by rw [h.kind_eq, hk]; cases φ₂.kind <;> rfl
  refine ⟨hk, hkψ, h.erase.2, by rw [h.wit_eq, if_neg (by rw [hk]; decide)], ?_⟩
  cases hk₂ : φ₂.kind with
  | own => rw [hk₂] at hl; exact ⟨s, s, hs, hl, subset_rfl⟩
  | imm =>
      obtain ⟨t, ht⟩ := lsOf_of_imm hk₂
      rw [hk₂, ht] at hl
      exact ⟨s, s ∪ t, hs, hl, by simp⟩
  | «mut» => rw [hk₂] at hl; exact ⟨s, s, hs, hl, subset_rfl⟩

theorem CellUT.CompR.immLe_right {φ₁ φ₂ ψ : TCell K} (h : CellUT.CompR φ₁ φ₂ ψ)
    (hk : φ₂.kind = Kind.imm) : ImmLe φ₂ ψ :=
  CellUT.CompR.immLe_left (CellUT.CompR.comm h) hk

/-- An `imm` composite has an `imm` operand. -/
theorem CellUT.CompR.imm_operand {φ₁ φ₂ ψ : TCell K} (h : CellUT.CompR φ₁ φ₂ ψ)
    (hk : ψ.kind = Kind.imm) : φ₁.kind = Kind.imm ∨ φ₂.kind = Kind.imm := by
  rw [h.kind_eq] at hk
  cases h₁ : φ₁.kind <;> cases h₂ : φ₂.kind <;> rw [h₁, h₂] at hk <;> simp_all [kcomb]

/-- **The lifetime set of an `imm` composite is the union of its `imm` operands'**: it lies in
any set that contains each of theirs. -/
theorem CellUT.CompR.imm_ls_le {φ₁ φ₂ ψ : TCell K} (h : CellUT.CompR φ₁ φ₂ ψ)
    (hk : ψ.kind = Kind.imm) (T : Finset Life)
    (h₁ : φ₁.kind = Kind.imm → ∃ s, φ₁.lsOf = some s ∧ s.set ⊆ T)
    (h₂ : φ₂.kind = Kind.imm → ∃ s, φ₂.lsOf = some s ∧ s.set ⊆ T) :
    ∃ t, ψ.lsOf = some t ∧ t.set ⊆ T := by
  have hl := h.lsOf_eq
  rw [h.kind_eq] at hk
  cases k₁ : φ₁.kind <;> cases k₂ : φ₂.kind <;> rw [k₁, k₂] at hk hl <;>
    simp only [kcomb, reduceCtorEq] at hk
  · obtain ⟨s, hs, hT⟩ := h₂ k₂; rw [hs] at hl; exact ⟨s, hl, hT⟩
  · obtain ⟨s, hs, hT⟩ := h₁ k₁; rw [hs] at hl; exact ⟨s, hl, hT⟩
  · obtain ⟨s, hs, hT⟩ := h₁ k₁
    obtain ⟨t, ht, hT'⟩ := h₂ k₂
    rw [hs, ht] at hl
    exact ⟨s ∪ t, hl, by simp [Finset.union_subset hT hT']⟩
  · obtain ⟨s, hs, hT⟩ := h₁ k₁; rw [hs] at hl; exact ⟨s, hl, hT⟩
  · obtain ⟨s, hs, hT⟩ := h₂ k₂; rw [hs] at hl; exact ⟨s, hl, hT⟩

variable {Θ : LocTy}

theorem CellAbs.of_le {ψ : TCell K} {χ χ' : TCell K'} (h : CellAbs Θ ψ χ) (h' : ImmLe χ χ') :
    CellAbs Θ ψ χ' := by
  obtain ⟨k₁, -, e, r, s, t, hs, ht, hst⟩ := h
  obtain ⟨-, k₂, e', w', t', u, ht', hu, htu⟩ := h'
  rw [ht] at ht'; cases ht'
  exact ⟨k₁, k₂, e'.trans e, w' ▸ r, s, u, hs, hu, hst.trans htu⟩

/-- An `imm` cell carried by `XCell` to a cell below `χ` is absorbed by `χ`. -/
theorem XCell.abs_of_le {ψ : TCell K} {ψ' χ : TCell K'} (h : XCell Θ ψ ψ')
    (hk : ψ.kind = Kind.imm) (h' : ImmLe ψ' χ) : CellAbs Θ ψ χ := by
  obtain ⟨e, r⟩ := h.2.2 hk
  obtain ⟨s, hs⟩ := lsOf_of_imm hk
  exact CellAbs.of_le ⟨hk, h.1.trans hk, e, r, s, s, hs, (h.lsOf_imm hk).trans hs, subset_rfl⟩ h'

/-- An `imm` cell carried by `XCell` is absorbed by it from the start side. -/
theorem XCell.sub {ψ : TCell K} {ψ' : TCell K'} (h : XCell Θ ψ ψ') (hk : ψ.kind = Kind.imm) :
    CellSub Θ ψ ψ' := by
  obtain ⟨e, r⟩ := h.2.2 hk
  obtain ⟨s, hs⟩ := lsOf_of_imm hk
  exact ⟨hk, h.1.trans hk, e, r, s, s, hs, (h.lsOf_imm hk).trans hs, subset_rfl⟩

theorem CellSub.of_le {ψ ψ₂ : TCell K} {ψ' : TCell K'} (h : ImmLe ψ ψ₂) (h' : CellSub Θ ψ ψ') :
    CellSub Θ ψ₂ ψ' := by
  obtain ⟨-, k₂, e, w, s, u, hs, hu, hsu⟩ := h
  obtain ⟨-, k', e', r, s', t, hs', ht, hts⟩ := h'
  rw [hs] at hs'; cases hs'
  exact ⟨k₂, k', e'.trans e.symm, w ▸ r, u, t, hu, ht, hts.trans hsu⟩

/-- **The end world absorbs an `imm` composite when it absorbs each `imm` operand.** -/
theorem cellAbs_compR {φ₁ φ₂ ψ : TCell K} {χ : TCell K'} (h : CellUT.CompR φ₁ φ₂ ψ)
    (hk : ψ.kind = Kind.imm) (h₁ : φ₁.kind = Kind.imm → CellAbs Θ φ₁ χ)
    (h₂ : φ₂.kind = Kind.imm → CellAbs Θ φ₂ χ) : CellAbs Θ ψ χ := by
  have one : ∀ {φ : TCell K}, ImmLe φ ψ → CellAbs Θ φ χ → CellAbs Θ ψ χ := by
    intro φ hle ha
    obtain ⟨-, kχ, e, r, s, t, -, ht, -⟩ := ha
    obtain ⟨-, -, eψ, wψ, -⟩ := hle
    have ls : ∀ {φ : TCell K}, (φ.kind = Kind.imm → CellAbs Θ φ χ) →
        φ.kind = Kind.imm → ∃ s, φ.lsOf = some s ∧ s.set ⊆ t.set := by
      intro φ hφ k
      obtain ⟨-, -, -, -, s, t', hs, ht', hst⟩ := hφ k
      rw [ht] at ht'; cases ht'
      exact ⟨s, hs, hst⟩
    obtain ⟨u, hu, hut⟩ := CellUT.CompR.imm_ls_le h hk t.set (ls h₁) (ls h₂)
    exact ⟨hk, kχ, e.trans eψ.symm, wψ ▸ r, u, t, hu, ht, hut⟩
  rcases CellUT.CompR.imm_operand h hk with k | k
  · exact one (CellUT.CompR.immLe_left h k) (h₁ k)
  · exact one (CellUT.CompR.immLe_right h k) (h₂ k)

/-- **A start cell absorbs an `imm` composite when it absorbs each `imm` operand.** -/
theorem cellSub_compR {ψ : TCell K} {φ₁ φ₂ ψ' : TCell K'} (h : CellUT.CompR φ₁ φ₂ ψ')
    (hk : ψ'.kind = Kind.imm) (h₁ : φ₁.kind = Kind.imm → CellSub Θ ψ φ₁)
    (h₂ : φ₂.kind = Kind.imm → CellSub Θ ψ φ₂) : CellSub Θ ψ ψ' := by
  have one : ∀ {φ : TCell K'}, ImmLe φ ψ' → CellSub Θ ψ φ → CellSub Θ ψ ψ' := by
    intro φ hle hs
    obtain ⟨kψ, -, e, r, s, -, hs', -, -⟩ := hs
    obtain ⟨-, -, eψ, wψ, -⟩ := hle
    have ls : ∀ {φ : TCell K'}, (φ.kind = Kind.imm → CellSub Θ ψ φ) →
        φ.kind = Kind.imm → ∃ t, φ.lsOf = some t ∧ t.set ⊆ s.set := by
      intro φ hφ k
      obtain ⟨-, -, -, -, s', t, hs'', ht, hts⟩ := hφ k
      rw [hs'] at hs''; cases hs''
      exact ⟨t, ht, hts⟩
    obtain ⟨u, hu, hus⟩ := CellUT.CompR.imm_ls_le h hk s.set (ls h₁) (ls h₂)
    exact ⟨kψ, hk, eψ.trans e, wψ ▸ r, s, u, hs', hu, hus⟩
  rcases CellUT.CompR.imm_operand h hk with k | k
  · exact one (CellUT.CompR.immLe_left h k) (h₁ k)
  · exact one (CellUT.CompR.immLe_right h k) (h₂ k)

theorem ImmLe.refl {ψ : TCell K} (hk : ψ.kind = Kind.imm) : ImmLe ψ ψ := by
  obtain ⟨s, hs⟩ := lsOf_of_imm hk
  exact ⟨hk, hk, rfl, rfl, s, s, hs, hs, subset_rfl⟩

/-! ### Cells of a `○` of resources -/

/-- Where the right operand holds nothing or an `own` cell, a non-`own` left cell is the
composite's. -/
theorem compR_get_left {ρ₁ ρ₂ ρ : TRes K} (h : ResUT.CompR ρ₁ ρ₂ ρ) {l : BoCa.Loc}
    {ψ : TCell K} (e : ρ₁.get l = some ψ) (hk : ψ.kind ≠ Kind.own)
    (h₂ : ∀ φ, ρ₂.get l = some φ → φ.kind = Kind.own) : ρ.get l = some ψ := by
  rcases G.Comp.get h l with ⟨e₁, -, -⟩ | ⟨ζ, e₁, -, e'⟩ | ⟨ζ, e₁, -, -⟩ |
      ⟨ζ₁, ζ₂, ζ, e₁, e₂, e', hc⟩
  · rw [e] at e₁; cases e₁
  · rw [e] at e₁; cases e₁; exact e'
  · rw [e] at e₁; cases e₁
  · rw [e] at e₁; cases e₁
    have ho := h₂ _ e₂
    have hkζ : ζ.kind ≠ Kind.own := by
      rw [CellUT.CompR.kind_eq hc, ho]; cases hψ : ψ.kind <;> simp_all [kcomb]
    rw [e', CellUT.CompR.eq_right_of_own (CellUT.CompR.comm hc) ho hkζ]

theorem compR_get_right {ρ₁ ρ₂ ρ : TRes K} (h : ResUT.CompR ρ₁ ρ₂ ρ) {l : BoCa.Loc}
    {ψ : TCell K} (e : ρ₂.get l = some ψ) (hk : ψ.kind ≠ Kind.own)
    (h₁ : ∀ φ, ρ₁.get l = some φ → φ.kind = Kind.own) : ρ.get l = some ψ :=
  compR_get_left (ResUT.CompR.comm h) e hk h₁

/-- Two equal operand cells are the composite's. -/
theorem compR_get_same {ρ₁ ρ₂ ρ : TRes K} (h : ResUT.CompR ρ₁ ρ₂ ρ) {l : BoCa.Loc}
    {ψ : TCell K} (e₁ : ρ₁.get l = some ψ) (e₂ : ρ₂.get l = some ψ) : ρ.get l = some ψ := by
  rcases G.Comp.get h l with ⟨f, -, -⟩ | ⟨ζ, -, f, -⟩ | ⟨ζ, f, -, -⟩ |
      ⟨ζ₁, ζ₂, ζ, f₁, f₂, e', hc⟩
  · rw [e₁] at f; cases f
  · rw [e₂] at f; cases f
  · rw [e₁] at f; cases f
  · rw [e₁] at f₁; cases f₁; rw [e₂] at f₂; cases f₂
    rw [e', CellUT.CompR.functional hc (CellUT.CompR.same _)]

/-- An `imm` cell of an operand is below the composite's cell. -/
theorem compR_get_imm {ρ₁ ρ₂ ρ : TRes K} (h : ResUT.CompR ρ₁ ρ₂ ρ) {l : BoCa.Loc}
    {φ : TCell K} (e : ρ₁.get l = some φ ∨ ρ₂.get l = some φ) (hk : φ.kind = Kind.imm) :
    ∃ ψ, ρ.get l = some ψ ∧ ImmLe φ ψ := by
  rcases G.Comp.get h l with ⟨f₁, f₂, -⟩ | ⟨ζ, f₁, f₂, e'⟩ | ⟨ζ, f₁, f₂, e'⟩ |
      ⟨ζ₁, ζ₂, ζ, f₁, f₂, e', hc⟩ <;> rcases e with e | e
  · rw [e] at f₁; cases f₁
  · rw [e] at f₂; cases f₂
  · rw [e] at f₁; cases f₁; exact ⟨_, e', ImmLe.refl hk⟩
  · rw [e] at f₂; cases f₂
  · rw [e] at f₁; cases f₁
  · rw [e] at f₂; cases f₂; exact ⟨_, e', ImmLe.refl hk⟩
  · rw [e] at f₁; cases f₁; exact ⟨_, e', CellUT.CompR.immLe_left hc hk⟩
  · rw [e] at f₂; cases f₂; exact ⟨_, e', CellUT.CompR.immLe_right hc hk⟩

/-- `⦇ρ⦈`'s cell where `ag(ρ)` holds an `imm` cell, or any cell `ex(ρ)_●` cannot be `▶◀` with,
is `ag(ρ)`'s. -/
theorem flat_of_ag_imm {ρ e a σ : TRes K} (he : ExST ρ e) (hc : ResUT.CompS e a σ)
    {m : BoCa.Loc} {ζ : TCell K} (hg : a.get m = some ζ) : σ.get m = some ζ := by
  have hen : e.get m = none := by
    cases f : e.get m with
    | none => rfl
    | some ξ => exact absurd (CellUT.CompatS.kinds (hc.1 m ξ ζ f hg)).1 (ExST.immFree he m ξ f)
  rcases G.Comp.get hc m with ⟨-, f, -⟩ | ⟨ξ, f, -, -⟩ | ⟨ξ, -, f, e'⟩ | ⟨ξ₁, ξ₂, ξ, f, -, -, -⟩
  · rw [hg] at f; cases f
  · rw [hen] at f; cases f
  · rw [hg] at f; cases f; exact e'
  · rw [hen] at f; cases f

/-- A `Beneath` read at another resource holding the ancestor. -/
theorem Beneath.of_get {σ τ : TRes K} {m n : BoCa.Loc} {ζ ξ : TCell K} (h : Beneath σ m ζ n ξ)
    (e : τ.get m = some ζ) : Beneath τ m ζ n ξ :=
  ⟨e, h.2⟩

/-! ### The frame -/

/-- **A frame re-read beside an `UpdA` run is kept**, along the walks: `[TR]` 6.48's proof
(`updV_frame`) at `UpdA`. The run `a ↭ a′` beside the end world `fw`, the frame `c` re-read to
`c′`, the end composite `a′ ● c′` a part of `fw`, and the frame holding nothing where only one side
is masked. `MutOne` of a world holding the start composite and of one holding the end composite
(both from `RecInv`, `TWNT.mutOne`) make a `mut` cell of each composite a single contribution.

The cases are `updV_frame`'s aliasable ones, at the framed part's cell.
* An `imm` cell of the start composite is absorbed by the end world: each `imm` operand is
  (`cellAbs_compR`), the run's by the inner clause and the frame's by being re-read into the end
  composite, a part of the end world.
* A `mut` cell of the start composite is the frame's, re-read into the end composite (`MutOne` at
  both ends), or the run's, decided by the inner clause; a run's `mut` cell leaving with its
  ancestor leaves with the ancestor's composite (`Beneath.lift`), which the end world absorbs.
* An `imm` cell of the end composite is absorbed by the start's (`cellSub_compR`).
* A `mut` cell of the end composite is the frame's or the run's. The frame's cell faces an `imm`
  cell of the run's start (the configuration of `not_xoptWFrameAt`) only from `ag(c)`: an
  exclusive `mut` cell is not `▶◀` with an `imm` one. There it sits beneath an `imm` cell of
  `ag(c)` (`AgW.mut_beneath`), which the start composite carries (`Beneath.lift_right`). -/
theorem UpdA.frame (hE : K.Ext K') {E E' : BoCa.Loc → Prop} {a c ac : TRes K}
    {a' c' ac' f' fw : TRes K'} (h : UpdA Θ E E' a a' fw) (hr : RR Θ c c')
    (h₁ : ResUT.CompS a c ac) (h₂ : ResUT.CompS a' c' ac') (hv₁ : ResUT.Valid ac)
    (hw : ResUT.CompS f' ac' fw) (hn : NoneAt (MaskDiff E E') c') {W : TRes K} (hW : MutOne W)
    (hs : ∀ y φ, CellAt ac y φ → φ.kind = Kind.mut → CellAt W y φ) {W' : TRes K'}
    (hW' : MutOne W') (hs' : ∀ y φ, CellAt ac' y φ → φ.kind = Kind.mut → CellAt W' y φ) :
    UpdA Θ E E' ac ac' fw := by
  obtain ⟨σa, σa', τw, hσa, hσa', hτw, hx⟩ := h
  obtain ⟨τ, hτ⟩ := hv₁
  obtain ⟨τ', hτ'⟩ := (ResUT.Valid.split hw ⟨τw, hτw⟩).2
  -- the start's walks: `⦇a ● c⦈ = ex(a)_● ● ex(c)_● ● (ag(a) ○ ag(c))`
  obtain ⟨e₁, e₂, e, g₁, g₂, g, σ₁, σc, he₁, he₂, hec, hg₁, hg₂, hgc, hτc, hσ₁, hσc⟩ :=
    ResUT.Flat.split_factors h₁ hτ
  have fc : ResUT.Flat c σc := ⟨e₂, g₂, he₂, hg₂, hσc⟩
  obtain rfl := ResUT.Flat.functional hσa ⟨e₁, g₁, he₁, hg₁, hσ₁⟩
  obtain ⟨σa₀, σc₀, fa₀, fc₀, hcomp⟩ := BoLo.flat_compR h₁ hτ
  obtain rfl := ResUT.Flat.functional hσa fa₀
  obtain rfl := ResUT.Flat.functional fc fc₀
  obtain ⟨σa₁, σc', fa₁, fc', hcomp'⟩ := BoLo.flat_compR h₂ hτ'
  obtain rfl := ResUT.Flat.functional hσa' fa₁
  obtain ⟨σc₁, fc₁, hsc⟩ := ResUT.Flat.rrLs hE fc hr
  obtain rfl := ResUT.Flat.functional fc' fc₁
  obtain ⟨σf, σw, -, fw', hcw⟩ := BoLo.flat_compR hw hτw
  obtain rfl := ResUT.Flat.functional hτ' fw'
  -- `mut` cells: one per location at each end
  have hsa : ∀ y φ, CellAt a y φ → φ.kind = Kind.mut → CellAt W y φ := fun y φ h k =>
    hs y φ (h.of_compS_left h₁ (kind_mut_ne_imm k)) k
  have hsc' : ∀ y φ, CellAt c y φ → φ.kind = Kind.mut → CellAt W y φ := fun y φ h k =>
    hs y φ (h.of_compS_right h₁ (kind_mut_ne_imm k)) k
  have hma := flat_mut_cellAt hW hsa hσa
  have hmc := flat_mut_cellAt hW hsc' fc
  have mutS : ∀ l φ₁ φ₂, σa.get l = some φ₁ → σc.get l = some φ₂ → φ₁.kind = Kind.mut →
      φ₂.kind = Kind.mut → φ₁ = φ₂ := fun l φ₁ φ₂ e₁ e₂ k₁ k₂ =>
    hW l _ _ (hsa _ _ (hma l _ e₁ k₁) k₁) (hsc' _ _ (hmc l _ e₂ k₂) k₂) k₁ k₂
  have hsa' : ∀ y φ, CellAt a' y φ → φ.kind = Kind.mut → CellAt W' y φ := fun y φ h k =>
    hs' y φ (h.of_compS_left h₂ (kind_mut_ne_imm k)) k
  have hsc'' : ∀ y φ, CellAt c' y φ → φ.kind = Kind.mut → CellAt W' y φ := fun y φ h k =>
    hs' y φ (h.of_compS_right h₂ (kind_mut_ne_imm k)) k
  have hma' := flat_mut_cellAt hW' hsa' hσa'
  have hmc' := flat_mut_cellAt hW' hsc'' fc'
  have mutE : ∀ l φ₁ φ₂, σa'.get l = some φ₁ → σc'.get l = some φ₂ → φ₁.kind = Kind.mut →
      φ₂.kind = Kind.mut → φ₁ = φ₂ := fun l φ₁ φ₂ e₁ e₂ k₁ k₂ =>
    hW' l _ _ (hsa' _ _ (hma' l _ e₁ k₁) k₁) (hsc'' _ _ (hmc' l _ e₂ k₂) k₂) k₁ k₂
  -- the frame's cells and their re-readings
  have reC : ∀ l φ, σc.get l = some φ → ∃ φ', σc'.get l = some φ' ∧ LsSim Θ φ' φ := by
    intro l φ e
    have := hsc l; rw [e] at this
    revert this; cases σc'.get l with
    | none => intro h; cases h
    | some φ' => intro h; cases h with | some h => exact ⟨φ', rfl, h⟩
  have reC' : ∀ l φ', σc'.get l = some φ' → ∃ φ, σc.get l = some φ ∧ LsSim Θ φ' φ := by
    intro l φ' e
    have := hsc l; rw [e] at this
    revert this; cases σc.get l with
    | none => intro h; cases h
    | some φ => intro h; cases h with | some h => exact ⟨φ, rfl, h⟩
  have noneC : ∀ l, σc.get l = none → σc'.get l = none := fun l e => by
    cases f : σc'.get l with
    | none => rfl
    | some φ' => obtain ⟨φ, e', -⟩ := reC' l φ' f; rw [e] at e'; cases e'
  have ownC : ∀ l, (∀ φ, σc.get l = some φ → φ.kind = Kind.own) →
      ∀ φ', σc'.get l = some φ' → φ'.kind = Kind.own := fun l h φ' e' => by
    obtain ⟨φ, e, hs⟩ := reC' l φ' e'; rw [hs.1]; exact h φ e
  have ownC' : ∀ l, (∀ φ', σc'.get l = some φ' → φ'.kind = Kind.own) →
      ∀ φ, σc.get l = some φ → φ.kind = Kind.own := fun l h φ e => by
    obtain ⟨φ', e', hs⟩ := reC l φ e; rw [← hs.1]; exact h φ' e'
  -- the masks where the frame holds a cell
  have hnc : ∀ l φ', σc'.get l = some φ' → ¬ MaskDiff E E' l := fun l φ' e hm => by
    have := hn σc' fc' l hm; rw [e] at this; cases this
  -- the end world absorbs the end composite's `imm` cells
  have absorb : ∀ l ψ', τ'.get l = some ψ' → ψ'.kind = Kind.imm →
      ∃ χ, τw.get l = some χ ∧ ImmLe ψ' χ := fun l ψ' e hk =>
    compR_get_imm hcw (Or.inr e) hk
  -- an `imm` cell of the start composite is absorbed, at an unmasked location
  have absA : ∀ m φ, ¬ E m → σa.get m = some φ → φ.kind = Kind.imm →
      ∃ χ, τw.get m = some χ ∧ CellAbs Θ φ χ := by
    intro m φ hEm e hk
    obtain ⟨-, hd⟩ := (hx m).1 φ e (by rw [hk]; decide) hEm
    rcases hd with ⟨φ', e', hxc⟩ | ha | ⟨hkm, -⟩
    · obtain ⟨ψ', eψ', hle⟩ := compR_get_imm hcomp' (Or.inl e') (hxc.1.trans hk)
      obtain ⟨χ, eχ, hle'⟩ := absorb m ψ' eψ' hle.2.1
      exact ⟨χ, eχ, (hxc.abs_of_le hk hle).of_le hle'⟩
    · exact ha
    · rw [hk] at hkm; cases hkm
  have absC : ∀ m φ, σc.get m = some φ → φ.kind = Kind.imm →
      ∃ χ, τw.get m = some χ ∧ CellAbs Θ φ χ := by
    intro m φ e hk
    obtain ⟨φ', e', hsm⟩ := reC m φ e
    obtain ⟨ψ', eψ', hle⟩ := compR_get_imm hcomp' (Or.inr e') (hsm.1.trans hk)
    obtain ⟨χ, eχ, hle'⟩ := absorb m ψ' eψ' hle.2.1
    exact ⟨χ, eχ, ((LsSim.xcell hsm).abs_of_le hk hle).of_le hle'⟩
  have absorbAt : ∀ m ψ, ¬ E m → τ.get m = some ψ → ψ.kind = Kind.imm →
      ∃ χ, τw.get m = some χ ∧ CellAbs Θ ψ χ := by
    intro m ψ hEm e hk
    rcases G.Comp.get hcomp m with ⟨-, -, f⟩ | ⟨ζ, f₁, -, f⟩ | ⟨ζ, -, f₂, f⟩ |
        ⟨ζ₁, ζ₂, ζ, f₁, f₂, f, hc⟩
    · rw [f] at e; cases e
    · rw [f] at e; cases e; exact absA m _ hEm f₁ hk
    · rw [f] at e; cases e; exact absC m _ f₂ hk
    · rw [f] at e; cases e
      have pick : ∃ χ, τw.get m = some χ := by
        rcases CellUT.CompR.imm_operand hc hk with k | k
        · obtain ⟨χ, eχ, -⟩ := absA m _ hEm f₁ k; exact ⟨χ, eχ⟩
        · obtain ⟨χ, eχ, -⟩ := absC m _ f₂ k; exact ⟨χ, eχ⟩
      obtain ⟨χ, eχ⟩ := pick
      refine ⟨χ, eχ, cellAbs_compR hc hk (fun k => ?_) (fun k => ?_)⟩
      · obtain ⟨χ', eχ', ha⟩ := absA m _ hEm f₁ k
        rw [eχ] at eχ'; cases eχ'; exact ha
      · obtain ⟨χ', eχ', ha⟩ := absC m _ f₂ k
        rw [eχ] at eχ'; cases eχ'; exact ha
  -- an `imm` cell of the end composite is absorbed by the start's
  have preA : ∀ m φ', ¬ E' m → σa'.get m = some φ' → φ'.kind = Kind.imm →
      ∃ φ, σa.get m = some φ ∧ CellSub Θ φ φ' := by
    intro m φ' hEm e hk
    obtain ⟨-, hd⟩ := (hx m).2 φ' e (by rw [hk]; decide) hEm
    rcases hd with ⟨φ, e₀, hxc | hsb⟩ | ⟨hkm, -⟩
    · exact ⟨φ, e₀, hxc.sub (hxc.1.symm.trans hk)⟩
    · exact ⟨φ, e₀, hsb⟩
    · rw [hk] at hkm; cases hkm
  have subAt : ∀ m ψ', ¬ E' m → τ'.get m = some ψ' → ψ'.kind = Kind.imm →
      ∃ ψ, τ.get m = some ψ ∧ CellSub Θ ψ ψ' := by
    intro m ψ' hEm e hk
    have fromA : ∀ φ', σa'.get m = some φ' → φ'.kind = Kind.imm →
        ∃ ψ, τ.get m = some ψ ∧ CellSub Θ ψ φ' := fun φ' e' k => by
      obtain ⟨φ, e₀, hsb⟩ := preA m φ' hEm e' k
      obtain ⟨ψ, eψ, hle⟩ := compR_get_imm hcomp (Or.inl e₀) hsb.1
      exact ⟨ψ, eψ, hsb.of_le hle⟩
    have fromC : ∀ φ', σc'.get m = some φ' → φ'.kind = Kind.imm →
        ∃ ψ, τ.get m = some ψ ∧ CellSub Θ ψ φ' := fun φ' e' k => by
      obtain ⟨φ, e₀, hsm⟩ := reC' m φ' e'
      have kφ : φ.kind = Kind.imm := hsm.1.symm.trans k
      obtain ⟨ψ, eψ, hle⟩ := compR_get_imm hcomp (Or.inr e₀) kφ
      exact ⟨ψ, eψ, ((LsSim.xcell hsm).sub kφ).of_le hle⟩
    rcases G.Comp.get hcomp' m with ⟨-, -, f⟩ | ⟨ζ, f₁, -, f⟩ | ⟨ζ, -, f₂, f⟩ |
        ⟨ζ₁, ζ₂, ζ, f₁, f₂, f, hc⟩
    · rw [f] at e; cases e
    · rw [f] at e; cases e; exact fromA _ f₁ hk
    · rw [f] at e; cases e; exact fromC _ f₂ hk
    · rw [f] at e; cases e
      have pick : ∃ ψ, τ.get m = some ψ := by
        rcases CellUT.CompR.imm_operand hc hk with k | k
        · obtain ⟨ψ, eψ, -⟩ := fromA _ f₁ k; exact ⟨ψ, eψ⟩
        · obtain ⟨ψ, eψ, -⟩ := fromC _ f₂ k; exact ⟨ψ, eψ⟩
      obtain ⟨ψ, eψ⟩ := pick
      refine ⟨ψ, eψ, cellSub_compR hc hk (fun k => ?_) (fun k => ?_)⟩
      · obtain ⟨ψ₀, eψ₀, hsb⟩ := fromA _ f₁ k
        rw [eψ] at eψ₀; cases eψ₀; exact hsb
      · obtain ⟨ψ₀, eψ₀, hsb⟩ := fromC _ f₂ k
        rw [eψ] at eψ₀; cases eψ₀; exact hsb
  -- the composite's cell where the frame holds a `mut` cell is that cell
  have frameMut : ∀ {σ₁ σ₂ σ : TRes K} (_ : ResUT.CompR σ₁ σ₂ σ) {l : BoCa.Loc} {ψ φ : TCell K},
      σ.get l = some ψ → σ₂.get l = some φ → φ.kind = Kind.mut → ψ.kind = Kind.mut →
      (∀ φ₁, σ₁.get l = some φ₁ → φ₁.kind = Kind.mut → φ₁ = φ) → ψ = φ := by
    intro σ₁ σ₂ σ hc l ψ φ eψ e₂ k₂ kψ huniq
    rcases G.Comp.get hc l with ⟨-, f, -⟩ | ⟨ζ, -, f, -⟩ | ⟨ζ, -, f₂, f⟩ |
        ⟨ζ₁, ζ₂, ζ, f₁, f₂, f, hC⟩
    · rw [e₂] at f; cases f
    · rw [e₂] at f; cases f
    · rw [f] at eψ; rw [e₂] at f₂; cases eψ; cases f₂; rfl
    · rw [f] at eψ; rw [e₂] at f₂; cases eψ; cases f₂
      have := CellUT.CompR.kind_eq hC
      rw [kψ, k₂] at this
      cases k₁ : ζ₁.kind with
      | own => exact CellUT.CompR.eq_right_of_own hC k₁ (by rw [kψ]; decide)
      | imm => rw [k₁] at this; cases this
      | «mut» =>
          obtain rfl := huniq ζ₁ f₁ k₁
          exact CellUT.CompR.functional hC (CellUT.CompR.same _)
  -- the composite's cell where the frame holds nothing or an `own` cell is the run's
  have runOf : ∀ {σ₁ σ₂ σ : TRes K} (_ : ResUT.CompR σ₁ σ₂ σ) {l : BoCa.Loc} {ψ : TCell K},
      σ.get l = some ψ → ψ.kind ≠ Kind.own → (∀ φ, σ₂.get l = some φ → φ.kind = Kind.own) →
      σ₁.get l = some ψ := by
    intro σ₁ σ₂ σ hc l ψ eψ hk h₂
    rcases G.Comp.get hc l with ⟨-, -, f⟩ | ⟨ζ, f₁, -, f⟩ | ⟨ζ, -, f₂, f⟩ |
        ⟨ζ₁, ζ₂, ζ, f₁, f₂, f, hC⟩
    · rw [f] at eψ; cases eψ
    · rw [f] at eψ; cases eψ; exact f₁
    · rw [f] at eψ; cases eψ; exact absurd (h₂ _ f₂) hk
    · rw [f] at eψ; cases eψ
      rw [f₁, CellUT.CompR.eq_right_of_own (CellUT.CompR.comm hC) (h₂ _ f₂) hk]
  have frameMut' : ∀ {σ₁ σ₂ σ : TRes K'} (_ : ResUT.CompR σ₁ σ₂ σ) {l : BoCa.Loc}
      {ψ φ : TCell K'}, σ.get l = some ψ → σ₂.get l = some φ → φ.kind = Kind.mut →
      ψ.kind = Kind.mut → (∀ φ₁, σ₁.get l = some φ₁ → φ₁.kind = Kind.mut → φ₁ = φ) →
      ψ = φ := by
    intro σ₁ σ₂ σ hc l ψ φ eψ e₂ k₂ kψ huniq
    rcases G.Comp.get hc l with ⟨-, f, -⟩ | ⟨ζ, -, f, -⟩ | ⟨ζ, -, f₂, f⟩ |
        ⟨ζ₁, ζ₂, ζ, f₁, f₂, f, hC⟩
    · rw [e₂] at f; cases f
    · rw [e₂] at f; cases f
    · rw [f] at eψ; rw [e₂] at f₂; cases eψ; cases f₂; rfl
    · rw [f] at eψ; rw [e₂] at f₂; cases eψ; cases f₂
      have := CellUT.CompR.kind_eq hC
      rw [kψ, k₂] at this
      cases k₁ : ζ₁.kind with
      | own => exact CellUT.CompR.eq_right_of_own hC k₁ (by rw [kψ]; decide)
      | imm => rw [k₁] at this; cases this
      | «mut» =>
          obtain rfl := huniq ζ₁ f₁ k₁
          exact CellUT.CompR.functional hC (CellUT.CompR.same _)
  have runOf' : ∀ {σ₁ σ₂ σ : TRes K'} (_ : ResUT.CompR σ₁ σ₂ σ) {l : BoCa.Loc} {ψ : TCell K'},
      σ.get l = some ψ → ψ.kind ≠ Kind.own → (∀ φ, σ₂.get l = some φ → φ.kind = Kind.own) →
      σ₁.get l = some ψ := by
    intro σ₁ σ₂ σ hc l ψ eψ hk h₂
    rcases G.Comp.get hc l with ⟨-, -, f⟩ | ⟨ζ, f₁, -, f⟩ | ⟨ζ, -, f₂, f⟩ |
        ⟨ζ₁, ζ₂, ζ, f₁, f₂, f, hC⟩
    · rw [f] at eψ; cases eψ
    · rw [f] at eψ; cases eψ; exact f₁
    · rw [f] at eψ; cases eψ; exact absurd (h₂ _ f₂) hk
    · rw [f] at eψ; cases eψ
      rw [f₁, CellUT.CompR.eq_right_of_own (CellUT.CompR.comm hC) (h₂ _ f₂) hk]
  -- an `imm` frame cell makes the composite `imm`
  have immOf : ∀ {σ₁ σ₂ σ : TRes K} (_ : ResUT.CompR σ₁ σ₂ σ) {l : BoCa.Loc} {ψ φ : TCell K},
      σ.get l = some ψ → σ₂.get l = some φ → φ.kind = Kind.imm → ψ.kind = Kind.imm :=
    fun hc _ _ _ eψ e₂ k => by
      obtain ⟨ψ₀, e₀, hle⟩ := compR_get_imm hc (Or.inr e₂) k
      rw [eψ] at e₀; cases e₀; exact hle.2.1
  have immOf' : ∀ {σ₁ σ₂ σ : TRes K'} (_ : ResUT.CompR σ₁ σ₂ σ) {l : BoCa.Loc}
      {ψ φ : TCell K'}, σ.get l = some ψ → σ₂.get l = some φ → φ.kind = Kind.imm →
      ψ.kind = Kind.imm :=
    fun hc _ _ _ eψ e₂ k => by
      obtain ⟨ψ₀, e₀, hle⟩ := compR_get_imm hc (Or.inr e₂) k
      rw [eψ] at e₀; cases e₀; exact hle.2.1
  refine ⟨τ, τ', τw, hτ, hτ', hτw, fun l => ⟨fun ψ eψ hk hEl => ?_, fun ψ' eψ hk hEl => ?_⟩⟩
  · ------------------------------------------------------------------ the start side
    have hE' : ¬ E' l := by
      cases fc₀ : σc.get l with
      | some φ =>
          obtain ⟨φ', e', -⟩ := reC l φ fc₀
          exact fun c => hnc l φ' e' (Or.inr ⟨c, hEl⟩)
      | none =>
          exact ((hx l).1 ψ (runOf hcomp eψ hk (fun φ c => by rw [fc₀] at c; cases c)) hk
            hEl).1
    refine ⟨hE', ?_⟩
    rcases (show ψ.kind = Kind.imm ∨ ψ.kind = Kind.mut by
        cases h : ψ.kind with
        | own => exact absurd h hk
        | imm => exact Or.inl rfl
        | «mut» => exact Or.inr rfl) with hkψ | hkψ
    · exact Or.inr (Or.inl (absorbAt l ψ hEl eψ hkψ))
    by_cases hcm : ∃ φ, σc.get l = some φ ∧ φ.kind = Kind.mut
    · -- the frame's `mut` cell (start `MutOne`), re-read into the end composite (end `MutOne`)
      obtain ⟨φ, eφ, hkφ⟩ := hcm
      obtain rfl := frameMut hcomp eψ eφ hkφ hkψ
        (fun φ₁ e₁ k₁ => mutS l _ _ e₁ eφ k₁ hkφ)
      obtain ⟨φ', e', hsm⟩ := reC l _ eφ
      have hkφ' : φ'.kind = Kind.mut := hsm.1.trans hkψ
      refine Or.inl ⟨φ', ?_, LsSim.xcell hsm⟩
      have hτ'l : ∃ ψ₀, τ'.get l = some ψ₀ := by
        rcases G.Comp.get hcomp' l with ⟨-, f, -⟩ | ⟨ζ, -, f, -⟩ | ⟨ζ, -, -, f⟩ |
            ⟨ζ₁, ζ₂, ζ, -, -, f, -⟩
        · rw [e'] at f; cases f
        · rw [e'] at f; cases f
        · exact ⟨ζ, f⟩
        · exact ⟨ζ, f⟩
      obtain ⟨ψ₀, eψ₀⟩ := hτ'l
      have hk₀ : ψ₀.kind = Kind.mut := by
        rcases G.Comp.get hcomp' l with ⟨-, f, -⟩ | ⟨ζ, -, f, -⟩ | ⟨ζ, -, f₂, f⟩ |
            ⟨ζ₁, ζ₂, ζ, f₁, f₂, f, hC⟩
        · rw [e'] at f; cases f
        · rw [e'] at f; cases f
        · rw [eψ₀] at f; rw [e'] at f₂; cases f; cases f₂; exact hkφ'
        · rw [eψ₀] at f; rw [e'] at f₂; cases f; cases f₂
          have kc := CellUT.CompR.kind_eq hC
          rw [hkφ'] at kc
          cases k₁ : ζ₁.kind with
          | own => rw [kc, k₁]; rfl
          | «mut» => rw [kc, k₁]; rfl
          | imm =>
              exfalso
              obtain ⟨φa, ea, hsb⟩ := preA l ζ₁ hE' f₁ k₁
              obtain ⟨ψ₁, e₁, hle⟩ := compR_get_imm hcomp (Or.inl ea) hsb.1
              rw [eψ] at e₁; cases e₁; rw [hle.2.1] at hkψ; cases hkψ
      rw [eψ₀, frameMut' hcomp' eψ₀ e' hkφ' hk₀ (fun φ₁ e₁ k₁ => mutE l _ _ e₁ e' k₁ hkφ')]
    · -- the run's cell, the frame holding nothing or an `own` cell
      have hown : ∀ φ, σc.get l = some φ → φ.kind = Kind.own := fun φ eφ => by
        cases k : φ.kind with
        | own => rfl
        | «mut» => exact absurd ⟨φ, eφ, k⟩ hcm
        | imm => rw [immOf hcomp eψ eφ k] at hkψ; cases hkψ
      obtain ⟨-, hd⟩ := (hx l).1 ψ (runOf hcomp eψ hk hown) hk hEl
      rcases hd with ⟨ψ', e', hxc⟩ | ha | ⟨hkm, m, ζ, χ, hEm, hb, -, -⟩
      · exact Or.inl ⟨ψ', compR_get_left hcomp' e' (by rw [hxc.1]; exact hk) (ownC l hown), hxc⟩
      · exact Or.inr (Or.inl ha)
      · obtain ⟨ζ', eζ', hkζ', -, -, hb'⟩ := hb.lift hcomp
        obtain ⟨χ', eχ', ha'⟩ := absorbAt m ζ' hEm eζ' hkζ'
        exact Or.inr (Or.inr ⟨hkm, m, ζ', χ', hEm, hb', eχ', ha'⟩)
  · ------------------------------------------------------------------ the end side
    have hE₀ : ¬ E l := by
      cases fc₀ : σc'.get l with
      | some φ' => exact fun c => hnc l φ' fc₀ (Or.inl ⟨c, hEl⟩)
      | none =>
          exact ((hx l).2 ψ' (runOf' hcomp' eψ hk (fun φ c => by rw [fc₀] at c; cases c)) hk
            hEl).1
    refine ⟨hE₀, ?_⟩
    rcases (show ψ'.kind = Kind.imm ∨ ψ'.kind = Kind.mut by
        cases h : ψ'.kind with
        | own => exact absurd h hk
        | imm => exact Or.inl rfl
        | «mut» => exact Or.inr rfl) with hkψ | hkψ
    · obtain ⟨ψ, eψ₀, hsb⟩ := subAt l ψ' hEl eψ hkψ
      exact Or.inl ⟨ψ, eψ₀, Or.inr hsb⟩
    by_cases hcm : ∃ φ', σc'.get l = some φ' ∧ φ'.kind = Kind.mut
    · -- the frame's `mut` cell (end `MutOne`)
      obtain ⟨φ', eφ', hkφ'⟩ := hcm
      obtain rfl := frameMut' hcomp' eψ eφ' hkφ' hkψ
        (fun φ₁ e₁ k₁ => mutE l _ _ e₁ eφ' k₁ hkφ')
      obtain ⟨φ, eφ, hsm⟩ := reC' l _ eφ'
      have hkφ : φ.kind = Kind.mut := hsm.1.symm.trans hkψ
      have hxc := LsSim.xcell hsm
      cases fa : σa.get l with
      | none =>
          exact Or.inl ⟨φ, compR_get_right hcomp eφ (by rw [hkφ]; decide)
            (fun φ c => by rw [fa] at c; cases c), Or.inl hxc⟩
      | some φa =>
          cases hka : φa.kind with
          | own =>
              exact Or.inl ⟨φ, compR_get_right hcomp eφ (by rw [hkφ]; decide)
                (fun φ c => by rw [fa] at c; cases c; exact hka), Or.inl hxc⟩
          | «mut» =>
              obtain rfl := mutS l _ _ fa eφ hka hkφ
              exact Or.inl ⟨φa, compR_get_same hcomp fa eφ, Or.inl hxc⟩
          | imm =>
              -- the frame's `mut` cell is in `ag(c)`: `ex(c)_●`'s cells are not `▶◀` with the
              -- run's `imm` cell. It sits beneath an `imm` cell of `ag(c)`.
              have hfree : e.ImmFree :=
                ResUT.ImmFree.compS hec (ExST.immFree he₁) (ExST.immFree he₂)
              have he₂l : e₂.get l = none := by
                cases fe : e₂.get l with
                | none => rfl
                | some x =>
                    exfalso
                    have hg₁l := ResUT.ag_eq_flat_at_imm he₁ hσ₁ fa hka
                    obtain ⟨y, ey⟩ : ∃ y, e.get l = some y := by
                      rcases G.Comp.get hec l with ⟨-, f₂, -⟩ | ⟨ζ, -, f₂, -⟩ |
                          ⟨ζ, -, -, f⟩ | ⟨ζ₁, ζ₂, ζ, -, -, f, -⟩
                      · rw [fe] at f₂; cases f₂
                      · rw [fe] at f₂; cases f₂
                      · exact ⟨ζ, f⟩
                      · exact ⟨ζ, f⟩
                    obtain ⟨z, ez⟩ : ∃ z, g.get l = some z := by
                      rcases G.Comp.get hgc l with ⟨f₁, -, -⟩ | ⟨ζ, -, -, f⟩ |
                          ⟨ζ, f₁, -, -⟩ | ⟨ζ₁, ζ₂, ζ, -, -, f, -⟩
                      · rw [hg₁l] at f₁; cases f₁
                      · exact ⟨ζ, f⟩
                      · rw [hg₁l] at f₁; cases f₁
                      · exact ⟨ζ, f⟩
                    exact hfree l y ey (CellUT.CompatS.kinds (hτc.1 l y z ey ez)).1
              have hg₂l : g₂.get l = some φ := by
                rcases G.Comp.get hσc l with ⟨-, -, f⟩ | ⟨ζ, f₁, -, -⟩ | ⟨ζ, -, f₂, f⟩ |
                    ⟨ζ₁, ζ₂, ζ, f₁, -, -, -⟩
                · rw [f] at eφ; cases eφ
                · rw [he₂l] at f₁; cases f₁
                · rw [f] at eφ; cases eφ; exact f₂
                · rw [he₂l] at f₁; cases f₁
              obtain ⟨m, ζ, hb⟩ := AgW.mut_beneath hW hg₂ hsc' l φ hg₂l hkφ
              have hbc : Beneath σc m ζ l φ :=
                hb.of_get (flat_of_ag_imm he₂ hσc hb.1)
              obtain ⟨ζ', -, -, -, -, hb'⟩ := hbc.lift_right hcomp
              exact Or.inr ⟨hkψ, m, ζ', φ, hb', hxc⟩
    · -- the run's cell, the frame holding nothing or an `own` cell
      have hown : ∀ φ', σc'.get l = some φ' → φ'.kind = Kind.own := fun φ' eφ' => by
        cases k : φ'.kind with
        | own => rfl
        | «mut» => exact absurd ⟨φ', eφ', k⟩ hcm
        | imm => rw [immOf' hcomp' eψ eφ' k] at hkψ; cases hkψ
      obtain ⟨-, hd⟩ := (hx l).2 ψ' (runOf' hcomp' eψ hk hown) hk hEl
      rcases hd with ⟨φ, e₀, hxc⟩ | ⟨hkm, m, ζ, ξ, hb, hxc⟩
      · have hkφ : φ.kind ≠ Kind.own := by
          rcases hxc with hxc | hxc
          · exact fun c => hk (hxc.1.trans c)
          · rw [hxc.1]; decide
        exact Or.inl ⟨φ, compR_get_left hcomp e₀ hkφ (ownC' l hown), hxc⟩
      · obtain ⟨ζ', -, -, -, -, hb'⟩ := hb.lift hcomp
        exact Or.inr ⟨hkm, m, ζ', ξ, hb', hxc⟩

end BoCa.Fig16.Tree.Wp

end
