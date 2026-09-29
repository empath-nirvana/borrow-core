import Core.Fundamental

/-!
# LoopBorrow — where a lend over several runs meets the typed world

A borrow over codata has to outlive the run that makes it: the loop is built in one run and
observed in later ones. Two facts of the typed world decide what a proof of that can look
like.

**`↭` brackets every borrow in one run.** `wpTS` relates the resource a run starts at to the
resource it ends at by `↭` (`ResU.UpdV`, 5.27), whose `mut` clause is an equivalence: a `mut`
cell with lifetime `b` and predicate `P̂` is in the flattening at the end iff it is at the
start. So a run that starts holding the lender's cell `ℓ ↦ own(v)` cannot end with
`ℓ ↦ mut(α, …)` anywhere in `ρ′ ● ρ⁺` (`not_upd_of_new_mut`, at singletons
`not_upd_lend_created`), and a run that starts with it cannot end without it
(`not_upd_of_ended_mut`, `not_upd_lend_ended`). The `imm` clause does the same for a frozen
lender (`not_upd_of_new_imm`). The Mut Frame (6.65) meets this by folding and unfolding the
cell inside one run.

**The Kripke order sees a borrow only through a borrow cell.** A thunk's relation holds at
every `ls′` with `Ext ls ls′ ρ` (the `U` clause of `vCE`, and `nuP`). `Ext` keeps fixed the
records strictly longer-lived than a borrow cell of `ρ`. So:

* **Re-pushing a lend at a new depth is harmless when the lend is visible.** If the state held
  between observations has a borrow cell at a lifetime `⊑ α` (`CellIn ρd α`), every `ls′` it
  admits is admitted by the state with the lend folded back in at `α`, whatever frames were
  pushed meanwhile (`ext_of_cellIn`, at the refolded shape `ext_refold_of_cellIn`).
* **It is not harmless when the lend is invisible.** With the lender's cell unfolded, `Ext`
  admits a record tagged longer-lived than `α` that the folded state forbids
  (`ext_unfolded_not_folded`). By the first fact, the state a run hands back cannot hold the
  lend folded, so this is the case a proof meets.

`RefoldKripke` names the implication a proof that re-folds the lend at each observation needs;
`refoldKripke_false` refutes it at the configuration that proof reaches. What this shows is that
this route does not close. It does not show that the rule is unsound: that is not claimed, and
not verified.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core.LoopBorrow
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo

/-! ### `↭` does not let a run create or end a borrow cell -/

/-- A `mut` cell in the flattening at the end of a run that was not at its start breaks `↭`. -/
theorem not_upd_of_new_mut {ρ π : WRes} {l : Loc} {b : Life} {P : Val → SPropS Loc Val b}
    {v : Val} {χ : WRes} {h : χ.InStratum b} {hw : P v ⟨χ, h⟩}
    (hπ : π.FlatAt l (CellU.mutOf b v χ h P hw))
    (hρ : ∀ (v' : Val) (χ' : WRes) (h' : χ'.InStratum b) (hw' : P v' ⟨χ', h'⟩),
      ¬ ρ.FlatAt l (CellU.mutOf b v' χ' h' P hw')) :
    ¬ ResU.Upd ρ π := by
  intro hu
  obtain ⟨v', χ', h', hw', hf⟩ := (hu.2 l b P).mpr ⟨v, χ, h, hw, hπ⟩
  exact hρ v' χ' h' hw' hf

/-- A `mut` cell in the flattening at the start of a run that is not at its end breaks `↭`. -/
theorem not_upd_of_ended_mut {ρ π : WRes} {l : Loc} {b : Life} {P : Val → SPropS Loc Val b}
    {v : Val} {χ : WRes} {h : χ.InStratum b} {hw : P v ⟨χ, h⟩}
    (hρ : ρ.FlatAt l (CellU.mutOf b v χ h P hw))
    (hπ : ∀ (v' : Val) (χ' : WRes) (h' : χ'.InStratum b) (hw' : P v' ⟨χ', h'⟩),
      ¬ π.FlatAt l (CellU.mutOf b v' χ' h' P hw')) :
    ¬ ResU.Upd ρ π := by
  intro hu
  obtain ⟨v', χ', h', hw', hf⟩ := (hu.2 l b P).mp ⟨v, χ, h, hw, hρ⟩
  exact hπ v' χ' h' hw' hf

/-- An `imm` cell in the flattening at the end of a run that was not at its start breaks `↭`. -/
theorem not_upd_of_new_imm {ρ π : WRes} {l : Loc} {s : LSet} {v : Val} {χ : WRes}
    {h : χ.InStratum s.join} (hπ : π.FlatAt l (CellU.immOf s v χ h))
    (hρ : ¬ ρ.FlatAt l (CellU.immOf s v χ h)) : ¬ ResU.Upd ρ π :=
  fun hu => hρ ((hu.1 l s v χ h).mpr hπ)

/-! ### At singletons -/

/-- The trivial stored predicate. -/
abbrev trueP (b : Life) : Val → SPropS Loc Val b := fun _ _ => True

/-- `ℓ ↦ mut(b, v, ∅, ⊤)`: the lender's cell folded, with an empty payload. -/
def mutCell (l : Loc) (b : Life) (v : Val) : WRes :=
  ResU.single l (CellU.mutOf b v PMap.empty (ResU.inStratum_empty b) (trueP b) trivial)

theorem mutCell_valid (l : Loc) (b : Life) (v : Val) : ResU.Valid (mutCell l b v) :=
  ResU.valid_single_mut_of_wit (ResU.comp_empty_left _) (ResU.valid_single_own l v)

theorem mutCell_flatAt (l : Loc) (b : Life) (v : Val) :
    (mutCell l b v).FlatAt l
      (CellU.mutOf b v PMap.empty (ResU.inStratum_empty b) (trueP b) trivial) := by
  obtain ⟨σ, hσ⟩ := mutCell_valid l b v
  exact ⟨σ, hσ, ResU.flat_get_of_ne_imm hσ (ResU.single_get_self _ _)
    (show Kind.mut ≠ Kind.imm by decide)⟩

/-- The flattening of `ℓ ↦ own(v)` has no borrow cell at `ℓ`. -/
theorem own_flatAt_eq {l : Loc} {v : Val} {ψ : CellU Loc Val}
    (h : (ResU.single l (CellU.ownOf v) : WRes).FlatAt l ψ) : ψ = CellU.ownOf v := by
  obtain ⟨σ, hσ, hg⟩ := h
  rw [ResU.Flat.functional hσ (ResU.flat_single_own l v), ResU.single_get_self] at hg
  exact (Option.some.inj hg).symm

theorem mutOf_ne_ownOf {b : Life} {v w : Val} {χ : WRes} {h : χ.InStratum b}
    {P : Val → SPropS Loc Val b} {hw : P v ⟨χ, h⟩} : CellU.mutOf b v χ h P hw ≠ CellU.ownOf w :=
  fun e => by
    have := congrArg CellU.kind e
    rw [CellU.kind_mutOf, CellU.kind_ownOf] at this
    exact Kind.noConfusion this

/-- A run that starts holding the lender `ℓ ↦ own(v)` and ends with the lend `ℓ ↦ mut(b, …)`
breaks `↭`: the lend cannot outlive the run that makes it. -/
theorem not_upd_lend_created (l : Loc) (b : Life) (v w : Val) :
    ¬ ResU.Upd (ResU.single l (CellU.ownOf w)) (mutCell l b v) :=
  not_upd_of_new_mut (mutCell_flatAt l b v)
    (fun _ _ _ _ hf => mutOf_ne_ownOf (own_flatAt_eq hf))

/-- A run that starts with the lend `ℓ ↦ mut(b, …)` and ends with the lender `ℓ ↦ own(w)`
breaks `↭`: a lend cannot end in a later run than the one it was made in. -/
theorem not_upd_lend_ended (l : Loc) (b : Life) (v w : Val) :
    ¬ ResU.Upd (mutCell l b v) (ResU.single l (CellU.ownOf w)) :=
  not_upd_of_ended_mut (mutCell_flatAt l b v)
    (fun _ _ _ _ hf => mutOf_ne_ownOf (own_flatAt_eq hf))

/-! ### The Kripke order and a lend re-pushed at a new depth -/

/-- `↓α ⊏ c` is `α ⊑ c`. -/
theorem down_lt_iff {α c : Life} : (↓α) < c ↔ α ≤ c := by
  show OrderDual.ofDual c < OrderDual.ofDual α + 1 ↔ OrderDual.ofDual c ≤ OrderDual.ofDual α
  omega

/-- **A visible lend survives any list its holder admits.** If the state held between
observations has a borrow cell no longer-lived than `α`, every list extension it admits is
admitted by any state whose borrow cells are at least `α` and whose relevant records are its
own: in particular by the state with the lend re-folded at `α`, whatever frames the consumer
pushed at the new depth. -/
theorem ext_of_cellIn {ls ls' : List SRec} {ρd ρi : WRes} {α : Life}
    (hd : Ext ls ls' ρd) (hα : CellIn ρd α) (hi : ∀ b, CellIn ρi b → α ⊑ b)
    (hk : ∀ r, Rel r ρi → Rel r ρd) : Ext ls ls' ρi :=
  ⟨fun r hr hrel => hd.1 r hr (hk r hrel),
    fun b hb x hx => hd.2 α hα x (lt_of_le_of_lt (hi b hb) hx)⟩

/-- The borrow cells of `ρr ● ℓ ↦ mut(α, …)` are at least `α` when `ρr ∈ Res_{↓α}`. -/
theorem cellIn_refold {ρr M : WRes} {l : Loc} {α : Life} {v : Val} {χ : WRes}
    {h : χ.InStratum α} {P : Val → SPropS Loc Val α} {hw : P v ⟨χ, h⟩}
    (hr : ρr.InStratum (↓α)) (hM : ResU.CompS ρr (ResU.single l (CellU.mutOf α v χ h P hw)) M) :
    ∀ b, CellIn M b → α ⊑ b := by
  classical
  rintro b ⟨m, ψ, hg, hk, hle⟩
  refine le_trans ?_ hle
  by_cases hml : m = l
  · subst hml
    have hkm : (CellU.mutOf α v χ h P hw).kind ≠ Kind.imm := by
      rw [CellU.kind_mutOf]; exact fun c => Kind.noConfusion c
    have hMl := (ResU.CompS.get_left_of_ne_imm (ResU.CompS.comm hM)
      (ResU.single_get_self _ _) hkm).2
    rw [hMl] at hg
    cases Option.some.inj hg
    exact le_rfl
  · have hrm : ρr.get m = some ψ := by
      rw [← ResU.Comp.get_of_right_none hM (ResU.single_get_ne _ hml)]; exact hg
    have hs := hr m ψ hrm
    exact down_lt_iff.mp (by
      cases ψ with
      | own _ => exact absurd rfl hk
      | imm i => exact hs
      | «mut» mm => exact hs)

/-- An `imm` cell of an operand leaves an `imm` cell at its location in the composite. -/
theorem imm_of_compS_left {ρ₁ ρ₂ ρ : WRes} (h : ResU.CompS ρ₁ ρ₂ ρ) {m : Loc}
    {ψ : CellU Loc Val} (hg : ρ₁.get m = some ψ) (hk : ψ.kind = Kind.imm) :
    ∃ ψ', ρ.get m = some ψ' ∧ ψ'.kind = Kind.imm := by
  rcases ResU.Comp.get h m with ⟨e₁, -, -⟩ | ⟨φ, e₁, -, e⟩ | ⟨φ, e₁, -, -⟩ |
      ⟨φ₁, φ₂, φ, e₁, -, e, hC⟩
  · rw [hg] at e₁; cases e₁
  · rw [hg] at e₁; cases Option.some.inj e₁; exact ⟨_, e, hk⟩
  · rw [hg] at e₁; cases e₁
  · exact ⟨φ, e, CellU.CompS.kind hC⟩

/-- The records relevant to `ρr ● ℓ ↦ mut(…)` are relevant to `ρr ● ℓ ↦ own(w) ● χ`. -/
theorem rel_refold {ρr X ρd M : WRes} {l : Loc} {α : Life} {w : Val} {χ : WRes}
    {h : χ.InStratum α} {P : Val → SPropS Loc Val α} {hw : P w ⟨χ, h⟩}
    (hX : ResU.CompS ρr (ResU.single l (CellU.ownOf w)) X) (hd : ResU.CompS X χ ρd)
    (hM : ResU.CompS ρr (ResU.single l (CellU.mutOf α w χ h P hw)) M) :
    ∀ r, Rel r M → Rel r ρd := by
  classical
  rintro r ⟨m, ψ, hg, hk, hpos⟩
  have hml : m ≠ l := by
    rintro rfl
    have hkm : (CellU.mutOf α w χ h P hw).kind ≠ Kind.imm := by
      rw [CellU.kind_mutOf]; exact fun c => Kind.noConfusion c
    rw [(ResU.CompS.get_left_of_ne_imm (ResU.CompS.comm hM) (ResU.single_get_self _ _) hkm).2]
      at hg
    cases Option.some.inj hg
    exact hkm hk
  have hrm : ρr.get m = some ψ := by
    rw [← ResU.Comp.get_of_right_none hM (ResU.single_get_ne _ hml)]; exact hg
  obtain ⟨ψ₁, hX₁, hk₁⟩ := imm_of_compS_left hX hrm hk
  obtain ⟨ψ₂, hd₂, hk₂⟩ := imm_of_compS_left hd hX₁ hk₁
  exact ⟨m, ψ₂, hd₂, hk₂, hpos⟩

/-- **The refolded lend's Kripke order, from the unfolded state's.** -/
theorem ext_refold_of_cellIn {ls ls' : List SRec} {ρr X ρd M : WRes} {l : Loc} {α : Life}
    {w : Val} {χ : WRes} {h : χ.InStratum α} {P : Val → SPropS Loc Val α} {hw : P w ⟨χ, h⟩}
    (hr : ρr.InStratum (↓α))
    (hX : ResU.CompS ρr (ResU.single l (CellU.ownOf w)) X) (hd : ResU.CompS X χ ρd)
    (hM : ResU.CompS ρr (ResU.single l (CellU.mutOf α w χ h P hw)) M)
    (hext : Ext ls ls' ρd) (hα : CellIn ρd α) : Ext ls ls' M :=
  ext_of_cellIn hext hα (cellIn_refold hr hM) (rel_refold hX hd hM)

/-- The step a proof that re-folds the lend at each observation needs: the Kripke order of the
unfolded state held between observations gives the Kripke order of the state with the lend
folded back in. -/
def RefoldKripke : Prop :=
  ∀ (ls ls' : List SRec) (l : Loc) (α : Life) (w : Val),
    Ext ls ls' (ResU.single l (CellU.ownOf w)) → Ext ls ls' (mutCell l α w)

/-- `mutCell` holds a borrow cell at its lifetime. -/
theorem cellIn_mutCell (l : Loc) (α : Life) (v : Val) : CellIn (mutCell l α v) α :=
  ⟨l, _, ResU.single_get_self _ _, show Kind.mut ≠ Kind.own by decide, le_rfl⟩

/-- `ℓ ↦ own(w)` holds no borrow cell. -/
theorem not_cellIn_own (l : Loc) (w : Val) (b : Life) :
    ¬ CellIn (ResU.single l (CellU.ownOf w) : WRes) b := by
  rintro ⟨m, ψ, hg, hk, -⟩
  by_cases hm : m = l
  · subst hm
    rw [ResU.single_get_self] at hg
    cases Option.some.inj hg
    exact hk rfl
  · rw [ResU.single_get_ne _ hm] at hg
    cases hg

/-- **The unfolded lend is invisible to the Kripke order.** One record `x`, tagged longer-lived
than the lend's `α`, added to the empty list: the unfolded state admits it, the folded one
does not. -/
theorem ext_unfolded_not_folded (l : Loc) (α : Life) (w : Val) (x : SRec) (hx : x.2 ⊐ α) :
    Ext [] [x] (ResU.single l (CellU.ownOf w)) ∧ ¬ Ext [] [x] (mutCell l α w) := by
  refine ⟨⟨fun r hr _ => by simp [rsOf] at hr, fun b hb => absurd hb (not_cellIn_own l w b)⟩, ?_⟩
  intro he
  have := (he.2 α (cellIn_mutCell l α w) x hx).mpr (List.mem_singleton_self x)
  simp at this

/-- `RefoldKripke` fails, at a record tagged `1` and a lend at `2`: both shorter-lived than
`⊤ = 0`, so lifetimes `withbor` gives. `Dormant.lean` builds the tagged typed world in which a
consumer's frame reaches this list (`refold_fails_at_consumer_frame`). -/
theorem refoldKripke_false : ¬ RefoldKripke := by
  intro h
  let x : SRec := (⟨0, .unit, PMap.empty, .unit, ⟨[]⟩⟩, OrderDual.toDual 1)
  have hx : x.2 ⊐ OrderDual.toDual 2 := by
    show OrderDual.toDual 2 < OrderDual.toDual 1
    exact OrderDual.toDual_lt_toDual.mpr (by decide)
  obtain ⟨h₁, h₂⟩ := ext_unfolded_not_folded 0 (OrderDual.toDual 2) .unit x hx
  exact h₂ (h [] [x] 0 _ .unit h₁)

end BoCa.Fig16.LogRel.Core.LoopBorrow

end
