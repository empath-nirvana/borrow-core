import LoopBorrow.Refold
import Core.Stale
import Core.ArrayWp

/-!
# LoopBorrow — a dormant lend, and what a run can hand back

A lend that spans observations is held unfolded between them (`Obstruction.lean`), so the
Kripke order of the state it is held in cannot see its lifetime `α`. A **dormant lend** is
anything that would let it: a record, in the state held between observations, that the lend
is suspended at `α`, so that `Ext` keeps the records longer-lived than `α` fixed.

* **With the freeze, the refold step closes.** `Frozen α ls ls′` is what a borrow cell at `α`
  gives `Ext` (`frozen_of_cellIn`). Given it, the Kripke order of the unfolded state gives the
  Kripke order of the state with the lend folded back in (`ext_refold_of_frozen`), and the
  implication `RefoldKripke` fails at holds (`refoldKripkeD`).
* **No run can install the freeze.** `Ext` sees a lifetime only through a borrow cell
  (`CellIn`), and a borrow cell at the top level of what a run returns is a borrow cell of the
  flattening it started from (`upd_borrow_top`, from `↭`). So from the unfolded lender
  `ℓ ↦ own(w)`, every run hands back a state with no borrow cell (`borrowFree_after_run`), and
  that state's Kripke order admits every list (`ext_of_borrowFree`). `MarkerInstallable` names
  the step a dormant lend built from the existing cells needs; `not_markerInstallable` refutes
  it at the configuration a spanning lend's creation reaches.
* **The refold fails at a list a consumer's frame reaches.** A consumer that borrows a cell
  of its own at `γ`, with `α ⊏ γ ⊏ ⊤`, and observes the loop inside that borrow, runs the
  observation at `[(r, γ)]`. That list is admitted by the unfolded state, is the list of a
  tagged typed world holding the lender (`consumer_frame_world`), and is not admitted by the
  folded state (`refold_not_ext_at_frame`).
* **A lending yield needs a borrow cell at the observation's end.** The same fact of `↭`
  shows that no observation from the unfolded lender returns a `Mut` or `Imm` element
  (`not_lendingYield_mut`, `not_lendingYield_imm`): an observation can hand out only a borrow
  whose cell was in the flattening of the state it started from.

What this shows is where the route stops in this model. It does not show that a spanning lend
is unsound: that is not claimed, and not verified.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.LoopBorrow
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap)

/-! ### The freeze a dormant lend would give -/

/-- The records strictly longer-lived than `α` are the same in `ls` and `ls′`. -/
def Frozen (α : Life) (ls ls' : List SRec) : Prop :=
  ∀ x : SRec, x.2 ⊐ α → (x ∈ ls ↔ x ∈ ls')

/-- The Kripke order of a state that sees a lend suspended at `α`. -/
def ExtD (α : Life) (ls ls' : List SRec) (ρ : WRes) : Prop :=
  Ext ls ls' ρ ∧ Frozen α ls ls'

/-- A borrow cell no longer-lived than `α` gives the freeze: the freeze is what `Ext` reads
off such a cell. -/
theorem frozen_of_cellIn {ls ls' : List SRec} {ρ : WRes} {α : Life} (h : Ext ls ls' ρ)
    (hα : CellIn ρ α) : Frozen α ls ls' :=
  h.2 α hα

/-- **With the freeze, the refolded lend's Kripke order follows from the unfolded state's.**
`ext_refold_of_cellIn` with the freeze in place of a borrow cell. -/
theorem ext_refold_of_frozen {ls ls' : List SRec} {ρr X ρd M : WRes} {l : Loc} {α : Life}
    {w : Val} {χ : WRes} {h : χ.InStratum α} {P : Val → SPropS Loc Val α} {hw : P w ⟨χ, h⟩}
    (hr : ρr.InStratum (↓α))
    (hX : ResU.CompS ρr (ResU.single l (CellU.ownOf w)) X) (hd : ResU.CompS X χ ρd)
    (hM : ResU.CompS ρr (ResU.single l (CellU.mutOf α w χ h P hw)) M)
    (hext : Ext ls ls' ρd) (hfz : Frozen α ls ls') : Ext ls ls' M :=
  ⟨fun r hr' hrel => hext.1 r hr' (rel_refold hX hd hM r hrel),
    fun b hb x hx => hfz x (lt_of_le_of_lt (cellIn_refold hr hM b hb) hx)⟩

/-- `RefoldKripke` with the unfolded state's Kripke order strengthened by the freeze. -/
def RefoldKripkeD : Prop :=
  ∀ (ls ls' : List SRec) (l : Loc) (α : Life) (w : Val),
    ExtD α ls ls' (ResU.single l (CellU.ownOf w)) → Ext ls ls' (mutCell l α w)

/-- `RefoldKripkeD` holds. -/
theorem refoldKripkeD : RefoldKripkeD := by
  intro ls ls' l α w ⟨he, hfz⟩
  exact ext_refold_of_frozen (ρr := PMap.empty) (χ := PMap.empty)
    (ResU.inStratum_empty _) (ResU.comp_empty_left _) (ResU.comp_empty_right _)
    (ResU.comp_empty_left _) he hfz

/-! ### A borrow-free state's Kripke order admits every list -/

/-- `ρ` holds no borrow cell at its top level. -/
def BorrowFree (ρ : WRes) : Prop := ∀ b, ¬ CellIn ρ b

/-- At a borrow-free state, `Ext` holds between any two lists: no record is relevant to it,
and no lifetime is frozen. -/
theorem ext_of_borrowFree {ρ : WRes} (h : BorrowFree ρ) (ls ls' : List SRec) :
    Ext ls ls' ρ :=
  ⟨fun _ _ hrel => by
      obtain ⟨m, ψ, hg, hk, -⟩ := hrel
      exact (h ψ.at ⟨m, ψ, hg, by rw [hk]; exact fun c => Kind.noConfusion c, le_rfl⟩).elim,
    fun b hb => absurd hb (h b)⟩

theorem borrowFree_single_own (l : Loc) (w : Val) :
    BorrowFree (ResU.single l (CellU.ownOf w) : WRes) :=
  fun b => not_cellIn_own l w b

/-! ### What a run hands back -/

/-- The flattening of `ρ` holds no borrow cell. -/
def FlatBorrowFree (ρ : WRes) : Prop := ∀ m ψ, ρ.FlatAt m ψ → ψ.kind = Kind.own

theorem flatBorrowFree_single_own (l : Loc) (w : Val) :
    FlatBorrowFree (ResU.single l (CellU.ownOf w) : WRes) := by
  rintro m ψ ⟨σ, hσ, hg⟩
  rw [ResU.Flat.functional hσ (ResU.flat_single_own l w)] at hg
  by_cases hm : m = l
  · subst hm
    rw [ResU.single_get_self] at hg
    cases Option.some.inj hg
    rfl
  · rw [ResU.single_get_ne _ hm] at hg
    cases hg

/-- **A borrow cell a run hands back was in the flattening it started from.** A borrow cell
at the top level of `ρ′`, a part of `π = ρ′ ● ρ⁺`, puts a borrow cell of the same kind at its
location in `⦇π⦈`; `↭`'s clause of that kind puts one in `⦇ρ⦈`. -/
theorem upd_borrow_top {ρ π ρ' ρp : WRes} (hu : ResU.UpdV ρ π) (hc : ResU.CompS ρ' ρp π)
    {m : Loc} {ψ : CellU Loc Val} (hg : ρ'.get m = some ψ) (hk : ψ.kind ≠ Kind.own) :
    ∃ χ : CellU Loc Val, ρ.FlatAt m χ ∧ χ.kind ≠ Kind.own := by
  obtain ⟨σ', hσ'⟩ := hu.2.2
  rcases CellU.rep ψ with ⟨v, rfl⟩ | ⟨s, v, χ, hs, rfl⟩ | ⟨b, v, χ, hs, P, hw, rfl⟩
  · exact absurd rfl hk
  · obtain ⟨φ, hφ, hkφ⟩ := imm_of_compS_left hc hg (by simp)
    obtain ⟨χ₀, hχ₀, hk₀, -, -⟩ := ResU.Flat.get hσ' hφ
    obtain ⟨s₀, hs₀, e₀⟩ := CellU.imm_eta (hk₀.trans hkφ)
    rw [e₀] at hχ₀
    exact ⟨_, (hu.1.1 m s₀ _ _ hs₀).mpr ⟨σ', hσ', hχ₀⟩, by simp⟩
  · have hkm : (CellU.mutOf b v χ hs P hw).kind ≠ Kind.imm := by simp
    have hπ := (ResU.CompS.get_left_of_ne_imm hc hg hkm).2
    obtain ⟨v', χ', h', hw', hf⟩ :=
      (hu.1.2 m b P).mpr ⟨v, χ, hs, hw, ⟨σ', hσ', ResU.flat_get_of_ne_imm hσ' hπ hkm⟩⟩
    exact ⟨_, hf, by simp⟩

/-- From a state whose flattening holds no borrow cell, at any completion to a tagged typed
world, the run a `wpTS` exhibits hands back a borrow-free state where its postcondition
holds. -/
theorem wpTS_result_borrowFree {ls : List SRec} {e : Expr} {Q : List SRec → Val → WProp}
    {ρ ρf fρ : WRes} {ps : List FrameRec} (hwp : wpTS ls e Q ρ) (hH : ResU.Hash ρf ρ)
    (hc : ResU.CompS ρf ρ fρ) (hT : TW fρ ps (rsOf ls)) (htg : Tagged fρ ps ls)
    (hbf : FlatBorrowFree ρ) : ∃ ls' v ρ', Q ls' v ρ' ∧ BorrowFree ρ' := by
  obtain ⟨ρ', ρp, -, -, π, v, -, -, -, ls', -, -, -, -, -, -, -, h9, h10, -, -, -, -, -, h12⟩ :=
    hwp ρf fρ ps hH hc hT htg Alloc.atCount 0
  refine ⟨ls', v, ρ', h12, fun b hb => ?_⟩
  obtain ⟨m, ψ, hg, hk, -⟩ := hb
  obtain ⟨χ, hf, hkχ⟩ := upd_borrow_top h10 h9 hg hk
  exact hkχ (hbf m χ hf)

/-- The unfolded lender `ℓ ↦ own(w)` alone is a tagged typed world at the empty list. -/
theorem own_completion (l : Loc) (w : Val) :
    ∃ fρ : WRes, ResU.Hash PMap.empty (ResU.single l (CellU.ownOf w)) ∧
      ResU.CompS PMap.empty (ResU.single l (CellU.ownOf w)) fρ ∧ TW fρ [] [] ∧
      Tagged fρ [] [] := by
  obtain ⟨x, σ', hx, hfx, hσ'x, hT, -, -, -⟩ :=
    alloc_world (ρf := PMap.empty) (ρ := PMap.empty) (ps := []) (rs := []) (l := l) w
      Fig16.LogRel.hash_empty (ResU.comp_empty_right _) TW.empty Fig16.BoLo.lower_empty rfl
  obtain rfl := ResU.eq_of_comp_empty_left hx
  exact ⟨σ', hfx, hσ'x, hT, fun y hy => absurd hy (by simp)⟩

/-- **Every run from the unfolded lender hands back a borrow-free state.** -/
theorem borrowFree_after_run (l : Loc) (w : Val) (e : Expr) (Q : List SRec → Val → WProp)
    (hwp : wpTS [] e Q (ResU.single l (CellU.ownOf w))) :
    ∃ ls' v ρ', Q ls' v ρ' ∧ BorrowFree ρ' := by
  obtain ⟨fρ, hH, hc, hT, htg⟩ := own_completion l w
  exact wpTS_result_borrowFree hwp hH hc hT htg (flatBorrowFree_single_own l w)

/-- The step a dormant lend built from the existing cells needs: a run from the unfolded
lender that hands back a state the Kripke order sees `α` in, a borrow cell no longer-lived
than `α`. -/
def MarkerInstallable (l : Loc) (w : Val) (α : Life) : Prop :=
  ∃ (e : Expr) (Q : List SRec → Val → WProp),
    wpTS [] e Q (ResU.single l (CellU.ownOf w)) ∧ ∀ ls v ρ', Q ls v ρ' → CellIn ρ' α

/-- `MarkerInstallable` fails. -/
theorem not_markerInstallable (l : Loc) (w : Val) (α : Life) : ¬ MarkerInstallable l w α := by
  rintro ⟨e, Q, hwp, hQ⟩
  obtain ⟨ls', v, ρ', hq, hbf⟩ := borrowFree_after_run l w e Q hwp
  exact hbf α (hQ ls' v ρ' hq)

/-! ### The list a consumer's frame reaches -/

/-- **A consumer's frame over the unfolded lender is a tagged typed world.** The lender
`ℓ ↦ own(w)`, and a consumer's own cell at `ℓ′` borrowed `imm` at `γ` (`TW.immFrame`, the entry
`withbor1` makes): the frame's cell completes the lender to a typed world whose record list is
`[r]`, tagged `[(r, γ)]`. An observation of the loop inside that borrow runs at this list. -/
theorem consumer_frame_world (l l' : Loc) (hl : l' ≠ l) (w : Val) (γ : Life)
    (δ : Lifetime.LSub) :
    ∃ (ρf fρ : WRes) (r : FrameRec), r.le = l' ∧
      ResU.Hash ρf (ResU.single l (CellU.ownOf w)) ∧
      ResU.CompS ρf (ResU.single l (CellU.ownOf w)) fρ ∧
      TW fρ [r] (rsOf [(r, γ)]) ∧ Tagged fρ [r] [(r, γ)] := by
  classical
  -- the lender
  obtain ⟨x₁, σ₁, hx₁, -, hσ₁, hT₁, hlow₁, -, -⟩ :=
    alloc_world (ρf := PMap.empty) (ρ := PMap.empty) (ps := []) (rs := []) (l := l) w
      Fig16.LogRel.hash_empty (ResU.comp_empty_right _) TW.empty Fig16.BoLo.lower_empty rfl
  obtain rfl := ResU.eq_of_comp_empty_left hx₁
  obtain rfl := ResU.eq_of_comp_empty_left hσ₁
  -- the consumer's own cell
  have hfree : (Heap.upd (fun _ => none) l w) l' = none := by
    simp [Heap.upd, hl]
  obtain ⟨x₂, σ₂, hx₂, hfx₂, hσ₂, hT₂, -, -, -⟩ :=
    alloc_world (ρf := PMap.empty) (l := l') (.unit : Val)
      ⟨hx₁.1, _, hx₁, ResU.valid_single_own l w⟩
      hx₁ hT₁ hlow₁ hfree
  obtain rfl := ResU.eq_of_comp_empty_left hσ₂
  have hvx₂ : ResU.Valid x₂ := (hash_valid hfx₂).2
  -- the frame: `ℓ′ ↦ imm({γ}, (), ∅)` in place of `ℓ′ ↦ own(())`
  have hstr : ResU.InStratum (LSet.singleton γ).join (PMap.empty : WRes) :=
    ResU.inStratum_empty _
  have hown : ResU.Hash (ResU.single l (CellU.ownOf w)) (ResU.single l' (CellU.ownOf (.unit : Val))) :=
    ⟨hx₂.1, x₂, hx₂, hvx₂⟩
  obtain ⟨-, W', hW', hvW'⟩ :=
    ResU.six34 (hs := hstr) (ResU.comp_empty_left (ResU.single l' (CellU.ownOf (.unit : Val)))) hown
  set r : FrameRec := ⟨l', (.unit : Val), PMap.empty, VTy.unit, δ⟩ with hr
  have hX : ResU.CompS (ResU.single l' (CellU.ownOf (.unit : Val))) PMap.empty
      (ResU.single l' (CellU.ownOf (.unit : Val))) := ResU.comp_empty_right _
  have hnodesc : ∀ d, d ∈ ([] : List FrameRec) ↔ Desc r d := by
    intro d
    refine ⟨fun h => absurd h (by simp), ?_⟩
    rintro ⟨p, hp, hlp⟩
    cases hlp with
    | nil => exact absurd rfl hp
    | cons hs _ =>
      obtain ⟨-, -, ζ, e, -⟩ := hs
      simp [hr] at e
  have hT' : TW W' (r :: []) (r :: ([] ++ [])) :=
    TW.immFrame .unit δ hstr hT₂ (fun x hx => absurd hx (by simp [VFree])) hX
      (ResU.CompS.comm hx₂) ⟨rfl, rfl⟩ (ResU.CompS.comm hW') hvW' hnodesc
  obtain ⟨hFL, -⟩ := frameLife_frame .unit δ hvx₂ hX (ResU.CompS.comm hx₂)
    (ResU.CompS.comm hW') hT₂.inv
  refine ⟨_, W', r, rfl, ⟨(ResU.CompS.comm hW').1, W', ResU.CompS.comm hW', hvW'⟩,
    ResU.CompS.comm hW', by simpa [rsOf] using hT', ?_⟩
  intro x hx
  rw [List.mem_singleton] at hx
  subst hx
  exact ⟨r, List.mem_singleton_self r, DescR.refl r, hFL⟩

/-- **The unfolded state admits the consumer's list; the folded state does not.** At a record
tagged `γ` longer-lived than the lend's `α`. -/
theorem refold_not_ext_at_frame (l : Loc) (w : Val) {α γ : Life} (hαγ : α ⊏ γ)
    (r : FrameRec) :
    Ext [] [(r, γ)] (ResU.single l (CellU.ownOf w)) ∧
      ¬ Ext [] [(r, γ)] (mutCell l α w) := by
  refine ⟨ext_of_borrowFree (borrowFree_single_own l w) _ _, fun he => ?_⟩
  have := (he.2 α (cellIn_mutCell l α w) (r, γ) hαγ).mpr (List.mem_singleton_self _)
  simp at this

/-- The configuration at lifetimes `withbor` produces: the lend at `α = 2`, the consumer's
frame at `γ = 1`, both shorter-lived than `⊤ = 0`, so both are lifetimes the `∀'x ⊏ ⊓Δ` of
`withbor`'s callback ranges over at the empty lifetime context. The consumer's list is the list
of a tagged typed world holding the lender, the unfolded state admits it, and the state with
the lend folded back in does not. -/
theorem refold_fails_at_consumer_frame (l l' : Loc) (hl : l' ≠ l) (w : Val)
    (δ : Lifetime.LSub) :
    let α : Life := OrderDual.toDual 2
    let γ : Life := OrderDual.toDual 1
    α ⊏ γ ∧ γ ⊏ ⊤ ∧
    ∃ (ρf fρ : WRes) (r : FrameRec),
      ResU.Hash ρf (ResU.single l (CellU.ownOf w)) ∧
      ResU.CompS ρf (ResU.single l (CellU.ownOf w)) fρ ∧
      TW fρ [r] (rsOf [(r, γ)]) ∧ Tagged fρ [r] [(r, γ)] ∧
      Ext [] [(r, γ)] (ResU.single l (CellU.ownOf w)) ∧ ¬ Ext [] [(r, γ)] (mutCell l α w) := by
  intro α γ
  have hαγ : α ⊏ γ := OrderDual.toDual_lt_toDual.mpr (by decide)
  have hγ : γ ⊏ ⊤ := OrderDual.toDual_lt_toDual.mpr (by decide)
  obtain ⟨ρf, fρ, r, -, hH, hc, hT, htg⟩ := consumer_frame_world l l' hl w γ δ
  exact ⟨hαγ, hγ, ρf, fρ, r, hH, hc, hT, htg, refold_not_ext_at_frame l w hαγ r⟩

/-! ### A lending yield -/

/-- The relation at `Mut a A` holds only at a resource with a borrow cell. -/
theorem cellIn_of_vC_mut {a : Lifetime.Life} {A : VTy} {ls : List SRec} {δ : Lifetime.LSub}
    {v : Val} {ρ : WRes} (h : vC true (.mut a A) ls δ v ρ) : ∃ b, CellIn ρ b := by
  obtain ⟨α, -, ℓ, hs⟩ := h
  obtain ⟨-, hm⟩ := pure_sep_iff.mp hs
  obtain ⟨b, u, σ, hσ, P, hw, ls₀, -, rfl, -⟩ := hm
  exact ⟨b, CellIn.single (ψ := CellU.mutOf b u σ hσ P hw) (by simp)⟩

/-- The relation at `Imm a A` holds only at a resource with a borrow cell. -/
theorem cellIn_of_vC_imm {a : Lifetime.Life} {A : VTy} {ls : List SRec} {δ : Lifetime.LSub}
    {v : Val} {ρ : WRes} (h : vC true (.imm a A) ls δ v ρ) : ∃ b, CellIn ρ b := by
  obtain ⟨α, -, ℓ, hs⟩ := h
  obtain ⟨-, hm⟩ := pure_sep_iff.mp hs
  obtain ⟨s, u, σ, hσ, ls₀, rfl, -⟩ := hm
  exact ⟨_, CellIn.single (ψ := CellU.immOf s u σ hσ) (by simp)⟩

/-- An observation from the unfolded lender that yields a `Mut` element. -/
def LendingYieldMut (l : Loc) (w : Val) (a : Lifetime.Life) (A : VTy) (δ : Lifetime.LSub) :
    Prop :=
  ∃ e : Expr, wpTS [] e (fun ls v => vC true (.mut a A) ls δ v) (ResU.single l (CellU.ownOf w))

/-- An observation from the unfolded lender that yields an `Imm` element. -/
def LendingYieldImm (l : Loc) (w : Val) (a : Lifetime.Life) (A : VTy) (δ : Lifetime.LSub) :
    Prop :=
  ∃ e : Expr, wpTS [] e (fun ls v => vC true (.imm a A) ls δ v) (ResU.single l (CellU.ownOf w))

/-- **No observation from the unfolded lender yields a `Mut` element.** -/
theorem not_lendingYield_mut (l : Loc) (w : Val) (a : Lifetime.Life) (A : VTy)
    (δ : Lifetime.LSub) : ¬ LendingYieldMut l w a A δ := by
  rintro ⟨e, hwp⟩
  obtain ⟨ls', v, ρ', hq, hbf⟩ := borrowFree_after_run l w e _ hwp
  obtain ⟨b, hb⟩ := cellIn_of_vC_mut hq
  exact hbf b hb

/-- **No observation from the unfolded lender yields an `Imm` element.** -/
theorem not_lendingYield_imm (l : Loc) (w : Val) (a : Lifetime.Life) (A : VTy)
    (δ : Lifetime.LSub) : ¬ LendingYieldImm l w a A δ := by
  rintro ⟨e, hwp⟩
  obtain ⟨ls', v, ρ', hq, hbf⟩ := borrowFree_after_run l w e _ hwp
  obtain ⟨b, hb⟩ := cellIn_of_vC_imm hq
  exact hbf b hb

end BoCa.Fig16.LogRel.Core.LoopBorrow

end
