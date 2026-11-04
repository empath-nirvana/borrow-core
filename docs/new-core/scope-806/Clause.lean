import Core.TreeConsume

/-! Scope check for #806: the relaxed clause elaborates, the old `UpdX` implies it, and the last
copy is refused independently of `UpdX`. -/

noncomputable section
variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]
namespace BoCa.Fig16.Tree.Wp
open BoCa BoCa.Fig16 BoCa.Fig16.Tree BoCa.Fig16.BoLo
open BoCa.BoLo (Heap)

variable {K K' : WCactus}

/-- `χ` (at the end) absorbs the `imm` cell `ψ` (at the start), across the re-reading: same
value, witness re-read, lifetime set at least `ψ`'s. Then `ψ'' ● χ = χ` for `ψ`'s re-reading. -/
def CellAbs (Θ : LocTy) (ψ : TCell K) (χ : TCell K') : Prop :=
  ψ.kind = Kind.imm ∧ χ.kind = Kind.imm ∧ χ.erase = ψ.erase ∧ RR Θ ψ.wit χ.wit ∧
    ∃ s t, ψ.lsOf = some s ∧ χ.lsOf = some t ∧ s.set ⊆ t.set

/-- `ψ'` (at the end) is absorbed by `ψ` (at the start): same value, witness re-read, lifetime
set at most `ψ`'s. -/
def CellSub (Θ : LocTy) (ψ : TCell K) (ψ' : TCell K') : Prop :=
  ψ.kind = Kind.imm ∧ ψ'.kind = Kind.imm ∧ ψ'.erase = ψ.erase ∧ RR Θ ψ.wit ψ'.wit ∧
    ∃ s t, ψ.lsOf = some s ∧ ψ'.lsOf = some t ∧ t.set ⊆ s.set

/-- **`XOpt` with the start-side `imm` clause relaxed (design b).** `ow` is the end world's
flattening at the location. An unmasked non-`own` cell of the start is a cell of the end
(`XCell`, as before) or an `imm` cell the end world absorbs. An unmasked non-`own` cell of the
end is a cell of the start (as before) or an `imm` cell a start cell absorbs. -/
def XOptW (Θ : LocTy) (E E' : Prop) (o : Option (TCell K)) (o' ow : Option (TCell K')) : Prop :=
  (∀ ψ, o = some ψ → ψ.kind ≠ Kind.own → ¬ E → ¬ E' ∧
    ((∃ ψ', o' = some ψ' ∧ XCell Θ ψ ψ') ∨ ∃ χ, ow = some χ ∧ CellAbs Θ ψ χ)) ∧
  (∀ ψ', o' = some ψ' → ψ'.kind ≠ Kind.own → ¬ E' → ¬ E ∧
    ∃ ψ, o = some ψ ∧ (XCell Θ ψ ψ' ∨ CellSub Θ ψ ψ'))

/-- **`UpdX` relaxed at the end world `fρ′`.** -/
def UpdXW (Θ : LocTy) (E E' : BoCa.Loc → Prop) (ρ : TRes K) (ρ' fρ' : TRes K') : Prop :=
  ∃ σ σ' τw, ResUT.Flat ρ σ ∧ ResUT.Flat ρ' σ' ∧ ResUT.Flat fρ' τw ∧
    ∀ l, XOptW Θ (E l) (E' l) (σ.get l) (σ'.get l) (τw.get l)

#check @UpdXW

/-- The old clause implies the relaxed one at any valid end world. -/
theorem UpdX.toW {Θ : LocTy} {E E' : BoCa.Loc → Prop} {ρ : TRes K} {ρ' fρ' : TRes K'}
    (h : UpdX Θ E E' ρ ρ') (hv : ResUT.Valid fρ') : UpdXW Θ E E' ρ ρ' fρ' := by
  obtain ⟨σ, σ', hσ, hσ', hx⟩ := h
  obtain ⟨τw, hτw⟩ := hv
  refine ⟨σ, σ', τw, hσ, hσ', hτw, fun l => ⟨fun ψ e hk hE => ?_, fun ψ' e hk hE => ?_⟩⟩
  · obtain ⟨h₁, h₂⟩ := (hx l).1 ψ e hk hE
    exact ⟨h₁, Or.inl h₂⟩
  · obtain ⟨h₁, ψ, e₀, hc⟩ := (hx l).2 ψ' e hk hE
    exact ⟨h₁, ψ, e₀, Or.inl hc⟩

/-- **The last copy cannot be consumed, whatever `↭` says**: the frame owns the record and holds
nothing, the run holds the only copy. The end world is empty and fails `RecInv` (`leInv_view`).
`EndT`'s `UpdX` clause is not read. -/
theorem twp_refuses_last_copy (F : TFrame) (hF : F wE PMap.empty) :
    ¬ twp (ℍ := ℍ) F QGiveUp 1 wE lsOne [] (.val .unit) (viewRes (lfE 1) 1) := by
  intro h
  obtain ⟨W₁, hW₁, hR₁, hI₁⟩ := recWInv_lendStep (lfE 1) (recInv_empty chainP)
    (winv_empty chainP) (l := 1) rfl
  obtain rfl : W₁ = viewRes (lfE 1) 1 :=
    ResUT.CompS.functional (ResUT.CompS.comm hW₁) (ResUT.compS_empty_right _)
  have hc : ResUT.CompS (PMap.empty : TRes wE.K) (viewRes (lfE 1) 1) (viewRes (lfE 1) 1) :=
    ResUT.CompS.comm (ResUT.compS_empty_right _)
  have hfd : FinDom (BoCa.BoLo.Heap.upd (fun _ => none : Heap) 1 BoCa.Val.unit) :=
    ⟨[1], fun l hl => by
      by_cases e : l = 1
      · simp [e]
      · exact absurd (BoCa.BoLo.Heap.upd_other e) hl⟩
  have hS : SplitT [lendRec (K := wE.K) 1] [] [lendRec 1] :=
    ⟨fun p => by simp, fun p hp => by simp at hp⟩
  obtain ⟨w', ρf', ρ', fρ', psF', ps', O', ls', -, hrf, hpsF, -, hc', hS', hR', -, ⟨-, hρ'⟩,
      -, -, -⟩ :=
    h wE (viewRes (lfE 1) 1) PMap.empty (viewRes (lfE 1) 1) lsOne [] [lendRec 1] [lendRec 1] _
      (TWd.Ext.refl _ _) rr_view (.cons ⟨lendRec_rr 1, rfl⟩ .nil) .nil hF
      ⟨hc.1, _, hc, hI₁.valid⟩ hc hS hR₁ hI₁ hfd 0 _ _ (by omega) (.refl _ _)
      (LogRel.Core.final_val _ Val.unit)
  subst hρ'
  obtain rfl := RR.of_empty hrf
  obtain rfl := ResUT.CompS.functional hc' (ResUT.compS_empty_right _)
  obtain _ | ⟨hpp, -⟩ := hpsF
  rename_i p' _
  have hp' : p' ∈ ps' := (hS'.1 p').mpr (Or.inr List.mem_cons_self)
  obtain ⟨ψ, eψ⟩ := leInv_view hR'.1 hp' PMap.empty agW_empty
  simp at eψ

end BoCa.Fig16.Tree.Wp

#print axioms BoCa.Fig16.Tree.Wp.twp_refuses_last_copy
#print axioms BoCa.Fig16.Tree.Wp.UpdX.toW

namespace BoCa.Fig16.Tree.Wp
open BoCa BoCa.Fig16 BoCa.Fig16.Tree BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Kont)

/-- The lender's postcondition: it ends holding `ℓ ↦ own(())`. -/
def QOwnBack : TPost := fun _ _ _ _ _ ρ => ρ = ResUT.single 1 (CellUT.ownOf BoCa.Val.unit)

/-- **A lend does not end while another part holds a live copy**: the lender holds the lend cell
and owns the record, the frame holds a copy; no run ends holding `ℓ ↦ own(())`. The end world
would compose the frame's copy with `own` at `ℓ`. `EndT`'s `UpdX` clause is not read. -/
theorem twp_refuses_lendEnd_live_copy (F : TFrame) (hF : F wE (viewRes (lfE 1) 1)) :
    ¬ twp (ℍ := ℍ) F QOwnBack 1 wE lsOne [lendRec 1] (.val .unit) (viewRes (lfE 1) 1) := by
  intro h
  obtain ⟨W₁, hW₁, hR₁, hI₁⟩ := recWInv_lendStep (lfE 1) (recInv_empty chainP)
    (winv_empty chainP) (l := 1) rfl
  obtain rfl : W₁ = viewRes (lfE 1) 1 :=
    ResUT.CompS.functional (ResUT.CompS.comm hW₁) (ResUT.compS_empty_right _)
  have hdup := viewRes_dup (K := wE.K) (lfE 1) 1
  have hfd : FinDom (BoCa.BoLo.Heap.upd (fun _ => none : Heap) 1 BoCa.Val.unit) :=
    ⟨[1], fun l hl => by
      by_cases e : l = 1
      · simp [e]
      · exact absurd (BoCa.BoLo.Heap.upd_other e) hl⟩
  have hS : SplitT [lendRec (K := wE.K) 1] [lendRec 1] [] :=
    ⟨fun p => by simp, fun p _ q hq => by simp at hq⟩
  obtain ⟨w', ρf', ρ', fρ', psF', ps', O', ls', -, hrf, -, -, hc', -, -, -, hρ', -, -, -⟩ :=
    h wE (viewRes (lfE 1) 1) (viewRes (lfE 1) 1) (viewRes (lfE 1) 1) lsOne [lendRec 1]
      [lendRec 1] [] _ (TWd.Ext.refl _ _) rr_view (.cons ⟨lendRec_rr 1, rfl⟩ .nil)
      (.cons (lendRec_rr 1) .nil) hF ⟨hdup.1, _, hdup, hI₁.valid⟩ hdup hS hR₁ hI₁ hfd 0 _ _
      (by omega) (.refl _ _) (LogRel.Core.final_val _ Val.unit)
  have hρ'' : ρ' = ResUT.single 1 (CellUT.ownOf BoCa.Val.unit) := hρ'
  subst hρ''
  obtain rfl := rr_view_eq hrf
  rcases ResUT.Comp.get hc' 1 with ⟨f, -, -⟩ | ⟨χ, -, f, -⟩ | ⟨χ, f, -, -⟩ |
      ⟨χ₁, χ₂, χ, -, f₂, -, hC⟩
  · simp [viewRes] at f
  · simp at f
  · simp [viewRes] at f
  · rw [ResUT.single_get_self] at f₂
    cases f₂
    obtain ⟨s₁, s₂, v, ρ, h₁, h₂, h₃, -, e₂, -⟩ := hC
    exact absurd (congrArg CellUT.kind e₂) (by simp [CellUT.ownOf, CellUT.kind, CellUT.immOf])

/-- **The admitted consume (design b), as a statement**: a run gives up a copy of a view when
every frame meeting its frame condition holds a copy absorbing it. -/
def HoldsView (Θ : LocTy) (β : Life) (l : BoCa.Loc) {K : WCactus} (ρf : TRes K) : Prop :=
  ∃ τ χ, ResUT.Flat ρf τ ∧ τ.get l = some χ ∧ CellAbs Θ (viewCell (K := K) β) χ

def StmtConsumeFramed : Prop :=
  ∀ (F : TFrame) (Q : TPost) (n : Nat) (w : TWd) (ls : List (SRecT w.K))
    (O : List (FrameRecT w.K)) (e : Expr) (Z ρ : TRes w.K) (β : Life) (l : BoCa.Loc),
    ResUT.CompS Z (viewRes β l) ρ → (∀ w' ρf, F w' ρf → HoldsView (sem w'.Θ) β l ρf) →
    twp (ℍ := ℍ) F Q n w ls O e Z → twp (ℍ := ℍ) F Q n w ls O e ρ

#check @StmtConsumeFramed

end BoCa.Fig16.Tree.Wp
#print axioms BoCa.Fig16.Tree.Wp.twp_refuses_lendEnd_live_copy
