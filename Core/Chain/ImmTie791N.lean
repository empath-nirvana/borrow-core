import Core.Chain.ImmRec791N

/-!
# A tie between the world's `imm` records and a run's records  `[spec §62]`

`scope-791-rule.md` §12. Step 8 of `withload_compatX` needs the source `Imm @a A` cell to be the
cell of a record of the run's list whose type is the source's, up to `TyEq`. §11's
`immAgreeErwp_both` shows that nothing read off the unchanged `erwp` gives this: the cell
`ℓ ↦ imm({α}, loc ℓ′, ℓ′ ↦ own(()))` is the cell of a lend recorded at `Ref 1` (`world_ref`) and
of one recorded at `U (F 1)` (`world_thunk`).

This file states the tie over an abstract record list `ΘI` (the `imm` records a world would carry,
each with the lifetime it was lent at) and checks what it gives and what it excludes.

* `ImmWit ΘI ℓ s u σ A δ`: a record of `ΘI` whose cell is `imm(s, u, σ)` at `ℓ`, lent at a
  lifetime of `s`, at a type `TyEq` to `A` at `δ` (the content of Core's `CohE`, at a record's own
  cell).
* `ImmTie ΘI ls ρ`: every record of `ΘI` whose cell `ρ` holds at a lifetime of `s` is a record of
  `ls`.
* `immTie_agree`: the tie and a witness give a record of the run's list whose cell is the source's
  and whose type is `TyEq` to the source's: steps 6 and 8's agreement at the run's first entry,
  where the typed world's records are `rsOf ls`.
* `immTie_excludes_thunk`: the tie excludes `immAgreeErwp_both`'s second world. A source at
  `Imm @a (Ref 1)` has its witness at `Ref 1` (`immWit_ref`); the tie at `world_thunk`'s list
  fails for it. At `world_ref`'s list it holds (`immTie_ref`).

Where the tie can be placed, and what each placement meets, is §12; `not_effOf_guarded` is the
check for a guard on `cN`'s run clauses.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI.ImmTie791N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa.Fig16.LogRel.Core.Chain.SI.ImmRec791N
open BoCa.Lifetime (LSub LifeVar)

/-- **A witness for an `imm` cell**: a record of `ΘI` whose cell is `imm(s, u, σ)` at `ℓ`, lent
at a lifetime of `s`, at a type `TyEq` to `A` at `δ`. -/
def ImmWit (ΘI : List SRec) (l : Loc) (s : LSet) (u : Val) (σ : WRes) (A : VTy) (δ : LSub) :
    Prop :=
  ∃ x ∈ ΘI, s.mem x.2 ∧ x.1.le = l ∧ x.1.v = u ∧ x.1.R = σ ∧ TyEq A δ x.1.T x.1.δ

/-- **The tie**: every record of `ΘI` whose cell `ρ` holds, at a lifetime of the cell's set, is a
record of the run's list. -/
def ImmTie (ΘI ls : List SRec) (ρ : WRes) : Prop :=
  ∀ x ∈ ΘI, ∀ (s : LSet) (h : x.1.R.InStratum s.join),
    ρ.get x.1.le = some (CellU.immOf s x.1.v x.1.R h) → s.mem x.2 → x.1 ∈ rsOf ls

/-- **Steps 6 and 8's agreement from the tie.** A source cell `imm(s, u, σ)` at `ℓ` of the run's
resource with a witness gives a record of the run's list whose cell is the source's and whose
type is `TyEq` to the source's. -/
theorem immTie_agree {ΘI ls : List SRec} {ρ : WRes} (ht : ImmTie ΘI ls ρ) {l : Loc} {s : LSet}
    {u : Val} {σ : WRes} {h : σ.InStratum s.join} (hg : ρ.get l = some (CellU.immOf s u σ h))
    {A : VTy} {δ : LSub} (hw : ImmWit ΘI l s u σ A δ) :
    ∃ r ∈ rsOf ls, r.le = l ∧ r.v = u ∧ r.R = σ ∧ TyEq A δ r.T r.δ := by
  obtain ⟨x, hx, hs, hle, hv, hR, hT⟩ := hw
  obtain ⟨⟨le, v, R, T, δ₀⟩, α⟩ := x
  simp only at hs hle hv hR hT
  subst hle hv hR
  exact ⟨_, ht _ hx s h hg hs, rfl, rfl, rfl, hT⟩

/-! ### The two worlds of `immAgreeErwp_both` -/

/-- **A witness for the cell at `Imm @a (Ref 1)` is at `Ref 1`**: `TyEq (Ref 1) δ T δ'` holds only
at `T = Ref 1`; so no witness of the cell at that type is the record at `U (F 1)`. -/
theorem immWit_ref {ΘI : List SRec} {l : Loc} {s : LSet} {u : Val} {σ : WRes} {δ : LSub}
    (hw : ImmWit ΘI l s u σ (.ref .unit) δ) :
    ∃ x ∈ ΘI, s.mem x.2 ∧ x.1.le = l ∧ x.1.v = u ∧ x.1.R = σ ∧ x.1.T = .ref .unit := by
  obtain ⟨x, hx, hs, hle, hv, hR, hT⟩ := hw
  refine ⟨x, hx, hs, hle, hv, hR, ?_⟩
  rcases hT' : x.1.T with _ | _ | _ | _ | _ | B | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ <;>
    rw [hT'] at hT <;> simp only [TyEq] at hT
  all_goals first
    | rfl
    | (cases B <;> simp only [TyEq] at hT; rfl)

theorem recT_ne {δ : LSub} {l l' : Loc} :
    recT (.ref .unit) δ l l' ≠ recT (.thunk (.ret .unit)) δ l l' := by
  intro h
  have := congrArg FrameRec.T h
  simp [recT] at this

/-- **The tie excludes `world_thunk`.** The cell's record at `Ref 1`, lent at `α`, is not a record
of the list of the world that recorded the cell at `U (F 1)`. -/
theorem immTie_excludes_thunk (δ : LSub) {l l' : Loc} (α : Life) :
    ¬ ImmTie [(recT (.ref .unit) δ l l', α)] [(recT (.thunk (.ret .unit)) δ l l', α)]
      (cellI α l l') := by
  intro ht
  have h := ht (recT (.ref .unit) δ l l', α) (List.mem_singleton_self _) (LSet.singleton α)
    (escU_inStratum l' _) (ResU.single_get_self _ _) (by simp [LSet.singleton])
  simp only [rsOf, List.map_cons, List.map_nil, List.mem_singleton] at h
  exact recT_ne h

/-- At `world_ref`'s list the tie holds. -/
theorem immTie_ref (δ : LSub) {l l' : Loc} (α : Life) :
    ImmTie [(recT (.ref .unit) δ l l', α)] [(recT (.ref .unit) δ l l', α)] (cellI α l l') := by
  intro x hx _ _ _ _
  simp only [List.mem_singleton] at hx
  subst hx
  simp [rsOf]

/-- **Every source at `Imm @a (Ref 1)` on the cell is excluded from `world_thunk`'s entry**: for
every `ΘI` holding a witness of the cell at `Ref 1`, the tie fails at `world_thunk`'s list, whose
one record is at `U (F 1)`. -/
theorem immTie_wit_excludes_thunk (δ δ' : LSub) {l l' : Loc} (α : Life) {ΘI : List SRec}
    (hw : ImmWit ΘI l (LSet.singleton α) (Val.loc l') (escU l') (.ref .unit) δ') :
    ¬ ImmTie ΘI [(recT (.thunk (.ret .unit)) δ l l', α)] (cellI α l l') := by
  intro ht
  obtain ⟨r, hr, -, -, -, hT⟩ :=
    immTie_agree ht (ResU.single_get_self _ _) (h := escU_inStratum l' _) hw
  simp only [rsOf, List.map_cons, List.map_nil, List.mem_singleton] at hr
  subst hr
  simp [recT, TyEq] at hT

/-! ### A guard on `cN`'s run clauses -/

/-- The trivial run `()` at the post `False` fails at `world_ref`'s entry. -/
theorem not_erwp_false (δ : LSub) {l l' : Loc} (hl : l ≠ l') (α : Life) (Φ : LocFam)
    (hΦ : ImmTieL Φ.imm [(recT (.ref .unit) δ l l', α)]) :
    ¬ erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) (fun _ _ _ _ => False) 1
      [(recT (.ref .unit) δ l l', α)] Val.unit.1 (cellI α l l') := by
  intro h
  rw [erwp_eq] at h
  obtain ⟨hTW, htg, hH, μ, hL, hfd⟩ := world_ref δ hl α
  obtain ⟨ρ', ρp, fρ', fρ'p, π, ps', ls', -, -, -, -, -, -, -, -, -, -, -, -, hq⟩ :=
    h PMap.empty (cellI α l l') [recT (.ref .unit) δ l l'] μ hH (ResU.comp_empty_left _) hTW
      htg hΦ hL hfd 0 μ Val.unit.1 (by decide) (StepsN.refl μ _) (final_val μ Val.unit)
  rcases hq with ⟨w, -, hf⟩ | ⟨K, m, i, v, en, hp⟩ | ⟨K, m, i, v, en, hp⟩
  · exact hf
  · obtain ⟨⟨-, -, hTe, -⟩, -⟩ := pure_sep_iff.mp hp
    cases hTe
  · obtain ⟨⟨-, -, hTe, -⟩, -⟩ := pure_sep_iff.mp hp
    cases hTe

/-- **A guard on `cN`'s run clauses does not keep `cN_effOf`.** Read `cN`'s run clause as
`G ls ρ → erwp …`. At a list and resource where `G` fails, `cN_effOf`'s `↔` would make the run
hold, and the run `()` at the post `False` does not hold at `world_ref`'s entry. -/
theorem not_effOf_guarded (G : List SRec → WRes → Prop) (δ : LSub) {l l' : Loc} (hl : l ≠ l')
    (α : Life) (Φ : LocFam) (hΦ : ImmTieL Φ.imm [(recT (.ref .unit) δ l l', α)])
    (hG : ¬ G [(recT (.ref .unit) δ l l', α)] (cellI α l l')) :
    ¬ ((G [(recT (.ref .unit) δ l l', α)] (cellI α l l') →
        erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) (fun _ _ _ _ => False) 1
          [(recT (.ref .unit) δ l l', α)] Val.unit.1 (cellI α l l')) ↔
      erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) (fun _ _ _ _ => False) 1
        [(recT (.ref .unit) δ l l', α)] Val.unit.1 (cellI α l l')) :=
  fun h => not_erwp_false δ hl α Φ hΦ (h.mp fun hg => absurd hg hG)

/-- The tie at `ΘI` holding the cell's record at `U (F 1)`, read at `world_ref`'s list, is a
guard that fails there: `not_effOf_guarded` applies to it. -/
theorem immTie_guard_fails (δ : LSub) {l l' : Loc} (α : Life) :
    ¬ ImmTie [(recT (.thunk (.ret .unit)) δ l l', α)] [(recT (.ref .unit) δ l l', α)]
      (cellI α l l') := by
  intro ht
  have h := ht (recT (.thunk (.ret .unit)) δ l l', α) (List.mem_singleton_self _)
    (LSet.singleton α) (escU_inStratum l' _) (ResU.single_get_self _ _) (by simp [LSet.singleton])
  simp only [rsOf, List.map_cons, List.map_nil, List.mem_singleton] at h
  exact recT_ne h.symm

end BoCa.Fig16.LogRel.Core.Chain.SI.ImmTie791N

end
