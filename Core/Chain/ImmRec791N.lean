import Core.Chain.Goal791N

/-!
# The record an `imm` value's reborrow reads, and what an `Imm` clause sees  `[spec §62]`

`withload_compatX`'s steps 6 and 8 (`scope-791-rule.md` §9.1, §10): the chain's reborrow of an
`imm` cell (`erwp_reborrow`, `erwp_reborrowT`; `SI/RebAcrossC.lean`, `SI/RebCancelC.lean`) is
taken at a record `r` of the run's list whose cell the source is, and hands the borrowed
computation the record's canonical image `canon r β` (`SI/TWNC.lean`). The image is fixed by the
record's template, which is chosen at the record's type `r.T`. The callback's argument type is
`Imm̲ 'x A`, at the source's type `A`. Core links the two by `CohE` (`Core/Relation.lean`): the
source's type is the record's, up to `TyEq`, and `CohE` reads the record list.

`WlImage P` is step 8 at an `Imm` clause `P` read, as `vN` is, at the type, the substitution, the
world, the index, the value and the resource only: at a run's first entry, wherever the source
is a record's cell and every premise of `erwp_reborrow` holds, the canonical image is a value of
`Imm̲ 'x A`.

The configuration: one cell `ℓ ↦ imm({α}, loc ℓ', ℓ' ↦ own(()))`. It is the cell of an `imm`
lend of `ℓ ↦ own(loc ℓ')` recorded at the type `Ref 1` (`world_of`, at `T = Ref 1`), and the
cell of one recorded at `U (F 1)` (`world_of`, at `T = U (F 1)`): `vShape (U C)` is `True`, and
both worlds are typed, tagged and lowered. At `U (F 1)` the template is `∅` (`Imm̲ (U C) = Unk`,
whose shape is `emp`), so the canonical image is `∅` at every `β` (`canon_thunk`). Every premise
of `erwp_reborrow` holds there. A clause that admits the cell at `Imm @a (Ref 1)` (as the lend
recorded at `Ref 1` needs) and has no value of `Imm 'x 1` at `∅` refutes `WlImage`
(`not_wlImage`); `vN`'s is one (`not_wlImage_vN`).

An agreement between the world and the source's record, read off a run's first entry
(`ImmAgreeErwp`), does not change this. `erwp`'s first entry is `rwpG`'s, universally quantified
over the typed worlds holding the resource, and no part of `erwp` reads an `imm` record against
the world; so every such agreement holds, at one world, at both records of the cell
(`immAgreeErwp_both`). With the agreement among step 8's premises (`WlImageA`), the same
configuration refutes step 8 (`not_wlImageA`), at `vN`'s clause strengthened by any condition on
the world at the cell (`not_wlImageA_vN`).

This is the step, not the constant: no run of `ConstN (.wl …)` is refuted.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI.ImmRec791N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa.Lifetime (LSub LifeVar)

/-- **Step 8 of `withload_compatX` at an `Imm` clause `P`.** At a run's first entry (`TWNC` at
the list's records, `Tagged`), at a record `r` of the list whose cell is the source `Imm @a A`
value, and with every premise `erwp_reborrow` reads (`hx`, `hS`, `hRβ`, `hshape`, `hβs`), the
image the reborrow hands the borrowed computation, `canon r β`, is a value of `Imm̲ 'x A` at
`δ['x ↦ β]`. -/
def WlImage (P : VTy → LSub → LocTy → Nat → Val → WRes → Prop) : Prop :=
  ∀ (W : WRes) (ps : List FrameRec) (ls : List SRec) (r : FrameRec) (s : LSet)
    (hs : r.R.InStratum s.join) (a : BoCa.Lifetime.Life) (A : VTy) (δ : LSub) (Θ : LocTy)
    (n : Nat) (x : LifeVar) (β : Life),
    TWNC W ps (rsOf ls) → Tagged W ps ls → r ∈ rsOf ls →
    W.get r.le = some (CellU.immOf s r.v r.R hs) →
    ¬ VFree x A → ¬ VFree x r.T → TmplSpec r (tmpl r) → r.R.InStratum β →
    vShape (r.T.immReborrow (.var x)) (r.δ.extend x β) r.v (canon r β) →
    (∀ y, s.mem y → β ⊑ y) →
    P (.imm a A) δ Θ n (Val.loc r.le) (ResU.single r.le (CellU.immOf s r.v r.R hs)) →
    P (A.immReborrow (.var x)) (δ.extend x β) Θ n r.v (canon r β)

/-! ### The cell and its two records -/

/-- The escrow `ℓ′ ↦ own(())`. -/
def escU (l' : Loc) : WRes := ResU.single l' (CellU.ownOf Val.unit)

theorem escU_inStratum (l' : Loc) (b : Life) : (escU l').InStratum b :=
  ResU.inStratum_single l' (by simp)

/-- The record of an `imm` lend of `ℓ ↦ own(loc ℓ′)`, escrow `ℓ′ ↦ own(())`, at the type `T`. -/
def recT (T : VTy) (δ : LSub) (l l' : Loc) : FrameRec := ⟨l, Val.loc l', escU l', T, δ⟩

/-- The lend's cell `ℓ ↦ imm({α}, loc ℓ′, ℓ′ ↦ own(()))`. -/
def cellI (α : Life) (l l' : Loc) : WRes :=
  ResU.single l (CellU.immOf (LSet.singleton α) (Val.loc l') (escU l') (escU_inStratum l' _))

/-- A record whose type has no `GPos` at its value has no proper sub-record. -/
theorem not_desc {r : FrameRec} (h : ∀ m S, ¬ GPos r.R r.T r.v m S) (d : FrameRec) :
    ¬ Desc r d := by
  rintro ⟨p, hp, hl⟩
  cases hl with
  | nil => exact hp rfl
  | cons hsub _ => exact h _ _ hsub.2.1

theorem noGPos_thunk (R : WRes) (C : CTy) (v : Val) (m : Loc) (S : VTy) :
    ¬ GPos R (.thunk C) v m S := by
  intro h
  cases h with
  | here hm => cases hm
  | step hr _ _ => cases hr

theorem noGPos_refUnit (R : WRes) (v : Val) (m : Loc) (S : VTy) :
    ¬ GPos R (.ref .unit) v m S := by
  intro h
  cases h with
  | here hm => cases hm
  | step hr _ hg =>
      cases hr
      cases hg with
      | here hm => cases hm
      | step hr' _ _ => cases hr'

/-- **The lend's world.** From `∅`: allocate `ℓ′ ↦ own(())`, then `ℓ ↦ own(loc ℓ′)`, then the
`imm` frame at `ℓ` recorded at `T` (`TWNC.immFrame`). The world is the cell, at the records
`[recT T δ ℓ ℓ′]`, tagged at `α`, valid and lowered. -/
theorem world_of (T : VTy) (δ : LSub) {l l' : Loc} (hl : l ≠ l') (α : Life)
    (hadm : AdmWf T δ) (hsh : vShape T δ (Val.loc l') (escU l'))
    (hnoD : ∀ d, ¬ Desc (recT T δ l l') d) :
    TWNC (cellI α l l') [recT T δ l l'] (rsOf [(recT T δ l l', α)]) ∧
      Tagged (cellI α l l') [recT T δ l l'] [(recT T δ l l', α)] ∧
      ResU.Hash PMap.empty (cellI α l l') ∧ ∃ μ, ResU.Lower (cellI α l l') μ ∧ FinDom μ := by
  have hc1 : ResU.CompS PMap.empty (escU l') (escU l') := ResU.comp_empty_left _
  have hW1 : TWNC (escU l') [] [] :=
    .alloc .empty lower_empty rfl hc1 (ResU.valid_single_own _ _)
  have hL1 := lower_compS_own hc1 lower_empty (l := l') rfl
  obtain ⟨W₂, hc2⟩ : ∃ W₂, ResU.CompS (escU l') (ResU.single l (CellU.ownOf (Val.loc l'))) W₂ :=
    (ResU.compS_defined_iff _ _).mpr (compatS_single_of_get_none (ResU.single_get_ne _ hl))
  have hμl : (BoCa.BoLo.Heap.upd (fun _ => none) l' Val.unit) l = none := by
    rw [BoCa.BoLo.Heap.upd_other hl]
  have hL2 := lower_compS_own hc2 hL1 hμl
  have hv2 : ResU.Valid W₂ := by obtain ⟨σ, hσ, -⟩ := hL2; exact ⟨σ, hσ⟩
  have hW2 : TWNC W₂ [] [] := .alloc hW1 hL1 hμl hc2 hv2
  have hH2 : ResU.Hash PMap.empty W₂ :=
    ⟨ResU.Compat.of_disjoint (fun _ => Or.inl rfl), W₂, ResU.comp_empty_left _, hv2⟩
  have hHi : ResU.Hash PMap.empty (cellI α l l') := ResU.six34 hc2 hH2
  have hvi : ResU.Valid (cellI α l l') := by
    obtain ⟨-, ρ, hρ, hv⟩ := hHi
    rwa [← ResU.eq_of_comp_empty_left hρ] at hv
  have hX : ResU.CompS (ResU.single l (CellU.ownOf (Val.loc l'))) (escU l') W₂ :=
    ResU.CompS.comm hc2
  have hXZ : ResU.CompS W₂ PMap.empty W₂ := ResU.comp_empty_right _
  have hW' : ResU.CompS (cellI α l l') PMap.empty (cellI α l l') := ResU.comp_empty_right _
  have hTW := TWNC.immFrame (ds := []) T δ (escU_inStratum l' _) hW2 hadm hX hXZ hsh hW' hvi
    (fun d => ⟨fun h => (by cases h), fun h => absurd h (hnoD d)⟩)
  obtain ⟨hFL, -⟩ := frameLife_frame T δ hv2 hX hXZ hW' hW2.inv
  refine ⟨hTW, ?_, hHi, ?_⟩
  · intro y hy
    simp only [List.mem_singleton] at hy
    subst hy
    exact ⟨recT T δ l l', List.mem_singleton_self _, DescR.refl _, hFL⟩
  · obtain ⟨σ, hσ⟩ := hvi
    have hL : ResU.Lower (cellI α l l') (fun x => (σ.get x).map CellU.erase) := ⟨σ, hσ, fun _ => rfl⟩
    exact ⟨_, hL, lower_finDom hL⟩

/-- The world of the lend recorded at `Ref 1`. -/
theorem world_ref (δ : LSub) {l l' : Loc} (hl : l ≠ l') (α : Life) :
    TWNC (cellI α l l') [recT (.ref .unit) δ l l'] (rsOf [(recT (.ref .unit) δ l l', α)]) ∧
      Tagged (cellI α l l') [recT (.ref .unit) δ l l'] [(recT (.ref .unit) δ l l', α)] ∧
      ResU.Hash PMap.empty (cellI α l l') ∧ ∃ μ, ResU.Lower (cellI α l l') μ ∧ FinDom μ :=
  world_of (.ref .unit) δ hl α (fun x h => absurd h (by simp [VFree]))
    ⟨l', Val.unit, pure_sep_mk rfl ⟨_, PMap.empty, ResU.comp_empty_right _, rfl, rfl, rfl⟩⟩
    (not_desc (noGPos_refUnit _ _))

/-- The world of the lend recorded at `U (F 1)`. -/
theorem world_thunk (δ : LSub) {l l' : Loc} (hl : l ≠ l') (α : Life) :
    TWNC (cellI α l l') [recT (.thunk (.ret .unit)) δ l l']
        (rsOf [(recT (.thunk (.ret .unit)) δ l l', α)]) ∧
      Tagged (cellI α l l') [recT (.thunk (.ret .unit)) δ l l']
        [(recT (.thunk (.ret .unit)) δ l l', α)] ∧
      ResU.Hash PMap.empty (cellI α l l') ∧ ∃ μ, ResU.Lower (cellI α l l') μ ∧ FinDom μ :=
  world_of (.thunk (.ret .unit)) δ hl α (fun x h => absurd h (by simp [VFree, CFree])) trivial
    (not_desc (noGPos_thunk _ _ _))

/-! ### The image at `U (F 1)` -/

/-- `∅` is an image of every escrow in `Res_β`. -/
theorem reb_to_empty {β : Life} {R : WRes} (h : R.InStratum β) : ResU.Reb β R PMap.empty :=
  ⟨h, [], PMap.empty, ⟨by simp, fun _ => by simp⟩, BigComp.nil, ⟨R, ResU.comp_empty_left _⟩,
    fun _ _ hm => absurd hm (by simp)⟩

/-- At a record of type `U C`, the template is `∅`: `Imm̲ (U C) = Unk`, whose shape is `emp`. -/
theorem tmpl_thunk {r : FrameRec} {C : CTy} (hT : r.T = .thunk C) : tmpl r = PMap.empty := by
  unfold tmpl
  split
  · rename_i h
    obtain ⟨_, _, _, _, hsh, _⟩ := Classical.choose_spec h
    rw [hT] at hsh
    exact hsh.1
  · rfl

theorem tmplSpec_thunk {r : FrameRec} (hT : r.T = .thunk (.ret .unit)) {β : Life}
    (hR : r.R.InStratum β) (x : LifeVar) : TmplSpec r (tmpl r) := by
  refine tmpl_spec ⟨PMap.empty, β, x, by rw [hT]; simp [VFree, CFree], reb_to_empty hR, ?_, _,
    agW_empty⟩
  rw [hT]
  exact ⟨rfl, trivial⟩

/-- **At a record of type `U C`, the canonical image is `∅`** at every `β`. -/
theorem canon_thunk {r : FrameRec} {C : CTy} (hT : r.T = .thunk C) (β : Life) :
    canon r β = PMap.empty := by
  refine PMap.ext fun m => ?_
  rw [canon, relRes_get, tmpl_thunk hT]
  simp

/-! ### The refutation -/

/-- **An `Imm` clause reading the resource cannot meet step 8.** Let `P` admit the cell
`ℓ ↦ imm({α}, loc ℓ′, ℓ′ ↦ own(()))` at `Imm @a (Ref 1)` (the lend recorded at `Ref 1` hands it
at that type, `world_ref`), and have no value of `Imm 'x 1` at `∅`. At the world of the lend
recorded at `U (F 1)` (`world_thunk`), every premise of `WlImage` holds and the canonical image is
`∅` (`canon_thunk`); so `WlImage P` fails. -/
theorem not_wlImage (P : VTy → LSub → LocTy → Nat → Val → WRes → Prop) {l l' : Loc}
    (hl : l ≠ l') (α : Life) (a : BoCa.Lifetime.Life) (δ : LSub) (Θ : LocTy) (n : Nat)
    (x : LifeVar)
    (h₁ : P (.imm a (.ref .unit)) δ Θ n (Val.loc l) (cellI α l l'))
    (h₂ : ¬ P (.imm (.var x) .unit) (δ.extend x α) Θ n (Val.loc l') PMap.empty) :
    ¬ WlImage P := by
  intro hW
  let r := recT (.thunk (.ret .unit)) LSub.empty l l'
  obtain ⟨hTW, htg, -, -⟩ := world_thunk LSub.empty hl α
  have hT : r.T = .thunk (.ret .unit) := rfl
  have hc := hW (cellI α l l') [r] [(r, α)] r (LSet.singleton α) (escU_inStratum l' _) a
    (.ref .unit) δ Θ n x α hTW htg (by simp [rsOf]) (ResU.single_get_self _ _)
    (by simp [VFree]) (by rw [hT]; simp [VFree, CFree])
    (tmplSpec_thunk hT (escU_inStratum l' α) x) (escU_inStratum l' _)
    (by rw [canon_thunk hT, hT]; exact ⟨rfl, trivial⟩)
    (fun y hy => by simp [LSet.singleton] at hy; subst hy; exact le_refl _) h₁
  rw [canon_thunk hT] at hc
  exact h₂ hc

/-- The world holding the cell's record at `Ref 1` among its `imm` records, and no entry. -/
def ΘRef (δ : LSub) (l l' : Loc) (α : Life) : LocTy :=
  ⟨fun _ _ => none, [(recT (.ref .unit) δ l l', α)]⟩

/-- `vN`'s `Imm` clause admits the cell at `Imm @a (Ref 1)`, at the world holding its record. -/
theorem vN_cellI (x : LifeVar) (α : Life) (l l' : Loc) (n : Nat) :
    vN (ℍ := ℍ) (.imm (.var x) (.ref .unit)) (LSub.empty.extend x α)
      (ΘRef (LSub.empty.extend x α) l l' α) n (Val.loc l) (cellI α l l') := by
  refine ⟨α, interp_ext_self _ x α, ⟨l, LSet.singleton α, Val.loc l', escU l',
    escU_inStratum l' _, rfl, rfl, le_refl _, l', Val.unit, PMap.empty, rfl,
    ResU.comp_empty_right _, rfl, rfl⟩, fun l₀ hl₀ => ?_⟩
  obtain rfl : l₀ = l := by
    have := congrArg Subtype.val hl₀
    simpa [Val.loc] using this.symm
  exact ⟨_, List.mem_singleton_self _, _, DescR.refl _, .ref .unit, LSub.empty.extend x α,
    TyEq.refl _ _, Or.inl ⟨_, List.mem_singleton_self _, rfl, rfl, fun _ _ => rfl⟩⟩

/-- `vN` has no value of an `Imm` type at `∅`. -/
theorem not_vN_imm_empty (a : BoCa.Lifetime.Life) (A : VTy) (δ : LSub) (Θ : LocTy) (n : Nat)
    (v : Val) : ¬ vN (ℍ := ℍ) (.imm a A) δ Θ n v PMap.empty := by
  rintro ⟨-, -, ⟨m, s, u, σ, hs, -, hρ, -⟩, -⟩
  have := congrArg (fun ρ : WRes => ρ.get m) hρ
  simp at this

/-- **`vN`'s `Imm` clause alone does not meet step 8**, at `ℓ = 0`, `ℓ′ = 1`, `α = 1`: `WlImage`
has no entry tie, and the run it reads may be entered at `world_thunk`'s list. -/
theorem not_wlImage_vN : ¬ WlImage (fun A δ Θ n v ρ => vN (ℍ := ℍ) A δ Θ n v ρ) :=
  not_wlImage _ (l := 0) (l' := 1) (by decide) 1 (.var 0) (LSub.empty.extend 0 1)
    (ΘRef (LSub.empty.extend 0 1) 0 1 1) 0 1
    (vN_cellI 0 1 0 1 0) (not_vN_imm_empty _ _ _ _ _ _)

/-! ### An agreement between the world and a record, read off a run's first entry -/

/-- **An `imm` consistency fact from `erwp`.** `Agree Θ ℓ T δ` relates the world `Θ` to the type
`T` (at `δ`) of a record whose cell is at `ℓ`. The fact: at the first entry of every run `erwp`
(at the view `Θ.view c`) from a resource holding a record's `imm` cell, the world agrees with
the record's type. The entry is `rwpG`'s: a frame `#`-valid with the resource, the composite a
`TWNC` world at the list's records, tagged. -/
def ImmAgreeErwp (Agree : LocTy → Loc → VTy → LSub → Prop) : Prop :=
  ∀ (Θ : LocTy) (c : Loc → Option Life) (Tb : TableN) (Q : PostN) (n : Nat) (ls : List SRec)
    (e : Expr) (ρ ρf W : WRes) (ps : List FrameRec) (r : FrameRec) (s : LSet)
    (hs : r.R.InStratum s.join),
    erwp (ℍ := ℍ) (Θ.view c) Tb Q n ls e ρ → ResU.Hash ρf ρ → ResU.CompS ρf ρ W →
    TWNC W ps (rsOf ls) → Tagged W ps ls → r ∈ rsOf ls →
    ρ.get r.le = some (CellU.immOf s r.v r.R hs) → Agree Θ r.le r.T r.δ

/-- **Step 8 with the agreement among its premises**: `WlImage`, where the run's first entry
also has the world agreeing with the source's record. -/
def WlImageA (P : VTy → LSub → LocTy → Nat → Val → WRes → Prop)
    (Agree : LocTy → Loc → VTy → LSub → Prop) : Prop :=
  ∀ (W : WRes) (ps : List FrameRec) (ls : List SRec) (r : FrameRec) (s : LSet)
    (hs : r.R.InStratum s.join) (a : BoCa.Lifetime.Life) (A : VTy) (δ : LSub) (Θ : LocTy)
    (n : Nat) (x : LifeVar) (β : Life),
    TWNC W ps (rsOf ls) → Tagged W ps ls → r ∈ rsOf ls →
    W.get r.le = some (CellU.immOf s r.v r.R hs) → Agree Θ r.le r.T r.δ →
    ¬ VFree x A → ¬ VFree x r.T → TmplSpec r (tmpl r) → r.R.InStratum β →
    vShape (r.T.immReborrow (.var x)) (r.δ.extend x β) r.v (canon r β) →
    (∀ y, s.mem y → β ⊑ y) →
    P (.imm a A) δ Θ n (Val.loc r.le) (ResU.single r.le (CellU.immOf s r.v r.R hs)) →
    P (A.immReborrow (.var x)) (δ.extend x β) Θ n r.v (canon r β)

/-- The agreement at the cell's lend, read off the trivial run at the world of the lend recorded
at `T`. -/
theorem agree_of_world {Agree : LocTy → Loc → VTy → LSub → Prop} (hA : ImmAgreeErwp (ℍ := ℍ) Agree)
    (T : VTy) (δ : LSub) {l l' : Loc} (α : Life) (Θ : LocTy)
    (hTW : TWNC (cellI α l l') [recT T δ l l'] (rsOf [(recT T δ l l', α)]))
    (htg : Tagged (cellI α l l') [recT T δ l l'] [(recT T δ l l', α)])
    (hH : ResU.Hash PMap.empty (cellI α l l')) : Agree Θ l T δ :=
  hA Θ (fun _ => none) (opTableN OpTabN.empty) (fun _ _ _ _ => True) 0
    [(recT T δ l l', α)] Val.unit.1 (cellI α l l') PMap.empty (cellI α l l')
    [recT T δ l l'] (recT T δ l l') (LSet.singleton α) (escU_inStratum l' _)
    (erwp_val (v := Val.unit) trivial) hH (ResU.comp_empty_left _) hTW htg (by simp [rsOf])
    (ResU.single_get_self _ _)

/-- **Every agreement `erwp` gives holds at both records of the cell**: at one world `Θ`, at
`Ref 1` and at `U (F 1)`. The run's first entry is universally quantified over the typed worlds
holding the resource, and `erwp` reads no `imm` record against the world. -/
theorem immAgreeErwp_both {Agree : LocTy → Loc → VTy → LSub → Prop}
    (hA : ImmAgreeErwp (ℍ := ℍ) Agree) {l l' : Loc} (hl : l ≠ l') (α : Life) (Θ : LocTy)
    (δ : LSub) :
    Agree Θ l (.ref .unit) δ ∧ Agree Θ l (.thunk (.ret .unit)) δ := by
  obtain ⟨hTr, htr, hHr, -⟩ := world_ref δ hl α
  obtain ⟨hTt, htt, hHt, -⟩ := world_thunk δ hl α
  exact ⟨agree_of_world hA _ δ α Θ hTr htr hHr, agree_of_world hA _ δ α Θ hTt htt hHt⟩

/-- **No agreement `erwp` gives closes step 8.** Let `P` admit the cell at `Imm @a (Ref 1)` at the
world `Θ` and have no value of `Imm 'x 1` at `∅` there. For every `Agree` with
`ImmAgreeErwp Agree`, `WlImageA P Agree` fails: the agreement holds at the world of the lend
recorded at `U (F 1)` (`immAgreeErwp_both`), where the canonical image is `∅`. -/
theorem not_wlImageA (P : VTy → LSub → LocTy → Nat → Val → WRes → Prop)
    {Agree : LocTy → Loc → VTy → LSub → Prop} (hA : ImmAgreeErwp (ℍ := ℍ) Agree) {l l' : Loc}
    (hl : l ≠ l') (α : Life) (a : BoCa.Lifetime.Life) (δ : LSub) (Θ : LocTy) (n : Nat)
    (x : LifeVar)
    (h₁ : P (.imm a (.ref .unit)) δ Θ n (Val.loc l) (cellI α l l'))
    (h₂ : ¬ P (.imm (.var x) .unit) (δ.extend x α) Θ n (Val.loc l') PMap.empty) :
    ¬ WlImageA P Agree := by
  intro hW
  let r := recT (.thunk (.ret .unit)) LSub.empty l l'
  obtain ⟨hTW, htg, -, -⟩ := world_thunk LSub.empty hl α
  have hT : r.T = .thunk (.ret .unit) := rfl
  have hag : Agree Θ r.le r.T r.δ := (immAgreeErwp_both hA hl α Θ LSub.empty).2
  have hc := hW (cellI α l l') [r] [(r, α)] r (LSet.singleton α) (escU_inStratum l' _) a
    (.ref .unit) δ Θ n x α hTW htg (by simp [rsOf]) (ResU.single_get_self _ _) hag
    (by simp [VFree]) (by rw [hT]; simp [VFree, CFree])
    (tmplSpec_thunk hT (escU_inStratum l' α) x) (escU_inStratum l' _)
    (by rw [canon_thunk hT, hT]; exact ⟨rfl, trivial⟩)
    (fun y hy => by simp [LSet.singleton] at hy; subst hy; exact le_refl _) h₁
  rw [canon_thunk hT] at hc
  exact h₂ hc

/-- `not_wlImageA` at the clause that reads, besides `vN`'s `Imm`, any condition `G` on the world
at the cell's location and type which the world holding the cell's record at `Ref 1` meets: every
such clause with every agreement from `erwp`, at `ℓ = 0`, `ℓ′ = 1`, `α = 1`. -/
theorem not_wlImageA_vN (G : LocTy → Loc → VTy → LSub → Prop)
    {Agree : LocTy → Loc → VTy → LSub → Prop} (hA : ImmAgreeErwp (ℍ := ℍ) Agree)
    (hG : G (ΘRef (LSub.empty.extend 0 1) 0 1 1) 0 (.ref .unit) (LSub.empty.extend 0 1)) :
    ¬ WlImageA (fun A δ Θ' n v ρ => vN (ℍ := ℍ) A δ Θ' n v ρ ∧
      ∀ a B l, A = .imm a B → v = Val.loc l → G Θ' l B δ) Agree :=
  not_wlImageA _ hA (l := 0) (l' := 1) (by decide) 1 (.var 0) (LSub.empty.extend 0 1)
    (ΘRef (LSub.empty.extend 0 1) 0 1 1) 0 0
    ⟨vN_cellI 0 1 0 1 0, fun a B l hA hv => by
      cases hA
      obtain rfl : l = 0 := by
        have := congrArg Subtype.val hv
        simpa [Val.loc] using this.symm
      exact hG⟩
    (fun h => not_vN_imm_empty _ _ _ _ _ _ h.1)

end BoCa.Fig16.LogRel.Core.Chain.SI.ImmRec791N

end
