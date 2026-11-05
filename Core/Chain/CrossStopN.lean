import Core.Chain.SI.IStopN
import Core.Chain.SI.LendProg

/-!
# A stop that carries a borrow out of the task that lent it, at `erwp`

**The fact** (`erwp_refuses_borrowOut`). `rwpG` asks `ρ ↭ π` at every configuration a run ends
at, a stop included: `ρ` the resource the segment started from, `π` everything the run holds at
the stop (payload, continuation's share, garbage). `↭`'s `imm` clause is an equivalence on the
flattenings' `imm` cells, and its `mut` clause one on their `mut` cells. So a segment whose start
holds no borrow of `ℓ` cannot stop with a payload holding one: the payload's borrow is a cell of
`π`, hence of `⦇π⦈`, of the same kind, and `↭` asks the same cell of `⦇ρ⦉`.

This is the stop of a task that lends a cell it owns and spawns a child with a borrow of it: the
lender's segment starts owning the cell (or before its allocation), and the spawn's payload is
the child's borrow. The frame rules across stops (`erwp_I_frame`, `erwp_M_frame` and their
cancellable forms) fold the borrow back into the continuation's share at every stop and ask the
payload to be in `Res_A` (`ILendOK.pa`, `LendOK.pa`), which is the same fact read as a condition
on the table.

**The cross-task Imm Frame is refuted** (`not_crossTaskILend`). `CrossTaskILend` is
`erwp_I_frame` at a table whose stops may pass the borrow out (`ILendOKX`: `ILendOK` without its
payload condition). At one table meeting `ILendOKX`, whose one entry's payload is a copy of the
borrow, the borrowed run `perform` is in `erwp` (the borrow duplicated, 6.116, one copy to the
payload), and the lender's run from `ℓ ↦ own(())` is not (`erwp_refuses_borrowOut`). Every
hypothesis is discharged on a world built by `TWNC.alloc`.

**The `mut` counterpart** (`not_crossTaskMLend`): `erwp_M_frame` at a table whose payload may
hold the borrow (`LendOKX`), refuted the same way at a payload that is the borrow itself.

**The restriction that excludes it** is Core's: the operations a borrowed callback may perform
outside it carry payloads free of the borrow's lifetime (`Row.Suspend`, `Core/TreeGoal791.lean`;
`ILendOK.pa` and `LendOK.pa` at the tables). It is decidable on the callback's row. A child that
holds the borrow is spawned into a scheduler handled inside the callback (`Core/Chain/Cross821N.lean`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI.CrossStop
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.BoLo (Heap Kont performE opPayload)
open BoCa.Lifetime (LSub)

/-! ### A borrow cell is one of the printed forms -/

theorem cell_imm_eq {ψ : CellU Loc Val} (h : ψ.kind = Kind.imm) :
    ∃ (s : LSet) (v : Val) (χ : WRes) (hχ : χ.InStratum s.join), ψ = CellU.immOf s v χ hχ := by
  cases ψ with
  | own _ => cases h
  | «mut» _ => cases h
  | imm i =>
    obtain ⟨s, v, r⟩ := i
    refine ⟨s, v, r.toU, r.toU_inStratum, ?_⟩
    show CellU.imm ⟨s, v, r⟩ = CellU.imm ⟨s, v, ResS.toRes r.toS⟩
    rw [Res.toRes_toS]

/-! ### `↭` refuses a borrow the start does not hold -/

/-- **A borrow at `ℓ` in `π` that `ρ`'s flattening does not hold at `ℓ` breaks `ρ ↭ π`.** -/
theorem not_updVN_of_borrow {Φ : LocFam} {n : Nat} {ρ π : WRes} {l : Loc} {ψ : CellU Loc Val}
    (hπ : π.get l = some ψ) (hk : ψ.kind ≠ Kind.own)
    (h₀ : ∀ χ : CellU Loc Val, ρ.FlatAt l χ → χ.kind = Kind.own) : ¬ UpdVN Φ n ρ π := by
  rintro ⟨⟨hImm, -, hMut⟩, -, σ, hσ⟩
  obtain ⟨χ, hχ, hkχ, -, -⟩ := hσ.get hπ
  have hFπ : π.FlatAt l χ := ⟨σ, hσ, hχ⟩
  cases hkc : ψ.kind with
  | own => exact hk hkc
  | imm =>
    obtain ⟨s, v, w, hw, rfl⟩ := cell_imm_eq (hkχ.trans hkc)
    have := h₀ _ ((hImm l s v w hw).mpr hFπ)
    simp at this
  | «mut» =>
    obtain ⟨χ₀, hF₀, hm⟩ := hMut l χ hFπ (hkχ.trans hkc)
    have := h₀ χ₀ hF₀
    rw [hm.1] at this
    cases this

/-- **A stop whose payload holds a borrow of `ℓ`, from a segment holding none, is not in
`erwp`.** At an operation whose every admitted payload has a non-`own` cell at `ℓ`, from any
configuration the relation quantifies over. -/
theorem erwp_refuses_borrowOut {Φ : LocFam} {T : OpTabN} {m i : UInt32} {en : OpEntN}
    (hT : T m i = some en) {l : Loc}
    (hPA : ∀ k ls v (ρ : WRes), en.PA k ls v ρ →
      ∃ ψ : CellU Loc Val, ρ.get l = some ψ ∧ ψ.kind ≠ Kind.own)
    {Q : PostN} {n : Nat} (hn : 0 < n) {ls : List SRec} {K : Kont} (hK : K.HasHnd m = false)
    {v : Val} {ρ₀ : WRes} (h₀ : ∀ χ : CellU Loc Val, ρ₀.FlatAt l χ → χ.kind = Kind.own)
    {ρf fρ : WRes} {ps : List FrameRec} {μ : Heap} (hf : ResU.Hash ρf ρ₀)
    (hc : ResU.CompS ρf ρ₀ fρ) (hTW : TWNC fρ ps (rsOf ls)) (htg : Tagged fρ ps ls)
    (hl : ResU.Lower fρ μ) (hfd : FinDom μ) :
    ¬ erwp (ℍ := ℍ) Φ (opTableN T) Q n ls (K.plug (performE (.val (opPayload m i v)))) ρ₀ := by
  intro h
  rw [erwp_eq] at h
  obtain ⟨ρ', ρp, -, -, π, -, ls', -, -, -, -, -, h9, hUpd, -, -, -, -, -, hq⟩ :=
    h ρf fρ ps μ hf hc hTW htg hl hfd 0 μ _ hn (StepsN.refl _ _)
      (final_opPlug (r := false) (payloadName_opPayload m i v) hK μ)
  rcases hq with ⟨w, hw, -⟩ | ⟨K', m', i', v', en', hp⟩ | ⟨K', m', i', v', en', hp⟩
  · exact plug_perform_ne_val K _ w hw
  · obtain ⟨⟨ht, -, hT', -⟩, ρa, ρk, hcak, hA, -⟩ := pure_sep_iff.mp hp
    obtain ⟨-, hpay⟩ := plug_perform_inj ht
    obtain ⟨rfl, rfl, rfl⟩ := opPayload_inj hpay
    rw [hT] at hT'
    cases hT'
    obtain ⟨ψ, hψ, hk⟩ := hPA _ _ _ _ hA
    obtain ⟨ψ', hψ', hk', -, -⟩ := compS_get_left' hcak hψ
    obtain ⟨ψ'', hψ'', hk'', -, -⟩ := compS_get_left' h9 hψ'
    exact not_updVN_of_borrow hψ'' (by rw [hk'', hk']; exact hk) h₀ hUpd
  · obtain ⟨⟨ht, -⟩, -⟩ := pure_sep_iff.mp hp
    exact plug_perform_ne_raise K K' _ _ ht

/-- `ℓ ↦ own(v)`'s flattening holds only `own` at `ℓ`. -/
theorem flatAt_single_own {l : Loc} {v : Val} {χ : CellU Loc Val}
    (h : (ResU.single l (CellU.ownOf v) : WRes).FlatAt l χ) : χ.kind = Kind.own := by
  obtain ⟨σ, hσ, hχ⟩ := h
  rw [ResU.Flat.functional hσ (ResU.flat_single_own l v), ResU.single_get_self] at hχ
  cases hχ
  rfl

/-! ### The world the refutations start from -/

/-- The cell `0 ↦ own(())`. -/
abbrev W₀ : WRes := ResU.single 0 (CellU.ownOf Val.unit)

theorem w₀_twnc : TWNC W₀ [] (rsOf []) :=
  TWNC.alloc TWNC.empty lower_empty rfl (compS_empty_left _) (ResU.valid_single_own 0 Val.unit)

theorem w₀_lower : ResU.Lower W₀ (BoCa.BoLo.Heap.upd (fun _ => none) 0 Val.unit) :=
  lower_compS_own (compS_empty_left _) lower_empty rfl

theorem w₀_hash : ResU.Hash (PMap.empty : WRes) W₀ :=
  ResU.hash_symm (ResU.hash_empty_right (ResU.valid_single_own 0 Val.unit))

/-- **No run from `0 ↦ own(())` stops with a borrow of `0` in its payload.** -/
theorem erwp_refuses_borrowOut₀ {Φ : LocFam} {T : OpTabN} {m i : UInt32} {en : OpEntN}
    (hT : T m i = some en)
    (hPA : ∀ k ls v (ρ : WRes), en.PA k ls v ρ →
      ∃ ψ : CellU Loc Val, ρ.get 0 = some ψ ∧ ψ.kind ≠ Kind.own)
    {Q : PostN} {n : Nat} (hn : 0 < n) {K : Kont} (hK : K.HasHnd m = false) (v : Val) :
    ¬ erwp (ℍ := ℍ) Φ (opTableN T) Q n [] (K.plug (performE (.val (opPayload m i v)))) W₀ :=
  erwp_refuses_borrowOut hT hPA hn hK (fun _ => flatAt_single_own) w₀_hash (compS_empty_left _)
    w₀_twnc (fun _ h => absurd h (by simp)) w₀_lower (fd_upd fd_empty 0 Val.unit)

/-! ### The cross-task Imm Frame -/

/-- `ILendOK` without its payload condition: a stop may pass the borrow out. -/
structure _root_.BoCa.Fig16.LogRel.Core.Chain.SI.OpTabN.ILendOKX (T : OpTabN) (A : Life) : Prop where
  entry : ∀ m i en, T m i = some en → en.abort = false ∧ en.q = .lin
  pb : ∀ m i en, T m i = some en → ∀ k ls w (ρ : WRes), en.PB k ls w ρ → ρ.InStratum A
  paExt : ∀ m i en, T m i = some en → ∀ k ls₁ ls₂ v (ρ : WRes), Ext ls₁ ls₂ ρ →
    en.PA k ls₁ v ρ → en.PA k ls₂ v ρ
  pbExt : ∀ m i en, T m i = some en → ∀ k ls₁ ls₂ w (ρ : WRes), Ext ls₁ ls₂ ρ →
    en.PB k ls₁ w ρ → en.PB k ls₂ w ρ

/-- **The cross-task Imm Frame**: `erwp_I_frame`'s statement at a table whose stops may pass the
borrow out. -/
def CrossTaskILend : Prop :=
  ∀ (Φ : LocFam) (l : Loc) (T : VTy) (δ : LSub) (_ : AdmWf T δ) (v : Val)
    (P : List SRec → Val → WProp) (_ : ∀ ls ρ, P ls v ρ → vShape T δ v ρ)
    (_ : ∀ ls₁ ls₂ ρ, Ext ls₁ ls₂ ρ → P ls₁ v ρ → P ls₂ v ρ)
    (A : Life) (Tb : OpTabN) (_ : Tb.ILendOKX A) (Q : PostN)
    (_ : ∀ k ls₁ ls₂ w ρ, Ext ls₁ ls₂ ρ → Q k ls₁ w ρ → Q k ls₂ w ρ)
    (n : Nat) (ls : List SRec) (e : Expr) (ρP ρlP ρb ρ : WRes) (houtP : ρP.InStratum A),
    ρb.InStratum A → P ls v ρP → ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP →
    ResU.CompS ρlP ρb ρ → (∀ x ∈ ls, x.2 ≠ A) → ∀ ds, (∀ d, d ∈ ds ↔ Desc ⟨l, v, ρP, T, δ⟩ d) →
    (∀ BI, ResU.CompS ρb (ResU.single l (CellU.immOf (LSet.singleton A) v ρP houtP)) BI →
      erwp (ℍ := ℍ) Φ (opTableN Tb) (IFPost l v P A Q) n (frameList ⟨l, v, ρP, T, δ⟩ ds A ls)
        e BI) →
    erwp (ℍ := ℍ) Φ (opTableN Tb) Q n ls e ρ

/-- The borrow `ℓ ↦ imm({A}, (), ∅)`. -/
abbrev viewI (l : Loc) (A : Life) : WRes :=
  ResU.single l (CellU.immOf (LSet.singleton A) Val.unit PMap.empty (LendProg.inStratum_empty A))

/-- An operation whose payload is a copy of the borrow of `ℓ` at `A`, resumed with nothing. -/
def enOutI (l : Loc) (A : Life) : OpEntN :=
  ⟨.lin, false, fun _ _ _ ρ => ρ = viewI l A, fun _ _ w ρ => w = Val.unit ∧ ρ = PMap.empty, none,
    fun _ _ _ => False⟩

/-- The table with that operation at `(7, 0)`. -/
def TOutI (l : Loc) (A : Life) : OpTabN := fun m i =>
  if m = 7 ∧ i = 0 then some (enOutI l A) else none

theorem TOutI_some {l : Loc} {A : Life} {m i : UInt32} {en : OpEntN}
    (h : TOutI l A m i = some en) : en = enOutI l A := by
  unfold TOutI at h
  split_ifs at h
  exact (Option.some.inj h).symm

theorem TOutI_iLendOKX (l : Loc) (A : Life) : (TOutI l A).ILendOKX A where
  entry := fun _ _ en h => by rw [TOutI_some h]; exact ⟨rfl, rfl⟩
  pb := fun _ _ en h _ _ _ ρ hB => by
    rw [TOutI_some h] at hB; obtain ⟨-, rfl⟩ := hB; exact LendProg.inStratum_empty A
  paExt := fun _ _ en h _ _ _ _ _ _ hA => by rw [TOutI_some h] at hA ⊢; exact hA
  pbExt := fun _ _ en h _ _ _ _ _ _ hB => by rw [TOutI_some h] at hB ⊢; exact hB

/-- The empty lifetime substitution. -/
def δ₀ : LSub := ⟨[]⟩

/-- The lender's postcondition: the cell owned again. -/
def Qown (l : Loc) : PostN := fun _ _ _ ρ => ptoOwn l Val.unit ρ

/-- **The borrowed run passes a copy of the borrow out**: `perform` at `TOutI`, from the
borrow, the payload one copy (6.116) and the continuation's share the other, at every index. -/
theorem outI_body (l : Loc) (A : Life) (n : Nat) (ls : List SRec) (BI : WRes)
    (hBI : ResU.CompS PMap.empty (viewI l A) BI) :
    erwp (ℍ := ℍ) (fun _ => none) (opTableN (TOutI l A)) (IFPost l Val.unit (fun _ _ ρ => ρ =
      PMap.empty) A (Qown l)) n ls (Kont.hole.plug (performE (.val (opPayload 7 0 Val.unit))))
      BI := by
  obtain rfl := eq_of_compS_empty_left hBI
  exact erwp_perform (en := enOutI l A) .hole rfl (by simp [TOutI]) rfl rfl
    (compS_imm_dup l _ Val.unit PMap.empty (LendProg.inStratum_empty A)) rfl
    (fun _ he => he.elim)

/-- **The cross-task Imm Frame is refuted.** -/
theorem not_crossTaskILend : ¬ CrossTaskILend (ℍ := ℍ) := by
  intro H
  have hshape : vShape .unk δ₀ Val.unit (PMap.empty : WRes) := ⟨rfl, trivial⟩
  have hadm : AdmWf .unk δ₀ := fun _ h => h.elim
  obtain ⟨ds, hds⟩ := lineage_list (r := ⟨0, Val.unit, PMap.empty, .unk, δ₀⟩) hshape hadm
    (ExW.empty_of_all_imm (fun _ _ h => by simp at h))
  have h := H (fun _ => none) 0 .unk δ₀ hadm Val.unit (fun _ _ ρ => ρ = PMap.empty)
    (fun _ ρ hρ => by subst hρ; exact hshape) (fun _ _ _ _ h => h) 0 (TOutI 0 0)
    (TOutI_iLendOKX 0 0) (Qown 0) (fun _ _ _ _ _ _ h => h) 1 []
    (Kont.hole.plug (performE (.val (opPayload 7 0 Val.unit)))) PMap.empty W₀ PMap.empty W₀
    (LendProg.inStratum_empty 0) (LendProg.inStratum_empty 0) rfl (ResU.comp_empty_right _)
    (ResU.comp_empty_right _) (fun _ hx => absurd hx (by simp)) ds hds
    (fun BI hBI => outI_body 0 0 1 _ BI hBI)
  refine erwp_refuses_borrowOut₀ (T := TOutI 0 0) (en := enOutI 0 0) (by simp [TOutI])
    (fun _ _ _ ρ hA => by subst hA; exact ⟨_, ResU.single_get_self _ _, fun h => Kind.noConfusion h⟩) one_pos
    (K := .hole) rfl Val.unit h

/-! ### The cross-task Mut Frame -/

/-- `LendOK` without its payload condition. -/
structure _root_.BoCa.Fig16.LogRel.Core.Chain.SI.OpTabN.LendOKX (T : OpTabN) (A : Life) : Prop where
  entry : ∀ m i en, T m i = some en → en.abort = false ∧ en.q = .lin
  pb : ∀ m i en, T m i = some en → ∀ k ls w (ρ : WRes), en.PB k ls w ρ → ρ.InStratum (↓A)

/-- **The cross-task Mut Frame**: `erwp_M_frame`'s statement at a table whose stops may pass the
borrow out. -/
def CrossTaskMLend : Prop :=
  ∀ (Φ : LocFam) (l : Loc) (A : Life) (F : Nat → Val → SPropS Loc Val A) (_ : DownFam A F)
    (T : OpTabN) (_ : T.LendOKX A) (Q : PostN) (n j : Nat), n ≤ j → ∀ ls e (v : Val)
    (ρP ρlP ρb ρ : WRes) (houtP : ρP.InStratum A), ρb.InStratum (↓A) →
    ∀ (P : Val → SPropS Loc Val A), (∀ u r, SPropS.toU (P u) r → SPropS.toU (F j u) r) →
    ∀ (hwit : P v ⟨ρP, houtP⟩), ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP →
    ResU.CompS ρlP ρb ρ →
    (∀ BM, ResU.CompS ρb (ResU.single l (CellU.mutOf A v ρP houtP P hwit)) BM →
      erwp (ℍ := ℍ) (Φ.set l A F) (opTableN T) (MFPost l A F Q) n ls e BM) →
    erwp (ℍ := ℍ) Φ (opTableN T) Q n ls e ρ

/-- The borrow `ℓ ↦ mut(A, (), ∅, famF A 1)`. -/
abbrev viewM (l : Loc) (A : Life) : WRes :=
  ResU.single l (CellU.mutOf A Val.unit PMap.empty (LendProg.inStratum_empty A)
    (LendProg.famF A 1) rfl)

/-- An operation whose payload is the borrow of `ℓ` at `A`, resumed with nothing. -/
def enOutM (l : Loc) (A : Life) : OpEntN :=
  ⟨.lin, false, fun _ _ _ ρ => ρ = viewM l A, fun _ _ w ρ => w = Val.unit ∧ ρ = PMap.empty, none,
    fun _ _ _ => False⟩

def TOutM (l : Loc) (A : Life) : OpTabN := fun m i =>
  if m = 7 ∧ i = 0 then some (enOutM l A) else none

theorem TOutM_some {l : Loc} {A : Life} {m i : UInt32} {en : OpEntN}
    (h : TOutM l A m i = some en) : en = enOutM l A := by
  unfold TOutM at h
  split_ifs at h
  exact (Option.some.inj h).symm

theorem TOutM_lendOKX (l : Loc) (A : Life) : (TOutM l A).LendOKX A where
  entry := fun _ _ en h => by rw [TOutM_some h]; exact ⟨rfl, rfl⟩
  pb := fun _ _ en h _ _ _ ρ hB => by
    rw [TOutM_some h] at hB; obtain ⟨-, rfl⟩ := hB; exact LendProg.inStratum_empty _

/-- **The cross-task Mut Frame is refuted**: the borrowed run passes the borrow itself out. -/
theorem not_crossTaskMLend : ¬ CrossTaskMLend (ℍ := ℍ) := by
  intro H
  have h := H (fun _ => none) 0 0 (LendProg.famF 0) (LendProg.famF_down 0) (TOutM 0 0)
    (TOutM_lendOKX 0 0) (Qown 0) 1 1 le_rfl []
    (Kont.hole.plug (performE (.val (opPayload 7 0 Val.unit)))) Val.unit PMap.empty W₀
    PMap.empty W₀ (LendProg.inStratum_empty 0) (LendProg.inStratum_empty _) (LendProg.famF 0 1)
    (fun _ _ h => h) rfl (ResU.comp_empty_right _) (ResU.comp_empty_right _)
    (fun BM hBM => by
      obtain rfl := eq_of_compS_empty_left hBM
      exact erwp_perform (en := enOutM 0 0) .hole rfl (by simp [TOutM]) rfl rfl
        (ResU.comp_empty_right _) rfl (fun _ he => he.elim))
  refine erwp_refuses_borrowOut₀ (T := TOutM 0 0) (en := enOutM 0 0) (by simp [TOutM])
    (fun _ _ _ ρ hA => by subst hA; exact ⟨_, ResU.single_get_self _ _, fun h => Kind.noConfusion h⟩) one_pos
    (K := .hole) rfl Val.unit h

end BoCa.Fig16.LogRel.Core.Chain.SI.CrossStop

end

