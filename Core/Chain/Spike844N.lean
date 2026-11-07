import Core.Chain.Goal791N
import Core.TreeGoal791

/-!
# Borrowed payloads at a suspending lend: where the present constants stop  `[spec §62]`

`docs/new-core/scope-844-borrowed-payloads.md`. A scratch file for #844: the row a callback would
suspend at if its operations' payloads and answers could carry its own borrow, and three steps of
`withbor2S_compat` that such a row does not meet, each a configuration with every hypothesis
discharged.

* `RowSuspendB`: `Row.Suspend` with the payload and answer clauses relaxed. An operation's payload
  and answer may name the callback's `'x`; whatever else they hold still outlives `@bnd`.
* `lender_mut_payload_empty` (typing): the lender reads its row at `δ`, where `'x` is not bound.
  There an entry whose payload is `Mut 'x A` has no values. The lend constants share one row `Σ`
  between the callback's type and their own result, so the lender's stop at such an operation
  never happens, and the twin `tabNK_foldTwin` asks for (`en'.PA = en.PA`) does not hold.
* `lend_mut_payload_not_inStratum`, `lendOKCR_pa_fails` (the frame's premise): at the lend's world,
  the callback's own borrow is a value of `Mut 'x A`, and its resource is not in `Res_α`. So the
  Mut Frame's premise `OpTabK.LendOKCR.pa` (`Core/Chain/SI/MFrameK.lean`), which the frame reads to
  put the lent cell in the continuation's share at every stop, fails at such an entry.
* `CrossStop.erwp_refuses_borrowOut`, `CrossStop.not_crossTaskMLend` (the relation): a segment that
  starts owning `ℓ` cannot stop with a borrow of `ℓ` in its payload, because `↭` is asked at the
  stop. So the Mut Frame's conclusion fails at a table whose payload is the borrow, whatever
  premise replaces `pa`.

None of these says that borrowed payloads are unsound. Each names a premise or a clause of the
present lemmas and relation that a borrowed payload does not meet.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Spike844N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- **The row of a callback that may pass its own borrow to the handler.** It is `Row.Suspend`
with the clauses `¬ VFree x o.A`, `¬ VFree x o.B` and the outliving clauses replaced. The payload
and the answer may name `'x`. With `'x` read as `⊤` (`substL`), they outlive `@bnd`, so whatever
they hold besides the callback's own borrows lies above the lend. The cancel row clause is
unchanged. -/
def RowSuspendB (S : Row) (x : LifeVar) (bnd : Lifetime.Life)
    (substL : VTy → VTy) : Prop :=
  ∀ o ∈ S, o.q ≠ .unr ∧ o.n ≠ 0 ∧
    VOutlives LifeCtx.empty bnd (substL o.A) ∧ VOutlives LifeCtx.empty bnd (substL o.B) ∧
    (capB o.q o.B = true → o.fin.SuspendC x bnd)

/-- `Row.Suspend` is `RowSuspendB` at a substitution that leaves the types alone. -/
theorem rowSuspendB_of_suspend {S : Row} {x : LifeVar}
    {bnd : Lifetime.Life} (h : S.Suspend x bnd) : RowSuspendB S x bnd id :=
  fun o ho => ⟨(h o ho).1, (h o ho).2.1, (h o ho).2.2.2.2.1, (h o ho).2.2.2.2.2.1,
    (h o ho).2.2.2.2.2.2⟩

/-- **The lender's reading of a `Mut 'x A` payload is empty.** The lender reads its row at `δ`,
where `'x` is not bound: `Mut 'x A` has no value there, at any world, index or resource. -/
theorem lender_mut_payload_empty {x : LifeVar} {δ : LSub} (hx : δ.find? x = none) (A : VTy)
    (Θ : LocTy) (n : Nat) (v : Val) (ρ : WRes) :
    ¬ vN (ℍ := ℍ) (.mut (.var x) A) δ Θ n v ρ := by
  rintro ⟨α, hα, -⟩
  simp [Lifetime.Life.interp_var, hx] at hα

/-- **The callback's own borrow, passed as a payload, is not in `Res_α`.** At the lend's world
`Θ + (ℓ, α)` and `δ['x ↦ α]`, the lend's borrow `ℓ ↦ mut(α, (), ∅, …)` is a value of
`Mut 'x 1` (`lend_mutL`). Its resource holds a cell at `α` itself, so it is not in `Res_α`. -/
theorem lend_mut_payload_not_inStratum (x : LifeVar) (δ : LSub) (Θ : LocTy) (l : Loc) (α : Life)
    (n : Nat) :
    ∃ ρ : WRes,
      vN (ℍ := ℍ) (.mut (.var x) .unit) (δ.extend x α)
        (Θ.add l α (famL α (fun Θ' j u r => vN (ℍ := ℍ) .unit (δ.extend x α) Θ' j u r) Θ))
        n (Val.loc l) ρ ∧ ¬ ρ.InStratum α := by
  have hw : famL α (fun Θ' j u r => vN (ℍ := ℍ) .unit (δ.extend x α) Θ' j u r) Θ n Val.unit
      ⟨PMap.empty, ResU.inStratum_empty α⟩ := ⟨rfl, rfl⟩
  refine ⟨ResU.single l (CellU.mutOf α Val.unit PMap.empty (ResU.inStratum_empty α)
    (famL α (fun Θ' j u r => vN (ℍ := ℍ) .unit (δ.extend x α) Θ' j u r) Θ n) hw), ?_, ?_⟩
  · refine ⟨α, interp_ext_self δ x α, α, le_refl α,
      lend_mutL Θ l α _ (le_refl n) (ResU.inStratum_empty α) hw, ?_⟩
    rintro Θ' j u r ⟨-, rfl⟩
    exact ResU.inStratum_empty α
  · intro h
    have hc := h l _ (ResU.single_get_self _ _)
    rw [CellU.inStratum_mutOf] at hc
    exact lt_irrefl _ hc

/-- **The Mut Frame's `pa` premise fails at a `Mut 'x` payload**: no reading of a payload that
admits the callback's own borrow puts every payload in `Res_α`. -/
theorem lendOKCR_pa_fails (x : LifeVar) (δ : LSub) (Θ : LocTy) (l : Loc) (α : Life) (n : Nat) :
    ¬ ∀ ρ : WRes,
      vN (ℍ := ℍ) (.mut (.var x) .unit) (δ.extend x α)
        (Θ.add l α (famL α (fun Θ' j u r => vN (ℍ := ℍ) .unit (δ.extend x α) Θ' j u r) Θ))
        n (Val.loc l) ρ → ρ.InStratum α := by
  intro h
  obtain ⟨ρ, hv, hn⟩ := lend_mut_payload_not_inStratum (ℍ := ℍ) x δ Θ l α n
  exact hn (h ρ hv)

end BoCa.Fig16.LogRel.Core.Chain.SI.Spike844N

/-! ## The lender's segment at a stop that passes the borrow out

The relation's `↭` (`UpdVN`) is asked at every configuration a segment ends at, a stop included.
A segment whose start holds `ℓ` only as `own` cannot stop with a payload holding a borrow of `ℓ`
(`erwp_refuses_borrowOut`). So the Mut Frame's conclusion fails at a table whose payload is the
borrow itself (`not_crossTaskMLend`), whatever premise replaces `LendOK.pa`. These are the
statements of branch `cross-821` (`Core/Chain/CrossStopN.lean` at bbf8f16a), restated at this
relation, whose entry carries the `imm` tie. `erwpK`'s segments are `rwpG`'s
(`Core/Chain/SI/ErwpK.lean`, `erwpK_eq`), so the same `↭` is asked of a lender's stop there. -/

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Spike844N.CrossStop
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
    (hI : ImmTieL Φ.imm ls) (hl : ResU.Lower fρ μ) (hfd : FinDom μ) :
    ¬ erwp (ℍ := ℍ) Φ (opTableN T) Q n ls (K.plug (performE (.val (opPayload m i v)))) ρ₀ := by
  intro h
  rw [erwp_eq] at h
  obtain ⟨ρ', ρp, -, -, π, -, ls', -, -, -, -, -, h9, hUpd, -, -, -, -, -, hq⟩ :=
    (h ρf fρ ps μ hf hc hTW htg hI hl hfd 0 μ _ hn (StepsN.refl _ _))
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
theorem erwp_refuses_borrowOut₀ {Φ : LocFam} (hΦ : Φ.imm = []) {T : OpTabN} {m i : UInt32}
    {en : OpEntN} (hT : T m i = some en)
    (hPA : ∀ k ls v (ρ : WRes), en.PA k ls v ρ →
      ∃ ψ : CellU Loc Val, ρ.get 0 = some ψ ∧ ψ.kind ≠ Kind.own)
    {Q : PostN} {n : Nat} (hn : 0 < n) {K : Kont} (hK : K.HasHnd m = false) (v : Val) :
    ¬ erwp (ℍ := ℍ) Φ (opTableN T) Q n [] (K.plug (performE (.val (opPayload m i v)))) W₀ :=
  erwp_refuses_borrowOut hT hPA hn hK (fun _ => flatAt_single_own) w₀_hash (compS_empty_left _)
    w₀_twnc (fun _ h => absurd h (by simp)) (fun _ h => by simp [hΦ] at h) w₀_lower
    (fd_upd fd_empty 0 Val.unit)

/-- The lender's postcondition: the cell owned again. -/
def Qown (l : Loc) : PostN := fun _ _ _ ρ => ptoOwn l Val.unit ρ

/-! ### The cross-task Mut Frame -/

/-- `LendOK` without its payload condition. -/
structure LendOKXM (T : OpTabN) (A : Life) : Prop where
  entry : ∀ m i en, T m i = some en → en.abort = false ∧ en.q = .lin
  pb : ∀ m i en, T m i = some en → ∀ k ls w (ρ : WRes), en.PB k ls w ρ → ρ.InStratum (↓A)

/-- **The cross-task Mut Frame**: `erwp_M_frame`'s statement at a table whose stops may pass the
borrow out. -/
def CrossTaskMLend : Prop :=
  ∀ (Φ : LocFam) (l : Loc) (A : Life) (F : Nat → Val → SPropS Loc Val A) (_ : DownFam A F)
    (T : OpTabN) (_ : LendOKXM T A) (Q : PostN) (n j : Nat), n ≤ j → ∀ ls e (v : Val)
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

theorem TOutM_lendOKX (l : Loc) (A : Life) : LendOKXM (TOutM l A) A where
  entry := fun _ _ en h => by rw [TOutM_some h]; exact ⟨rfl, rfl⟩
  pb := fun _ _ en h _ _ _ ρ hB => by
    rw [TOutM_some h] at hB; obtain ⟨-, rfl⟩ := hB; exact LendProg.inStratum_empty _

/-- **The cross-task Mut Frame is refuted**: the borrowed run passes the borrow itself out. -/
theorem not_crossTaskMLend : ¬ CrossTaskMLend (ℍ := ℍ) := by
  intro H
  have h := H ⟨fun _ => none, []⟩ 0 0 (LendProg.famF 0) (LendProg.famF_down 0) (TOutM 0 0)
    (TOutM_lendOKX 0 0) (Qown 0) 1 1 le_rfl []
    (Kont.hole.plug (performE (.val (opPayload 7 0 Val.unit)))) Val.unit PMap.empty W₀
    PMap.empty W₀ (LendProg.inStratum_empty 0) (LendProg.inStratum_empty _) (LendProg.famF 0 1)
    (fun _ _ h => h) rfl (ResU.comp_empty_right _) (ResU.comp_empty_right _)
    (fun BM hBM => by
      obtain rfl := eq_of_compS_empty_left hBM
      exact erwp_perform (en := enOutM 0 0) .hole rfl (by simp [TOutM]) rfl rfl
        (ResU.comp_empty_right _) rfl (fun _ he => he.elim))
  refine erwp_refuses_borrowOut₀ (Φ := ⟨fun _ => none, []⟩) rfl (T := TOutM 0 0) (en := enOutM 0 0) (by simp [TOutM])
    (fun _ _ _ ρ hA => by subst hA; exact ⟨_, ResU.single_get_self _ _, fun h => Kind.noConfusion h⟩) one_pos
    (K := .hole) rfl Val.unit h

end BoCa.Fig16.LogRel.Core.Chain.SI.Spike844N.CrossStop

end
