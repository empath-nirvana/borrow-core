import Core.EffBorrow
import Core.EffBoxed

/-!
# Core — a lend held across a call-graded stop  `[spec §48]`

A lend's callback runs at a row whose operations are abortive or call-graded (`Row.Lend`). At a
graded stop the continuation is owed only at lists with the stop's members (`Owed`), so the
stop's handler resumes it in the scope of the stop. The frame of `[TR]` 6.65 then spans the
stop: the stop ends the lend as at a return (the exit of `wpG_M_frameAt` reads no term), the
frame's stop owes its continuation the owner, and the resumption lends again **at the lifetime it
lent at, with the cell the stop held**, so the callback's continuation runs from exactly the
resource it stopped with. No value moves to another lifetime.

The proof is one induction on the callback's least fixed point (`lendM_frame`), at a table of the
row's stops beside a tick's stop that owes a fixed obligation (`LTab`): no tick at a row without
`Div`, the tick of a segment of `cwp`, the closing tick of `Closing`. Its cases:

* a return: the printed exit, the answer handed the owner;
* an abortive stop: the abandoned continuation holds nothing owned and is left behind, the frame
  ends as at a return, and the unwinding frame `ubind` runs the finaliser on the owner and raises
  again (`ewp_ubind_raise`, §19's unwinding);
* a graded stop whose share holds the cell: the cell joins the leftover, the frame ends, and the
  share less the cell is in `Res_α` (`six27S`, 6.27's stratum from 6.50 at one location); the
  continuation, owed at lists with the stop's members, is resumed with the lend made again;
* a graded stop whose share has left the cell behind: the owner is carried beside the callback to
  its end (`lendM_owner`).

No case names an effect or a depth.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont Step1N performE raiseE opPayload ubindE)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### A run ends at a list with its start's members -/

/-- `wpG` ends at a list with its start's members: its last conjunct, as a postcondition. -/
theorem wpG_sameMem {ls : List SRec} {e : Expr} {Q : List SRec → Expr → WProp} {ρ : WRes}
    (h : wpG ls e Q ρ) : wpG ls e (fun ls' t σ => (∀ x, x ∈ ls' ↔ x ∈ ls) ∧ Q ls' t σ) ρ := by
  intro ρf fρ ps h1 h2 h3 h4 A k
  obtain ⟨ρ', ρp, fρ', fρ'p, π, t, μ, μ', ps', ls', a1, a2, a3, a4, a5, a6, a7, a8, a9, a10,
    a11, a12, a13, a14, a15⟩ := h ρf fρ ps h1 h2 h3 h4 A k
  exact ⟨ρ', ρp, fρ', fρ'p, π, t, μ, μ', ps', ls', a1, a2, a3, a4, a5, a6, a7, a8, a9, a10,
    a11, a12, a13, a14, a14, a15⟩

/-! ### The stratum with the cell set aside -/

/-- **6.27's stratum with the cell set aside**: if `ρ ∈ Res_α` and
`ρ ● ℓ ↦ mut(α, v, ρ_v, P̂) ↭ ρ′`, then `ρ′/ℓ ∈ Res_α`. -/
def Six27S : Prop :=
  ∀ (l : BoCa.Loc) (α : Life) (v : BoCa.Val) (ρ ρv M ρ' : WRes) (h : ρv.InStratum α)
    (P : BoCa.Val → SPropS BoCa.Loc BoCa.Val α) (hw : P v ⟨ρv, h⟩),
    ρ.InStratum α → ResU.CompS ρ (ResU.single l (CellU.mutOf α v ρv h P hw)) M →
    ResU.UpdV M ρ' → (ρ'.del l).InStratum α

/-- Off `ℓ`, a resource and its composite with a cell at `ℓ` agree. -/
theorem get_off_single {ρ₁ ρ : WRes} {l m : BoCa.Loc} {ψ : CellU BoCa.Loc BoCa.Val}
    (h : ResU.CompS ρ₁ (ResU.single l ψ) ρ) (hm : m ≠ l) : ρ.get m = ρ₁.get m := by
  have hn : (ResU.single l ψ).get m = none := ResU.single_get_ne ψ hm
  rcases ResU.Comp.get h m with ⟨f₁, -, f⟩ | ⟨χ, f₁, -, f⟩ | ⟨χ, -, f₂, -⟩ |
      ⟨χ₁, χ₂, χ, -, f₂, -, -⟩
  · rw [f, f₁]
  · rw [f, f₁]
  · rw [hn] at f₂; cases f₂
  · rw [hn] at f₂; cases f₂

/-- **`Six27S` holds**: off `ℓ`, `ρ ● ℓ ↦ mut(α, …)` is in `Res_α`, and the whole is in
`Res_{↓α}`, so 6.50 at one location (`ResU.updV_outlives_at`) puts every cell of `ρ′` off `ℓ` in
`Res_α`. -/
theorem six27S : Six27S := by
  intro l α v ρ ρv M ρ' h P hw hout hM hu m ψ e
  by_cases hm : m = l
  · subst hm; rw [ResU.del_get_self] at e; cases e
  · rw [ResU.del_get_ne _ hm] at e
    have hdM : M.InStratum (↓α) :=
      BoLo.inStratum_comp (BoLo.compS_hC (↓α)) hM
        (fun m ψ e => CellU.InStratum.mono (le_of_lt (Life.down_sqsubset α)) (hout m ψ e))
        (ResU.inStratum_single l ((CellU.inStratum_mutOf (↓α) α v ρv h P hw).mpr
          (Life.down_sqsubset α)))
    exact ResU.updV_outlives_at hdM hu
      (fun φ hφ => hout m φ (by rw [← get_off_single hM hm]; exact hφ)) e

/-- At the end of a run started from `Res_α ● ℓ ↦ mut(α, …)`, the share less `ℓ` is in `Res_α`. -/
theorem wpG_viewStrat {l : BoCa.Loc} {α : Life} {v : BoCa.Val} {ρv : WRes}
    {h : ρv.InStratum α} {P : BoCa.Val → SPropS BoCa.Loc BoCa.Val α} {hw : P v ⟨ρv, h⟩}
    {ρb ρ : WRes} (hout : ρb.InStratum α)
    (hcomp : ResU.CompS ρb (ResU.single l (CellU.mutOf α v ρv h P hw)) ρ)
    {ls : List SRec} {e : Expr} {Q : List SRec → Expr → WProp} (hq : wpG ls e Q ρ) :
    wpG ls e (fun ls' t σ => Q ls' t σ ∧ (σ.del l).InStratum α) ρ := by
  intro ρf fρ ps h1 h2 h3 h4 A k
  obtain ⟨ρ', ρp, fρ', fρ'p, π, t, μ, μ', ps', ls', a1, a2, a3, a4, a5, a6, a7, a8, a9, a10,
    a11, a12, a13, a14, a15⟩ := hq ρf fρ ps h1 h2 h3 h4 A k
  exact ⟨ρ', ρp, fρ', fρ'p, π, t, μ, μ', ps', ls', a1, a2, a3, a4, a5, a6, a7, a8, a9, a10,
    a11, a12, a13, a14, a15, del_inStratum_left a8 (six27S l α v ρb ρv ρ π h P hw hout hcomp a9)⟩

/-! ### The cell a lend holds, read at lists with the same members -/

theorem QsAt_congr {T : VTy} {δ : LSub} {ls ls' : List SRec} (hs : ∀ x, x ∈ ls' ↔ x ∈ ls)
    (A : Life) : QsAt T δ ls A = QsAt T δ ls' A := by
  funext w r
  exact propext ⟨fun h => vC_local true T (ext_of_same hs r.1) h,
    fun h => vC_local true T (ext_of_same (fun x => (hs x).symm) r.1) h⟩

theorem mutOf_congr {A : Life} {v : Val} {ρP : WRes} {h : ρP.InStratum A}
    {Q Q' : Val → SPropS BoCa.Loc BoCa.Val A} (hQ : Q = Q') (hw : Q v ⟨ρP, h⟩)
    (hw' : Q' v ⟨ρP, h⟩) : CellU.mutOf A v ρP h Q hw = CellU.mutOf A v ρP h Q' hw' := by
  subst hQ; rfl

/-- The cell a lend holds is the same at two lists with the same members. -/
theorem viewCell_congr {l : BoCa.Loc} {T : VTy} {δ : LSub} {ls ls' : List SRec}
    (hs : ∀ x, x ∈ ls' ↔ x ∈ ls) {A : Life} {v : Val} {ρP : WRes} {h : ρP.InStratum A}
    (hw : vC true T ls δ v ρP) (hw' : vC true T ls' δ v ρP) :
    viewCell l T δ ls A v ρP h hw = viewCell l T δ ls' A v ρP h hw' :=
  congrArg (ResU.single l) (mutOf_congr (QsAt_congr hs A) hw hw')

/-! ### The owner and the callback's post -/

/-- The lender's place, owned: `∃w. ℓ ↦ w ⋆ 𝒱⟦T⟧(ls)δ(w)`, the relation of `ℓ : Ref T`. -/
def owner (l : BoCa.Loc) (T : VTy) (δ : LSub) (ls : List SRec) : WProp :=
  ex fun w => ptoOwn l w ⋆ vC true T ls δ w

theorem owner_same {l : BoCa.Loc} {T : VTy} {δ : LSub} {ls ls' : List SRec}
    (hs : ∀ x, x ∈ ls' ↔ x ∈ ls) {ρ : WRes} (h : owner l T δ ls ρ) : owner l T δ ls' ρ := by
  obtain ⟨w, ρ₁, ρ₂, hc, ho, hv⟩ := h
  exact ⟨w, ρ₁, ρ₂, hc, ho, vC_local true T (ext_of_same hs ρ₂) hv⟩

/-- The owner is `ℓ`'s relation at `Ref T`. -/
theorem owner_iff {l : BoCa.Loc} {T : VTy} {δ : LSub} {ls : List SRec} {ρ : WRes} :
    owner l T δ ls ρ ↔ vC true (.ref T) ls δ (.loc l) ρ := by
  constructor
  · rintro ⟨w, h⟩; exact ⟨l, w, pure_sep_mk rfl h⟩
  · rintro ⟨m, w, h⟩
    obtain ⟨hm, h⟩ := pure_sep_iff.mp h
    cases hm
    exact ⟨w, h⟩

/-- The callback's post at a lend at `α`: 6.65's `[α] ∀v′. ℓ ↦ v′ ─⋆ P̂(v′) ─⋆ Q`. -/
def postA (l : BoCa.Loc) (T : VTy) (δ : LSub) (α : Life) (Q : List SRec → Val → WProp) :
    List SRec → Val → WProp := fun ls'' v' =>
  box α (all fun w => ptoOwn l w ─⋆ (vC true T ls'' δ w ─⋆ Q ls'' v'))

theorem postA_apply {l : BoCa.Loc} {T : VTy} {δ : LSub} {α : Life} {Q : List SRec → Val → WProp}
    {ls : List SRec} {v' : Val} {σ₁ σ₂ σ : WRes} (h : postA l T δ α Q ls v' σ₁)
    (ho : owner l T δ ls σ₂) (hc : ResU.CompS σ₁ σ₂ σ) : Q ls v' σ := by
  obtain ⟨w, ρ₁, ρ₂, hc₁₂, rfl, hv⟩ := ho
  obtain ⟨y, hy₁, hy₂⟩ := compS_reassoc' hc₁₂ hc
  exact h.1 w _ y rfl hy₁ ρ₂ σ hv hy₂

/-- The share and the answer compose once the owner is turned back into the cell. -/
theorem compS_exists_swap {ρk₁ W kS τ₁ τ₂ ρk : WRes} {l : BoCa.Loc}
    {ψ φ : CellU BoCa.Loc BoCa.Val}
    (hkS : ResU.CompS ρk₁ W kS) (hcτ : ResU.CompS kS τ₁ τ₂)
    (hk₁ : ResU.CompS ρk₁ (ResU.single l ψ) ρk)
    (hW : W.get l = some φ) (hφ : φ.kind ≠ Kind.imm) : ∃ z, ResU.CompS ρk τ₁ z := by
  have hτl : τ₁.get l = none := by
    have hkSl : kS.get l = some φ :=
      (ResU.CompS.get_left_of_ne_imm (ResU.CompS.comm hkS) hW hφ).2
    exact (ResU.CompS.get_left_of_ne_imm hcτ hkSl hφ).1
  have hc₁ : ResU.CompatS ρk₁ τ₁ :=
    ResU.CompatS.of_factors hkS (ResU.CompS.comm (compS_empty_left τ₁)) hcτ.1
  refine (ResU.compS_defined_iff ρk τ₁).mpr ?_
  intro m ψ₁ ψ₂ e₁ e₂
  by_cases hm : m = l
  · subst hm; rw [hτl] at e₂; cases e₂
  · rw [get_off_single hk₁ hm] at e₁
    exact hc₁ m ψ₁ ψ₂ e₁ e₂

/-! ### A lend's tables -/

/-- **A lend's table at `α`**: each entry of a nonzero name, its arguments in `Res_α`, and either
abortive, or call-graded and linear with its answers in `Res_α` (closed data, `Row.Lend`).
`[spec §48]` -/
def OpTab.LendAt (α : Life) (T : OpTab) : Prop :=
  ∀ n i en, T n i = some en → n ≠ 0 ∧ (∀ ls w τ, en.PA ls w τ → τ.InStratum α) ∧
    (en.abort = true ∨ (en.call = true ∧ en.q = .lin ∧ ∀ ls w τ, en.PB ls w τ → τ.InStratum α))

/-- The table of a lend's segment: the row's stops, and a tick's stop owing `Ψ`, whatever the
run would owe (`T0` empty at a row without `Div`).  `[spec §48]` -/
abbrev LTab (T₁ T0 : OpTab) (Ψ : List SRec → Expr → WProp) : Table :=
  orTab (opTable T₁) (fun ls t _ => performStop T0 ls t Ψ)

theorem LTab_mono (T₁ T0 : OpTab) (Ψ : List SRec → Expr → WProp) : (LTab T₁ T0 Ψ).Mono :=
  orTab_mono (opTable_mono T₁) (Table.Const.mono fun _ _ _ _ _ h => h)

/-- A graded, linear stop, its share owed at the lists with the stop's members. -/
theorem performStop_graded_mk {T : OpTab} {ls : List SRec} {Φ : List SRec → Expr → WProp}
    {K : Kont} {n i : UInt32} {v : Val} {en : OpEnt} {ρa ρk ρ : WRes}
    (hK : K.HasHnd n = false) (hT : T n i = some en) (ha : en.abort = false)
    (hc : en.call = true) (hq : en.q = .lin) (hcp : ResU.CompS ρa ρk ρ) (hA : en.PA ls v ρa)
    (hk : ∀ ls', (∀ x, x ∈ ls' ↔ x ∈ ls) → ∀ w : Val,
      (en.PB ls' w ─⋆ Φ ls' (K.plug (.val w))) ρk) :
    performStop T ls (K.plug (performE (.val (opPayload n i v)))) Φ ρ := by
  refine ⟨K, n, i, v, en, pure_sep_mk ⟨rfl, hK, hT, ha⟩ ⟨ρa, ρk, hcp, hA, fun hu => ?_, ?_⟩⟩
  · rw [hq] at hu; cases hu
  · intro ls' ho
    unfold Owed at ho; rw [hc] at ho
    exact ⟨hk ls' ho, fun hq' => absurd hq hq'⟩

/-- A graded stop, unpacked: its argument, and its share owed at the lists with its members. -/
theorem performStop_graded_inv {T : OpTab} {α : Life} (hT : T.LendAt α) {ls : List SRec}
    {Φ : List SRec → Expr → WProp} {t : Expr} {ρ : WRes} (h : performStop T ls t Φ ρ) :
    ∃ (K : Kont) (n i : UInt32) (v : Val) (en : OpEnt) (ρa ρk : WRes),
      t = K.plug (performE (.val (opPayload n i v))) ∧ K.HasHnd n = false ∧ T n i = some en ∧
      en.abort = false ∧ en.call = true ∧ en.q = .lin ∧ ResU.CompS ρa ρk ρ ∧ en.PA ls v ρa ∧
      ρa.InStratum α ∧ (∀ ls w τ, en.PB ls w τ → τ.InStratum α) ∧
      ∀ ls', (∀ x, x ∈ ls' ↔ x ∈ ls) → ∀ w : Val,
        (en.PB ls' w ─⋆ Φ ls' (K.plug (.val w))) ρk := by
  obtain ⟨K, n, i, v, en, hp⟩ := h
  obtain ⟨⟨rfl, hK, hTn, ha⟩, ρa, ρk, hcp, hA, -, hcont⟩ := pure_sep_iff.mp hp
  obtain ⟨-, harg, hab | ⟨hc, hq, hans⟩⟩ := hT n i en hTn
  · rw [hab] at ha; cases ha
  refine ⟨K, n, i, v, en, ρa, ρk, rfl, hK, hTn, ha, hc, hq, hcp, hA, harg ls v ρa hA, hans,
    fun ls' hs w => (hcont ls' (owed_of_same en hs ρk)).1 w⟩

/-- An end of a lend's callback: an answer, a graded stop, a tick's stop, or a `raise` held by its
argument alone, the abandoned continuation left behind (it holds nothing owned). -/
def lendEnd (T₁ T0 : OpTab) (Ψ : List SRec → Expr → WProp) (Qv : List SRec → Val → WProp)
    (P : List SRec → Expr → WProp) : List SRec → Expr → WProp := fun ls t σ =>
  valPost Qv ls t σ ∨ performStop T₁ ls t P σ ∨ performStop T0 ls t Ψ σ ∨
    ∃ (K : Kont) (n i : UInt32) (v : Val) (en : OpEnt),
      t = K.plug (raiseE (.val (opPayload n i v))) ∧ K.Catches n = false ∧ T₁ n i = some en ∧
      en.abort = true ∧ en.PA ls v σ ∧ NoOwn σ

/-- **A raise's continuation is left behind** at the end of a segment (`wpG_garbage`). -/
theorem wpG_lendEnd {T₁ T0 : OpTab} {Ψ : List SRec → Expr → WProp} {Qv : List SRec → Val → WProp}
    {P : List SRec → Expr → WProp} {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : ewpStep (LTab T₁ T0 Ψ) Qv P ls e ρ) : wpG ls e (lendEnd T₁ T0 Ψ Qv P) ρ := by
  refine wpG_garbage (wpG_mono (fun ls' t σ ht => ?_) h)
  rcases ht with hv | hp | hp
  · exact ⟨σ, PMap.empty, ResU.comp_empty_right σ, noOwn_empty, Or.inl hv⟩
  · rcases hp with hp | ⟨K, n, i, v, en, hp⟩
    · exact ⟨σ, PMap.empty, ResU.comp_empty_right σ, noOwn_empty, Or.inr (Or.inl hp)⟩
    · obtain ⟨⟨rfl, hK, hT, ha⟩, ρa, ρn, hcan, ⟨hPA, hnA⟩, hn⟩ := pure_sep_iff.mp hp
      exact ⟨ρa, ρn, hcan, hn, Or.inr (Or.inr (Or.inr ⟨K, n, i, v, en, rfl, hK, hT, ha, hPA, hnA⟩))⟩
  · exact ⟨σ, PMap.empty, ResU.comp_empty_right σ, noOwn_empty, Or.inr (Or.inr (Or.inl hp))⟩

/-- A lend's end keeps the stratum of the share less `ℓ` as its resource shrinks. -/
theorem lendEnd_mono {T₁ T0 : OpTab} {Ψ : List SRec → Expr → WProp} {Qv Qv' : List SRec → Val → WProp}
    {P : List SRec → Expr → WProp} (hQ : ∀ ls v σ, Qv ls v σ → Qv' ls v σ) {ls : List SRec}
    {t : Expr} {σ : WRes} (h : lendEnd T₁ T0 Ψ Qv P ls t σ) : lendEnd T₁ T0 Ψ Qv' P ls t σ := by
  rcases h with ⟨v, rfl, hv⟩ | h
  · exact Or.inl ⟨v, rfl, hQ _ _ _ hv⟩
  · exact Or.inr h

/-! ### The unwinding frame at a `raise` -/

/-- **`ubind (N, D)` at a `raise`**: the finaliser runs on the frame `Fr` beside the argument, and
the `raise` goes on, its continuation holding nothing owned.  `ewp_unwind`'s `raise` case, at any
table beside the row's.  `[spec §19]` -/
theorem ewp_ubind_raise {T : OpTab} (hL : T.Local) (h0 : ∀ i, T 0 i = none) {Px : Table}
    (hPx : Px.Mono) (Nv Dv : Val) (Fr : List SRec → WProp) {Qd : List SRec → Val → WProp}
    (hQd : ∀ ls v ρ, Qd ls v ρ → v = .unit ∧ NoOwn ρ)
    (hD : ∀ ls, Entails (Fr ls) (wpTS ls (.app (.val Dv) (.val .unit)) Qd))
    {Q : List SRec → Val → WProp} {ls : List SRec} {K₁ : Kont} {n i : UInt32} {v : Val}
    {en : OpEnt} (hT : T n i = some en) (ha : en.abort = true) (hK₁ : K₁.Catches n = false)
    {σ₁ σ₂ σ : WRes} (hcσ : ResU.CompS σ₁ σ₂ σ)
    (h₁ : ((fun ρ => en.PA ls v ρ ∧ NoOwn ρ) ⋆ fun ρ => NoOwn ρ) σ₁) (hF : Fr ls σ₂) :
    ewpTS ls ((ubindK Nv Dv).plug (K₁.plug (raiseE (.val (opPayload n i v)))))
      (orTab (opTable T) Px) Q σ := by
  have hM := orTab_mono (opTable_mono T) hPx
  obtain ⟨ρa, ρn, hcan, ⟨hPA, hnA⟩, hn⟩ := h₁
  have hn0 : n ≠ 0 := fun h => by subst h; rw [h0 i] at hT; exact absurd hT (by simp)
  refine ewp_fold hM ?_
  refine wpG_head (fun μ => Head.ufin μ Nv Dv n i v K₁ hn0 hK₁) rfl _ _ σ ?_
  refine wpG_bind (.seq .hole (raiseE (.val (opPayload n i v)))) _ ls _ σ ?_
  let R : List SRec → WProp := fun ls => (fun τ => en.PA ls v τ ∧ NoOwn τ) ⋆ fun τ => NoOwn τ
  have hRs : ∀ ls'', (∀ x, x ∈ ls'' ↔ x ∈ ls) → Entails (R ls) (R ls'') := by
    rintro ls'' hs τ ⟨τa, τb, hcab, ⟨hPA', hnA'⟩, hnb⟩
    exact ⟨τa, τb, hcab, ⟨(hL n i en hT ls ls'' v τa (ext_of_same hs τa)).1 hPA', hnA'⟩, hnb⟩
  have h₂ := wpG_frame (e := .app (.val Dv) (.val .unit)) R hRs σ
    ⟨σ₂, σ₁, ResU.CompS.comm hcσ, (wpTS_iff_wpG _ _ _ _).mp (hD ls σ₂ hF),
      ρa, ρn, hcan, ⟨hPA, hnA⟩, hn⟩
  refine wpG_mono (fun ls'' t τ ht => ?_) h₂
  obtain ⟨τ₁, τ₂, hcτ, ⟨w, rfl, hw⟩, ra, rn, hcr, ⟨hPA', hnA'⟩, hnr⟩ := ht
  obtain ⟨rfl, hnw⟩ := hQd _ _ _ hw
  refine wpG_head (fun μ => Head.seq μ _) rfl _ _ τ ?_
  obtain ⟨z, hz, hcz⟩ := compS_lcomm hcr hcτ
  exact wpG_here _ _ _ τ (Or.inr (Or.inl (Or.inr ⟨.hole, n, i, v, en,
    pure_sep_mk ⟨rfl, rfl, hT, ha⟩
      ⟨ra, z, hcz, ⟨hPA', hnA'⟩, noOwn_compS hz hnw hnr⟩⟩)))

/-! ### The owner beside a callback that holds no lend -/

section
variable {T₁ T0 : OpTab} {α : Life} (hT₁ : T₁.LendAt α) (hL : T₁.Local)
  (h0 : ∀ i, T₁ 0 i = none) (hT0 : T0.LendAt α) (Nv Dv : Val) {Qd : List SRec → Val → WProp}
  (hQd : ∀ ls v ρ, Qd ls v ρ → v = .unit ∧ NoOwn ρ) (l : BoCa.Loc) (Tt : VTy) (δ : LSub)
  (hD : ∀ ls, Entails (owner l Tt δ ls) (wpTS ls (.app (.val Dv) (.val .unit)) Qd))
  (Ψi Ψo : List SRec → Expr → WProp) (Qx Q : List SRec → Val → WProp)
  (hk : ∀ ls v, Entails (Qx ls v) (ewpTS ls ((ubindK Nv Dv).plug (.val v)) (LTab T₁ T0 Ψo) Q))

theorem ubindK_comp_hasHnd (K₁ : Kont) (n : UInt32) (hK₁ : K₁.HasHnd n = false) :
    ((ubindK Nv Dv).comp K₁).HasHnd n = false := by
  rw [hasHnd_comp, hK₁]; simp [Kont.HasHnd, Expr.val, Val.pair]

include hT₁ hL h0 hT0 hQd hD hk in
/-- **The owner beside a callback that has left the lend behind**: at each graded stop the owner
joins the continuation's share; at a `raise` the finaliser runs on it; at the answer it is handed
to the callback's post (`postA`).  `[spec §48]` -/
theorem lendM_owner
    (hΨB : ∀ ls c σ σo σ', Ψi ls c σ → owner l Tt δ ls σo → ResU.CompS σ σo σ' →
      Ψo ls ((ubindK Nv Dv).plug c) σ') :
    ∀ {ls : List SRec} {e : Expr} {ρc : WRes},
      ewpTS ls e (LTab T₁ T0 Ψi) (postA l Tt δ α Qx) ρc →
      ∀ {ρo ρ : WRes}, owner l Tt δ ls ρo → ResU.CompS ρc ρo ρ →
        ewpTS ls ((ubindK Nv Dv).plug e) (LTab T₁ T0 Ψo) Q ρ := by
  have hM := LTab_mono T₁ T0 Ψo
  intro ls e ρc h
  refine ewp_ind (fun ls e ρc => ∀ {ρo ρ : WRes}, owner l Tt δ ls ρo → ResU.CompS ρc ρo ρ →
    ewpTS ls ((ubindK Nv Dv).plug e) (LTab T₁ T0 Ψo) Q ρ) ?_ h
  intro ls e ρc hs ρo ρ ho hc
  refine ewp_fold hM (wpG_bind (ubindK Nv Dv) e ls _ ρ ?_)
  have h₁ := wpG_frame (e := e) (owner l Tt δ) (fun ls' hs' => fun _ h => owner_same hs' h) ρ
    ⟨ρc, ρo, hc, wpG_lendEnd hs, ho⟩
  refine wpG_mono (fun ls' t σ ht => ?_) h₁
  obtain ⟨σ₁, σ₂, hcσ, hp, ho'⟩ := ht
  rcases hp with ⟨v, rfl, hv⟩ | hp | hp | ⟨K₁, n, i, v, en, rfl, hK₁, hT, ha, hPA, hnA⟩
  · exact ewp_unfold hM (hk ls' v σ (postA_apply hv ho' hcσ))
  · -- a graded stop: the owner joins the continuation's share
    obtain ⟨K₁, n, i, v, en, ρa, ρk, rfl, hK₁, hT, ha, hgc, hq, hck, hA, -, -, hcont⟩ :=
      performStop_graded_inv hT₁ hp
    obtain ⟨ρk', hk', hcσ'⟩ := compS_reassoc hck hcσ
    rw [← Kont.plug_comp]
    refine wpG_here _ _ _ σ (Or.inr (Or.inl (Or.inl (performStop_graded_mk
      (ubindK_comp_hasHnd Nv Dv K₁ n hK₁) hT ha hgc hq hcσ' hA
      fun ls'' hs'' w τ₁ τ₂ hB hcτ => ?_))))
    obtain ⟨z, hz, hcz⟩ := compS_exch hk' hcτ
    rw [Kont.plug_comp]
    exact hcont ls'' hs'' w τ₁ z hB hz (owner_same hs'' ho') hcz
  · -- a tick's stop: the owner joins its obligation
    obtain ⟨K₁, n, i, v, en, ρa, ρk, rfl, hK₁, hT, ha, hgc, hq, hck, hA, -, -, hcont⟩ :=
      performStop_graded_inv hT0 hp
    obtain ⟨ρk', hk', hcσ'⟩ := compS_reassoc hck hcσ
    rw [← Kont.plug_comp]
    refine wpG_here _ _ _ σ (Or.inr (Or.inr (performStop_graded_mk
      (ubindK_comp_hasHnd Nv Dv K₁ n hK₁) hT ha hgc hq hcσ' hA
      fun ls'' hs'' w τ₁ τ₂ hB hcτ => ?_)))
    obtain ⟨z, hz, hcz⟩ := compS_exch hk' hcτ
    rw [Kont.plug_comp]
    exact hΨB ls'' _ z σ₂ τ₂ (hcont ls'' hs'' w τ₁ z hB hz) (owner_same hs'' ho') hcz
  · -- a `raise`: the finaliser runs on the owner, and the `raise` goes on
    exact ewp_unfold hM (ewp_ubind_raise hL h0 (Table.Const.mono fun _ _ _ _ _ h => h) Nv Dv
      (owner l Tt δ) hQd hD hT ha hK₁ hcσ
      ⟨σ₁, PMap.empty, ResU.comp_empty_right σ₁, ⟨hPA, hnA⟩, noOwn_empty⟩ ho')


include hT₁ hL h0 hT0 hQd hD hk in
/-- **`[TR]` 6.65 across graded stops, under the unwinding frame.**  A callback run from
`ρ_b ● ℓ ↦ mut(α, v, ρ_P, P̂)`, `ρ_b ∈ Res_α`, at a lend's table (`OpTab.LendAt`) beside a tick
owing `Ψi`, whose answer hands the owner back (`postA`), is under `ubind (N, D)` in `ewpTS` from
`ℓ ↦ own(v) ● ρ_P ● ρ_b`, beside a tick owing `Ψo`.  At each segment's end the lend ends
(`wpG_M_frameAt`): at an answer the owner goes to `N`; at a `raise` to `D`; at a graded stop whose
share holds the cell, the continuation is resumed in the scope of the stop, with the lend made
again at `α` with the cell the stop held; at one whose share has left it, the owner goes on
beside the callback (`lendM_owner`).  A tick's obligation is carried by `hΨA` and `hΨB`, the
same two ways.  `[spec §48]` -/
theorem lendM_frame
    (hΨB : ∀ ls c σ σo σ', Ψi ls c σ → owner l Tt δ ls σo → ResU.CompS σ σo σ' →
      Ψo ls ((ubindK Nv Dv).plug c) σ')
    (hΨA : ∀ ls c (v'' : Val) (χ : WRes) (hχ : χ.InStratum α) (ls₀ : List SRec)
      (hw₀ : vC true Tt ls₀ δ v'' χ) (b z W τ : WRes), (∀ x, x ∈ ls ↔ x ∈ ls₀) →
      b.InStratum α → ResU.CompS b (viewCell l Tt δ ls₀ α v'' χ hχ hw₀) z → Ψi ls c z →
      ResU.CompS (ResU.single l (CellU.ownOf v'')) χ W → ResU.CompS W b τ →
      Ψo ls ((ubindK Nv Dv).plug c) τ)
    (ls₀ : List SRec) :
    ∀ {ls : List SRec} {e : Expr} {ρc : WRes},
      ewpTS ls e (LTab T₁ T0 Ψi) (postA l Tt δ α Qx) ρc →
      ∀ (v : Val) (ρP ρb ρlP ρ : WRes) (hPv : vC true Tt ls₀ δ v ρP) (houtP : ρP.InStratum α),
        (∀ x, x ∈ ls ↔ x ∈ ls₀) → ρb.InStratum α →
        ResU.CompS ρb (viewCell l Tt δ ls₀ α v ρP houtP hPv) ρc →
        ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP → ResU.CompS ρlP ρb ρ →
        ewpTS ls ((ubindK Nv Dv).plug e) (LTab T₁ T0 Ψo) Q ρ := by
  have hM := LTab_mono T₁ T0 Ψo
  intro ls e ρc h
  refine (ewp_ind (fun ls e ρc => ewpTS ls e (LTab T₁ T0 Ψi) (postA l Tt δ α Qx) ρc ∧
    ∀ (v : Val) (ρP ρb ρlP ρ : WRes) (hPv : vC true Tt ls₀ δ v ρP) (houtP : ρP.InStratum α),
        (∀ x, x ∈ ls ↔ x ∈ ls₀) → ρb.InStratum α →
        ResU.CompS ρb (viewCell l Tt δ ls₀ α v ρP houtP hPv) ρc →
        ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP → ResU.CompS ρlP ρb ρ →
        ewpTS ls ((ubindK Nv Dv).plug e) (LTab T₁ T0 Ψo) Q ρ) ?_ h).2
  intro ls e ρc hs
  refine ⟨ewp_fold (LTab_mono _ _ _) (ewpStep_mono (LTab_mono _ _ _) (fun _ _ _ h => h.1) hs), ?_⟩
  intro v ρP ρb ρlP ρ hPv houtP hs₀ hb hcb hclP hcρ
  have hs₀' : ∀ x, x ∈ ls₀ ↔ x ∈ ls := fun x => (hs₀ x).symm
  have hPv' : vC true Tt ls δ v ρP := vC_local true Tt (ext_of_same hs₀ ρP) hPv
  have hcell : viewCell l Tt δ ls α v ρP houtP hPv' = viewCell l Tt δ ls₀ α v ρP houtP hPv :=
    viewCell_congr hs₀' hPv' hPv
  have hrun := wpG_sameMem (wpG_viewStrat hb hcb (wpG_lendEnd hs))
  have hex := wpG_M_frameAt l Tt δ α v e ls ρP ρb ρlP ρ hPv' houtP hb hclP hcρ _
    (fun BM hBM => by
      rw [hcell] at hBM
      cases ResU.CompS.functional hBM hcb
      exact hrun)
  refine ewp_fold hM (wpG_bind (ubindK Nv Dv) e ls _ ρ (wpG_mono (fun ls'' t R hx => ?_) hex))
  obtain ⟨ρ', v'', χ, hχ, hw, ρ₁, y, ⟨hsm, hq, hstr⟩, hχv, hcase, hy₁, hy₂⟩ := hx
  have hkm : (CellU.mutOf α v'' χ hχ (QsAt Tt δ ls α) hw).kind ≠ Kind.imm := by
    rw [CellU.kind_mutOf]; exact fun c => Kind.noConfusion c
  -- the cell is not in `Res_α`
  have hnot : ∀ σ : WRes, σ.InStratum α →
      σ.get l = some (CellU.mutOf α v'' χ hχ (QsAt Tt δ ls α) hw) → False := by
    intro σ hσ hg
    have := hσ l _ hg
    rw [CellU.inStratum_mutOf] at this
    exact lt_irrefl _ this
  have hsm₀ : ∀ x, x ∈ ls'' ↔ x ∈ ls₀ := fun x => (hsm x).trans (hs₀ x)
  -- the owner the exit hands back
  obtain ⟨W, hW, hρ₁W⟩ := compS_reassoc hy₁ hy₂
  have hownk : (CellU.ownOf v'' : CellU BoCa.Loc BoCa.Val).kind ≠ Kind.imm := by
    rw [CellU.kind_ownOf]; exact fun c => Kind.noConfusion c
  have hWl : W.get l = some (CellU.ownOf v'') :=
    (ResU.CompS.get_left_of_ne_imm hW (ResU.single_get_self _ _) hownk).2
  have hown : ∀ ls3, (∀ x, x ∈ ls3 ↔ x ∈ ls'') → owner l Tt δ ls3 W := fun ls3 h' =>
    ⟨v'', _, χ, hW, rfl, vC_local true Tt (ext_of_same h' χ) hχv⟩
  have hw₀ : vC true Tt ls₀ δ v'' χ := vC_local true Tt (ext_of_same hs₀' χ) hw
  have hcell' : ResU.single l (CellU.mutOf α v'' χ hχ (QsAt Tt δ ls α) hw) =
      viewCell l Tt δ ls₀ α v'' χ hχ hw₀ := viewCell_congr hs₀' hw hw₀
  -- a stop whose share holds the cell: it sits in the share, not in the argument
  have hsplit : ∀ {ρa ρk : WRes}, ResU.CompS ρa ρk ρ' → ρa.InStratum α →
      ResU.CompS ρ₁ (ResU.single l (CellU.mutOf α v'' χ hχ (QsAt Tt δ ls α) hw)) ρ' →
      ResU.CompS ρa (ρk.del l) ρ₁ ∧
        ResU.CompS (ρk.del l) (ResU.single l (CellU.mutOf α v'' χ hχ (QsAt Tt δ ls α) hw)) ρk := by
    intro ρa ρk hck hαa hc1
    have hρ'l := (ResU.CompS.get_left_of_ne_imm (ResU.CompS.comm hc1)
      (ResU.single_get_self _ _) hkm).2
    have hρ₁l : ρ₁.get l = none := (ResU.CompS.get_left_of_ne_imm (ResU.CompS.comm hc1)
      (ResU.single_get_self _ _) hkm).1
    have hρkl : ρk.get l = some (CellU.mutOf α v'' χ hχ (QsAt Tt δ ls α) hw) := by
      rcases ResU.CompS.get_split_of_ne_imm hck hρ'l hkm with ⟨ha', -⟩ | ⟨-, hk'⟩
      · exact (hnot ρa hαa ha').elim
      · exact hk'
    have hk₁ := ResU.del_compS hρkl
    obtain ⟨X, hX, hXc⟩ := compS_reassoc' hk₁ hck
    have hXl : X.get l = none :=
      (ResU.CompS.get_left_of_ne_imm (ResU.CompS.comm hXc) (ResU.single_get_self _ _) hkm).1
    have hX₁ : ρ₁ = X := by
      apply PMap.ext; intro m
      by_cases hm : m = l
      · subst hm; rw [hρ₁l, hXl]
      · rw [← get_off_single hc1 hm, ← get_off_single hXc hm]
    subst hX₁
    exact ⟨hX, hk₁⟩
  -- the lend made again at a resumption, from the cell the stop held
  have hrel : ∀ {ρa ρk kS τ₁ τ₂ : WRes}, ResU.CompS ρa ρk ρ' →
      ResU.CompS (ρk.del l) (ResU.single l (CellU.mutOf α v'' χ hχ (QsAt Tt δ ls α) hw)) ρk →
      ResU.CompS (ρk.del l) W kS → ResU.CompS kS τ₁ τ₂ → τ₁.InStratum α →
      ∃ z b, ResU.CompS ρk τ₁ z ∧ b.InStratum α ∧
        ResU.CompS b (viewCell l Tt δ ls₀ α v'' χ hχ hw₀) z ∧ ResU.CompS W b τ₂ := by
    intro ρa ρk kS τ₁ τ₂ hck hk₁ hkS hcτ hτα
    obtain ⟨z, hz⟩ := compS_exists_swap hkS hcτ hk₁ hWl hownk
    obtain ⟨b', hb', hb'z⟩ := compS_exch hk₁ hz
    obtain ⟨bc, hbc, hWbc⟩ := compS_reassoc (ResU.CompS.comm hkS) hcτ
    cases ResU.CompS.functional hbc hb'
    have hstrk : (ρk.del l).InStratum α := del_inStratum_left (ResU.CompS.comm hck) hstr
    refine ⟨z, b', hz, inStratum_compS hb' hstrk hτα, ?_, hWbc⟩
    rw [← hcell']; exact hb'z
  rcases hq with ⟨v', rfl, hv⟩ | hp | hp | ⟨K₁, n, i, va, en, rfl, hK₁, hT, ha, hPA, hnA⟩
  · -- an answer: the box puts the cell in the leftover
    rcases hcase with ⟨-, rfl⟩ | hc1
    · exact ewp_unfold hM (hk ls'' v' R (hv.1 v'' _ y rfl hy₁ χ R hχv hy₂))
    · exact (hnot ρ' hv.2 (ResU.CompS.get_left_of_ne_imm (ResU.CompS.comm hc1)
        (ResU.single_get_self _ _) hkm).2).elim
  · -- a graded stop
    obtain ⟨K₁, n, i, va, en, ρa, ρk, rfl, hK₁, hT, ha, hgc, hqq, hck, hA, hαa, hans, hcont⟩ :=
      performStop_graded_inv hT₁ hp
    rw [← Kont.plug_comp]
    rcases hcase with ⟨-, rfl⟩ | hc1
    · -- the callback has left the cell behind: the owner goes on beside it
      obtain ⟨kS, hkS, hR⟩ := compS_reassoc hck hρ₁W
      refine wpG_here _ _ _ R (Or.inr (Or.inl (Or.inl (performStop_graded_mk
        (ubindK_comp_hasHnd Nv Dv K₁ n hK₁) hT ha hgc hqq hR hA
        fun ls3 hs3 w τ₁ τ₂ hB hcτ => ?_))))
      obtain ⟨z, hz, hcz⟩ := compS_exch hkS hcτ
      rw [Kont.plug_comp]
      exact lendM_owner hT₁ hL h0 hT0 Nv Dv hQd l Tt δ hD Ψi Ψo Qx Q hk hΨB
        (hcont ls3 hs3 w τ₁ z hB hz).1 (hown ls3 hs3) hcz
    · -- the share holds the cell: the lend is made again at the resumption
      obtain ⟨hX, hk₁⟩ := hsplit hck hαa hc1
      obtain ⟨kS, hkS, hR⟩ := compS_reassoc hX hρ₁W
      refine wpG_here _ _ _ R (Or.inr (Or.inl (Or.inl (performStop_graded_mk
        (ubindK_comp_hasHnd Nv Dv K₁ n hK₁) hT ha hgc hqq hR hA
        fun ls3 hs3 w τ₁ τ₂ hB hcτ => ?_))))
      obtain ⟨z, b, hz, hbα, hbz, hWb⟩ := hrel hck hk₁ hkS hcτ (hans ls3 w τ₁ hB)
      rw [Kont.plug_comp]
      exact (hcont ls3 hs3 w τ₁ z hB hz).2 v'' χ b W τ₂ hw₀ hχ
        (fun x => (hs3 x).trans (hsm₀ x)) hbα hbz hW hWb
  · -- a tick's stop: its obligation is carried, the same two ways
    obtain ⟨K₁, n, i, va, en, ρa, ρk, rfl, hK₁, hT, ha, hgc, hqq, hck, hA, hαa, hans, hcont⟩ :=
      performStop_graded_inv hT0 hp
    rw [← Kont.plug_comp]
    rcases hcase with ⟨-, rfl⟩ | hc1
    · obtain ⟨kS, hkS, hR⟩ := compS_reassoc hck hρ₁W
      refine wpG_here _ _ _ R (Or.inr (Or.inr (performStop_graded_mk
        (ubindK_comp_hasHnd Nv Dv K₁ n hK₁) hT ha hgc hqq hR hA
        fun ls3 hs3 w τ₁ τ₂ hB hcτ => ?_)))
      obtain ⟨z, hz, hcz⟩ := compS_exch hkS hcτ
      rw [Kont.plug_comp]
      exact hΨB ls3 _ z W τ₂ (hcont ls3 hs3 w τ₁ z hB hz) (hown ls3 hs3) hcz
    · obtain ⟨hX, hk₁⟩ := hsplit hck hαa hc1
      obtain ⟨kS, hkS, hR⟩ := compS_reassoc hX hρ₁W
      refine wpG_here _ _ _ R (Or.inr (Or.inr (performStop_graded_mk
        (ubindK_comp_hasHnd Nv Dv K₁ n hK₁) hT ha hgc hqq hR hA
        fun ls3 hs3 w τ₁ τ₂ hB hcτ => ?_)))
      obtain ⟨z, b, hz, hbα, hbz, hWb⟩ := hrel hck hk₁ hkS hcτ (hans ls3 w τ₁ hB)
      rw [Kont.plug_comp]
      exact hΨA ls3 _ v'' χ hχ ls₀ hw₀ b z W τ₂ (fun x => (hs3 x).trans (hsm₀ x)) hbα hbz
        (hcont ls3 hs3 w τ₁ z hB hz) hW hWb
  · -- a `raise`, held by its argument alone: the frame ends, and `D` runs on the owner
    have hαa := (hT₁ n i en hT).2.1 ls'' va ρ' hPA
    rcases hcase with ⟨-, rfl⟩ | hc1
    · exact ewp_unfold hM (ewp_ubind_raise hL h0 (Table.Const.mono fun _ _ _ _ _ h => h) Nv Dv
        (owner l Tt δ) hQd hD hT ha hK₁ hρ₁W
        ⟨ρ₁, PMap.empty, ResU.comp_empty_right ρ₁, ⟨hPA, hnA⟩, noOwn_empty⟩
        (hown ls'' (fun _ => Iff.rfl)))
    · exact (hnot ρ' hαa (ResU.CompS.get_left_of_ne_imm (ResU.CompS.comm hc1)
        (ResU.single_get_self _ _) hkm).2).elim

end

/-! ### A lend's row -/

theorem Row.Lend.nz {S : Row} {x : LifeVar} (hS : S.Lend x) : S.NZ :=
  fun o ho => (hS o ho).1

/-- A lend's row's table does not see `'x`: its argument and answer types are free of it. -/
theorem Row.Lend.tab_extend {S : Row} {x : LifeVar} (hS : S.Lend x) (δ : LSub) (α : Life) :
    Row.tab S (δ.extend x α) = Row.tab S δ := by
  funext n i
  unfold Row.tab
  cases hf : Row.find S n i with
  | none => rfl
  | some o =>
      obtain ⟨-, hx, -, hk⟩ := hS o (Row.find_mem hf).1
      have hB : ¬ VFree x o.B := by
        rcases hk with ha | ⟨-, -, hB, -⟩
        · rw [OpSig.B_zero ha]; exact id
        · exact hB
      have hc : capB o.q o.B = false := by
        rcases hk with ha | ⟨-, hq, -, -⟩
        · simp [capB, OpSig.B_zero ha, VTy.isZero]
        · simp [capB, hq]
      simp only [Option.map_some, OpSig.ent, vC_extend_of_not_free hx, vC_extend_of_not_free hB, hc,
        Bool.false_eq_true, if_false]

/-- **A lend's row's table is a lend's table at every lifetime**: its arguments and graded answers
are closed data (6.60, `vC_outlives`).  `[spec §48]` -/
theorem Row.Lend.lendAt {S : Row} {x : LifeVar} (hS : S.Lend x) (δ : LSub) (α : Life) :
    (Row.tab S δ).LendAt α := by
  intro n i en hT
  obtain ⟨o, hf, rfl⟩ := Row.tab_some hT
  obtain ⟨hn, hx, hA, hk⟩ := hS o (Row.find_mem hf).1
  have hfn := (Row.find_mem hf).2.1
  have hout : ∀ T : VTy, ¬ VFree x T → (∀ Δ a, VOutlives Δ a T) →
      ∀ ls w τ, vC true T ls δ w τ → τ.InStratum α := fun T hxT hT ls w τ h =>
    vC_outlives (Δ := LifeCtx.empty) (a := .var x) (models_empty_any _)
      (interp_ext_self δ x α) (hT _ _) true ls w τ (by rw [vC_extend_of_not_free hxT]; exact h)
  refine ⟨by rw [← hfn]; exact hn, hout o.A hx hA, ?_⟩
  rcases hk with ha | ⟨hc, hq, hxB, hB⟩
  · exact Or.inl ha
  · exact Or.inr ⟨hc, hq, hout o.B hxB hB⟩

theorem OpTab.LendAt.erase0 {T : OpTab} {α : Life} (h : T.LendAt α) : T.erase0.LendAt α := by
  intro n i en hT
  unfold OpTab.erase0 at hT; split at hT
  · cases hT
  · exact h n i en hT

theorem OpTab.LendAt.only0 {T : OpTab} {α : Life} (h : T.LendAt α) : T.only0.LendAt α := by
  intro n i en hT
  obtain ⟨rfl, rfl, hT0⟩ := OpTab.only0_some hT
  exact h _ _ en hT0

theorem OpTab.LendAt.closeAt {T : OpTab} {α : Life} (h : T.LendAt α) : T.closeAt.LendAt α := by
  intro n i en hT
  unfold OpTab.closeAt at hT; split at hT
  · cases hT₀ : T n i with
    | none => rw [hT₀] at hT; cases hT
    | some en₀ =>
        rw [hT₀] at hT; cases hT
        obtain ⟨hn, hA, hk⟩ := h n i en₀ hT₀
        refine ⟨hn, hA, ?_⟩
        rcases hk with ha | ⟨hc, hq, hB⟩
        · exact Or.inl ha
        · exact Or.inr ⟨hc, hq, fun ls w τ hb => hB ls w τ hb.1⟩
  · exact h n i en hT

theorem OpTab.Local.erase0 {T : OpTab} (h : T.Local) : T.erase0.Local := by
  intro n i en hT
  unfold OpTab.erase0 at hT; split at hT
  · cases hT
  · exact h n i en hT

theorem OpTab.Local.closeAt {T : OpTab} (h : T.Local) : T.closeAt.Local := by
  intro n i en hT ls ls' v ρ he
  unfold OpTab.closeAt at hT; split at hT
  · cases hT₀ : T n i with
    | none => rw [hT₀] at hT; cases hT
    | some en₀ =>
        rw [hT₀] at hT; cases hT
        exact ⟨(h n i en₀ hT₀ ls ls' v ρ he).1, fun hb => ⟨(h n i en₀ hT₀ ls ls' v ρ he).2 hb.1, hb.2⟩⟩
  · exact h n i en hT ls ls' v ρ he

/-- At a row without a tick's table the lend's table is the row's. -/
theorem ewp_LTab_empty {T : OpTab} {Ψ : List SRec → Expr → WProp} {ls : List SRec} {e : Expr}
    {Q : List SRec → Val → WProp} {ρ : WRes} :
    ewpTS ls e (LTab T OpTab.empty Ψ) Q ρ ↔ ewpTS ls e (opTable T) Q ρ := by
  constructor
  · intro h
    refine ewp_mono (opTable_mono T) (fun ls t Φ ρ hp => ?_) (fun _ _ _ h => h) h
    rcases hp with hp | hp
    · exact hp
    · obtain ⟨_, _, _, _, _, hp⟩ := hp
      exact absurd (pure_sep_iff.mp hp).1.2.2.1 (by simp [OpTab.empty])
  · intro h
    exact ewp_mono (LTab_mono T OpTab.empty Ψ) (fun ls t Φ ρ hp => Or.inl hp) (fun _ _ _ h => h) h

/-! ### The entry: the lend's lifetime, chosen once -/

/-- **6.65's entry**: H4 chooses the lend's lifetime `A` below `β`, every tag and the callback's
`fresh` bound, and the callback runs from the cell `ℓ ↦ mut(A, v, ρ_P, P̂)` beside `ρ_b ∈ Res_A`.
The rest of the lend is made at this `A`, every time.  `[spec §48]` -/
theorem lendM_entry {l : BoCa.Loc} {Tt : VTy} {δ : LSub} {β : Life}
    (hP : ∀ ls w σ, vC true Tt ls δ w σ → σ.InStratum β) {v : Val} {ls : List SRec}
    {X : Life → WProp} {ρ : WRes}
    (h : (ptoOwn l v ⋆ vC true Tt ls δ v ⋆
      fresh (fun α => ptoMutS l α ls (fun ls₀ => vC true Tt ls₀ δ) ─⋆ X α)) ρ) :
    ∃ (A : Life) (ρP ρb ρlP BM : WRes) (houtP : ρP.InStratum A) (hPv : vC true Tt ls δ v ρP),
      A ⊏ β ∧ ρb.InStratum A ∧ ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP ∧
      ResU.CompS ρlP ρb ρ ∧ ResU.CompS ρb (viewCell l Tt δ ls A v ρP houtP hPv) BM ∧ X A BM := by
  obtain ⟨γ, hγ⟩ := fresh_frame (ptoOwn l v ⋆ vC true Tt ls δ v) _ ρ
    (BoLo.sep_assoc' _ _ _ ρ h)
  obtain ⟨b₀, hb₀⟩ := exists_fresh ls
  set A : Life := b₀ ⊓ (↓(γ ⊓ β)) with hAdef
  have hAγ : A ⊏ γ :=
    lt_of_le_of_lt inf_le_right (lt_of_lt_of_le (Life.down_sqsubset _) inf_le_left)
  have hAβ : A ⊏ β :=
    lt_of_le_of_lt inf_le_right (lt_of_lt_of_le (Life.down_sqsubset _) inf_le_right)
  have hAtag : ∀ x ∈ ls, x.2 ⊐ A := fun x hx => lt_of_le_of_lt inf_le_left (hb₀ x hx)
  obtain ⟨hbody, houtρ⟩ := hγ A hAγ
  obtain ⟨ρlP, ρb, hcρ, hlP, hwand⟩ := hbody
  obtain ⟨hlPv, houtlP⟩ := hlP
  obtain ⟨ρl, ρP, hclP, hpl, hPv⟩ := hlPv
  subst hpl
  have houtP : ResU.InStratum A ρP := ResU.CompS.inStratum_right hclP houtlP
  have houtb : ResU.InStratum A ρb := ResU.CompS.inStratum_right hcρ houtρ
  have hunif : ∀ ls' w σ, vC true Tt ls' δ w σ → ResU.InStratum A σ := fun ls' w σ h m ψ hm =>
    CellU.InStratum.mono (le_of_lt hAβ) (hP ls' w σ h m ψ hm)
  have hofS : BoLo.ofS (QsAt Tt δ ls A) = fun w => vC true Tt ls δ w := by
    funext w σ
    exact propext ⟨fun h => h.2, fun h => ⟨hunif ls w σ h, h⟩⟩
  obtain ⟨hwit, hcellm⟩ := ptoMutX_create (l := l) (α := A) (le_refl A) hofS hAtag
    hunif houtP hPv
  have hbl : ρb.get l = none := by
    have hlP : ρlP.get l = some (CellU.ownOf v) :=
      (ResU.CompS.get_left_of_ne_imm hclP (ResU.single_get_self _ _)
        (by rw [CellU.kind_ownOf]; exact fun c => Kind.noConfusion c)).2
    exact (ResU.CompS.get_left_of_ne_imm hcρ hlP
      (by rw [CellU.kind_ownOf]; exact fun c => Kind.noConfusion c)).1
  obtain ⟨BM, hBM⟩ := (ResU.compS_defined_iff ρb (viewCell l Tt δ ls A v ρP houtP hPv)).mpr
    (fun m ψ₁ ψ₂ e₁ e₂ => by
      by_cases hm : m = l
      · subst hm; rw [hbl] at e₁; cases e₁
      · unfold viewCell at e₂; rw [ResU.single_get_ne _ hm] at e₂; cases e₂)
  exact ⟨A, ρP, ρb, ρlP, BM, houtP, hPv, hAβ, houtb, hclP, hcρ, hBM, hwand _ BM hcellm hBM⟩

/-! ### The lend at a row that holds `Div` -/

/-- **The candidate** of the coinduction at `cwp`: the unwinding frame around a callback of `cwp`,
either lent at `α` with the cell its last stop held, or with the owner beside it.  `[spec §48]` -/
def lendW (T : OpTab) (l : BoCa.Loc) (Tt : VTy) (δ : LSub) (α : Life)
    (Qx : List SRec → Val → WProp) (Nv Dv : Val) : List SRec → Expr → WProp := fun ls x ρ =>
  (∃ (e : Expr) (ρc : WRes) (ls₀ : List SRec) (v : Val) (ρP ρb ρlP : WRes)
      (hPv : vC true Tt ls₀ δ v ρP) (houtP : ρP.InStratum α),
    x = (ubindK Nv Dv).plug e ∧ cwp T (postA l Tt δ α Qx) ls e ρc ∧ (∀ x, x ∈ ls ↔ x ∈ ls₀) ∧
      ρb.InStratum α ∧ ResU.CompS ρb (viewCell l Tt δ ls₀ α v ρP houtP hPv) ρc ∧
      ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP ∧ ResU.CompS ρlP ρb ρ) ∨
  (∃ (e : Expr) (ρc ρo : WRes), x = (ubindK Nv Dv).plug e ∧
    cwp T (postA l Tt δ α Qx) ls e ρc ∧ owner l Tt δ ls ρo ∧ ResU.CompS ρc ρo ρ)

section
variable {T : OpTab} {α : Life} (hT : T.LendAt α) (hL : T.Local) (h0 : ∀ i, T 0 i = none)
  (Nv Dv : Val) {Qd : List SRec → Val → WProp}
  (hQd : ∀ ls v ρ, Qd ls v ρ → v = .unit ∧ NoOwn ρ) (l : BoCa.Loc) (Tt : VTy) (δ : LSub)
  (hD : ∀ ls, Entails (owner l Tt δ ls) (wpTS ls (.app (.val Dv) (.val .unit)) Qd))
  (Qx Q : List SRec → Val → WProp)
  (hkc : ∀ ls v, Entails (Qx ls v) (cwp T Q ls ((ubindK Nv Dv).plug (.val v))))

/-- The tick's obligations are both cases of the candidate's; their `Closing` the lend at the
closing table, where no tick's table is beside the row's. -/
abbrev noTick : List SRec → Expr → WProp := fun _ _ _ => False

include hT hL h0 hQd hD hkc in
theorem closing_lendM_owner {ls : List SRec} {c : Expr} {σ σo σ' : WRes}
    (hc : Closing T (postA l Tt δ α Qx) ls c σ) (ho : owner l Tt δ ls σo)
    (hcp : ResU.CompS σ σo σ') : Closing T Q ls ((ubindK Nv Dv).plug c) σ' :=
  ewp_LTab_empty.mp (lendM_owner (Ψi := noTick) (Ψo := noTick) hT.closeAt hL.closeAt
    (fun i => by rw [OpTab.closeAt_ne (fun h => divEff_ne_zero h.1.symm)]; exact h0 i)
    (fun _ _ _ h => by simp [OpTab.empty] at h) Nv Dv hQd l Tt δ hD Qx Q
    (fun ls v σ hσ => ewp_LTab_empty.mpr (closing_of_cwp (hkc ls v σ hσ)))
    (fun _ _ _ _ _ h => h.elim) (ewp_LTab_empty.mpr hc) ho hcp)

include hT hL h0 hQd hD hkc in
theorem closing_lendM {ls ls₀ : List SRec} {c : Expr} {v : Val} {ρP ρb ρlP ρc ρ : WRes}
    (hPv : vC true Tt ls₀ δ v ρP) (houtP : ρP.InStratum α)
    (hcl : Closing T (postA l Tt δ α Qx) ls c ρc) (hs : ∀ x, x ∈ ls ↔ x ∈ ls₀)
    (hb : ρb.InStratum α) (hcb : ResU.CompS ρb (viewCell l Tt δ ls₀ α v ρP houtP hPv) ρc)
    (hclP : ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP) (hcρ : ResU.CompS ρlP ρb ρ) :
    Closing T Q ls ((ubindK Nv Dv).plug c) ρ :=
  ewp_LTab_empty.mp (lendM_frame (Ψi := noTick) (Ψo := noTick) hT.closeAt hL.closeAt
    (fun i => by rw [OpTab.closeAt_ne (fun h => divEff_ne_zero h.1.symm)]; exact h0 i)
    (fun _ _ _ h => by simp [OpTab.empty] at h) Nv Dv hQd l Tt δ hD Qx Q
    (fun ls v σ hσ => ewp_LTab_empty.mpr (closing_of_cwp (hkc ls v σ hσ)))
    (fun _ _ _ _ _ h => h.elim) (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ h => h.elim) ls₀
    (ewp_LTab_empty.mpr hcl) v ρP ρb ρlP ρ hPv houtP hs hb hcb hclP hcρ)

include hT hL h0 hQd hD hkc in
/-- **The lend across graded stops at a row that holds `Div`**, by coinduction (`lendW`): a
segment of the callback is `lendM_frame` (lent) or `lendM_owner` (the owner beside) at the
segment's tables, a tick of the callback a graded stop whose continuation is owed the candidate
and `Closing`, which is the same lemma at the closing table.  `[spec §48]` -/
theorem cwp_lendM {ls : List SRec} {x : Expr} {ρ : WRes}
    (h : lendW T l Tt δ α Qx Nv Dv ls x ρ) : cwp T Q ls x ρ := by
  have hE0 := hT.erase0
  have hO0 := hT.only0
  have hL0 := hL.erase0
  have h00 : ∀ i, T.erase0 0 i = none := fun i => by
    rw [OpTab.erase0_ne (fun h => divEff_ne_zero h.1.symm)]; exact h0 i
  let W' : List SRec → Expr → WProp := fun ls e ρ => lendW T l Tt δ α Qx Nv Dv ls e ρ ∨ cwp T Q ls e ρ
  have hk : ∀ ls v, Entails (Qx ls v) (ewpTS ls ((ubindK Nv Dv).plug (.val v))
      (LTab T.erase0 T.only0 (owe T Q W')) Q) :=
    fun ls v σ hσ => cwpF_mono (fun _ _ _ h => Or.inr h) (cwp_out (hkc ls v σ hσ))
  have hΨB : ∀ ls c σ σo σ', owe T (postA l Tt δ α Qx) (cwp T (postA l Tt δ α Qx)) ls c σ →
      owner l Tt δ ls σo → ResU.CompS σ σo σ' → owe T Q W' ls ((ubindK Nv Dv).plug c) σ' :=
    fun ls c σ σo σ' hc ho hcp => ⟨Or.inl (Or.inr ⟨c, σ, σo, rfl, hc.1, ho, hcp⟩),
      closing_lendM_owner hT hL h0 Nv Dv hQd l Tt δ hD Qx Q hkc hc.2 ho hcp⟩
  have hΨA : ∀ ls c (v'' : Val) (χ : WRes) (hχ : χ.InStratum α) (ls₀ : List SRec)
      (hw₀ : vC true Tt ls₀ δ v'' χ) (b z W τ : WRes), (∀ x, x ∈ ls ↔ x ∈ ls₀) →
      b.InStratum α → ResU.CompS b (viewCell l Tt δ ls₀ α v'' χ hχ hw₀) z →
      owe T (postA l Tt δ α Qx) (cwp T (postA l Tt δ α Qx)) ls c z →
      ResU.CompS (ResU.single l (CellU.ownOf v'')) χ W → ResU.CompS W b τ →
      owe T Q W' ls ((ubindK Nv Dv).plug c) τ :=
    fun ls c v'' χ hχ ls₀ hw₀ b z W τ hs hb hbz hc hW hWτ =>
      ⟨Or.inl (Or.inl ⟨c, z, ls₀, v'', χ, b, W, hw₀, hχ, rfl, hc.1, hs, hb, hbz, hW, hWτ⟩),
        closing_lendM hT hL h0 Nv Dv hQd l Tt δ hD Qx Q hkc hw₀ hχ hc.2 hs hb hbz hW hWτ⟩
  refine cwp_coind_up (W := lendW T l Tt δ α Qx Nv Dv) (fun ls x ρ hx => ?_) h
  rcases hx with ⟨e, ρc, ls₀, v, ρP, ρb, ρlP, hPv, houtP, rfl, he, hs, hb, hcb, hclP, hcρ⟩ |
    ⟨e, ρc, ρo, rfl, he, ho, hcp⟩
  · exact lendM_frame (Ψi := owe T (postA l Tt δ α Qx) (cwp T (postA l Tt δ α Qx)))
      (Ψo := owe T Q W') hE0 hL0 h00 hO0 Nv Dv hQd l Tt δ hD Qx Q hk hΨB hΨA ls₀
      (cwp_out he) v ρP ρb ρlP ρ hPv houtP hs hb hcb hclP hcρ
  · exact lendM_owner (Ψi := owe T (postA l Tt δ α Qx) (cwp T (postA l Tt δ α Qx)))
      (Ψo := owe T Q W') hE0 hL0 h00 hO0 Nv Dv hQd l Tt δ hD Qx Q hk hΨB (cwp_out he) ho hcp

end

/-! ### `withbor` (2) at a lend's row -/

/-- The callback's answer, out of `['x]`, with the source handed back: `postA` from 6.65's box. -/
theorem postA_of_box {l : BoCa.Loc} {A B : VTy} {δ : LSub} {x : LifeVar} {α : Life}
    (hfree₂ : ¬ VFree x B) {ls : List SRec} {v : Val} {ρ : WRes}
    (h : vC true (.box (.var x) B) ls (δ.extend x α) v ρ) :
    postA l A δ α (fun ls v => vP B ls δ v ⋆ owner l A δ ls) ls v ρ := by
  obtain ⟨α', hα', hB, hout⟩ := h
  rw [interp_ext_self] at hα'
  cases Option.some.inj hα'
  have hB' : vP B ls δ v ρ := by rw [vC_extend_of_not_free hfree₂] at hB; exact hB
  refine ⟨fun w c₁ c₂ hc₁ hcc p₁ p₂ hp hcp => ?_, hout⟩
  obtain ⟨s, hs, hρs⟩ := compS_reassoc hcc hcp
  exact ⟨ρ, s, hρs, hB', w, c₁, p₁, hs, hc₁, hp⟩

/-- **`withbor` (2) at a lend's row**: `Ref A` lent as `Mut 'x A` to a callback whose row has
abortive and call-graded operations (`Row.Lend`).  `[TR]` 6.173's proof (`withbor2_compatX`):
the lend at a lifetime H4 chooses once (`lendM_entry`), then 6.65 across the callback's graded
stops under the unwinding frame (`lendM_frame`), coinductively where the row holds `Div`
(`cwp_lendM`).  Its side conditions are non-strict, read at `↓@bδ`.  `[spec §19, §23, §48]` -/
theorem withbor2L_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {A B : VTy} {S : Row} {d : Expr}
    (x : LifeVar) (hΓ : Ctx.DeadP Γ) (hside : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A)
    (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) (hS : S.Lend x)
    (hdc : closedAt 0 d = true) (hd : SemV Δ Γ d (.lolli (.ref A) .unit)) :
    SemV Δ Γ (withborUE d) (withbor2UTy x Δ.meetOfDom A B S) := by
  intro δ γ ls ρ hδ hg
  have hρ : ρ = PMap.empty := gSepC_deadP hΓ (gDenC_iff.mp hg).2
  subst hρ
  have hdg := semV_dead_closed hdc hd hδ hg
  show wpTS ls (substAll γ (withborUE d)) _ _
  rw [show substAll γ (withborUE d) = .val (withborUV d) from
    psub_closedAt _ γ (withborUE_closed hdc) (Nat.zero_le 0)]
  refine wpTS_val _ _ _ _ ?_
  intro ls₁ _ v₁ ρ₁ τ₀ hv₁ hcomp
  obtain rfl := eq_of_compS_empty_left hcomp
  obtain ⟨ℓ, vℓ, hs₁⟩ := hv₁
  obtain ⟨rfl, ρℓ, ρP, hcℓ, hown, hP⟩ := pure_sep_iff.mp hs₁
  intro vf ρ₂ τ hvf hc₂
  let T := Row.tab S δ
  let Nv : Val := Val.lam (.pair (.val (.loc ℓ)) (.var 0))
  let Dv : Val := Val.lam (.app d (.val (.loc ℓ)))
  let Qx : List SRec → Val → WProp := fun ls v => vP B ls δ v ⋆ owner ℓ A δ ls
  have hQd : ∀ ls v ρ, vP .unit ls δ v ρ → v = .unit ∧ NoOwn ρ := fun _ _ _ h => by
    obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, noOwn_empty⟩
  have hD : ∀ ls, Entails (owner ℓ A δ ls) (wpTS ls (.app (.val Dv) (.val .unit))
      (fun ls v => vP .unit ls δ v)) :=
    fun ls σ h => fin_run hdc rfl hdg ls σ (owner_iff.mp h)
  have hret : ∀ {Tb : Table}, Tb.Mono → ∀ ls v, Entails (Qx ls v)
      (ewpTS ls ((ubindK Nv Dv).plug (.val v)) Tb (fun ls v => vP (.tensor (.ref A) B) ls δ v)) :=
    fun hTb ls' v σ ⟨σ₁, σ₂, hcσ, hv, hFr⟩ => ewp_ret_pair hTb (.loc ℓ) rfl _ v
      ⟨.loc ℓ, v, pure_sep_mk rfl ⟨σ₂, σ₁, ResU.CompS.comm hcσ, owner_iff.mp hFr, hv⟩⟩
  -- the lend's lifetime bound: 6.60 at the non-strict side condition, every stratum below `↓β`
  obtain ⟨b, hdef, hO⟩ := hside
  obtain ⟨β, hb⟩ := hdef δ hδ
  have hβ := fun ls' w σ' h =>
    vC_outlivesLe hδ hb hO true ls' w σ' h _ (Life.down_sqsubset β)
  generalize Life.down β = β at hβ
  -- the callback, at every lend `α ⊏ ⊓Δδ`, in the relation at its row with 6.65's post
  obtain ⟨σ, hcσ, hcτ⟩ := compS_reassoc hcℓ hc₂
  obtain ⟨a₂, ha₂⟩ := ρ₂.exists_atLife
  obtain ⟨m, hm⟩ : ∃ m, Δ.meetOfDom.interp δ = some m :=
    Lifetime.Life.interp_defined_of_wf hδ (Lifetime.meetOfDomL_wf Δ.entries)
  have hfr : (ptoOwn ℓ vℓ ⋆ vC true A ls₁ δ vℓ ⋆ fresh (fun α => ptoMutS ℓ α ls₁
      (fun ls₀ => vC true A ls₀ δ) ─⋆ effWp (Row.divB S) T (postA ℓ A δ α Qx) ls₁
        (.app (.app (.val vf) (.val .unit)) (.val (.loc ℓ))))) τ := by
    refine ⟨ρℓ, σ, hcτ, hown, ρP, ρ₂, hcσ, hP, a₂ ⊓ m, fun α hα =>
      ⟨?_, outlives_of_atLife ha₂ (lt_of_lt_of_le hα inf_le_left)⟩⟩
    intro ρm σ' hm' hcm
    have hmut' : vP (.mut (.var x) A) ls₁ (δ.extend x α) (.loc ℓ) ρm := by
      have e : (fun ls₀ => vC true A ls₀ (δ.extend x α)) = (fun ls₀ => vC true A ls₀ δ) :=
        funext fun ls₀ => vC_extend_of_not_free hfree₁ true ls₀ δ α
      refine ⟨α, interp_ext_self δ x α, ℓ, pure_sep_mk rfl ?_⟩
      show ptoMutS ℓ α ls₁ (fun ls₀ => vC true A ls₀ (δ.extend x α)) ρm
      rw [e]; exact hm'
    have hlt : LtLife δ Δ.meetOfDom α := ⟨m, hm, lt_of_lt_of_le hα inf_le_right⟩
    have hcb := (hvf ls₁ (Ext.refl _ _) α PMap.empty ρ₂ ⟨rfl, hlt⟩ (ResU.comp_empty_right ρ₂))
      (.loc ℓ) ρm σ' hmut' hcm
    rw [cC_effOf_wp, hS.tab_extend δ α] at hcb
    cases hdv : Row.divB S <;> rw [hdv] at hcb
    · exact ewp_mono (opTable_mono _) (fun _ _ _ _ h => h)
        (fun _ _ _ h => postA_of_box hfree₂ h) hcb
    · exact cwp_post (fun _ _ _ h => postA_of_box hfree₂ h) hcb
  obtain ⟨α, ρP', ρb, ρlP, BM, houtP, hPv, hαβ, hb', hclP, hcρ, hBM, hX⟩ :=
    lendM_entry (Tt := A) hβ hfr
  refine (cC_effOf_wp S _ ls₁ δ _ τ).mpr ?_
  have hTL := hS.lendAt δ α
  have hL := Row.tab_local S δ
  have h0 := Row.tab_zero hS.nz δ
  cases hdv : Row.divB S <;> rw [hdv] at hX
  · -- a row without `Div`: one induction
    refine withborUE_beta (opTable_mono _) hdc (.loc ℓ) rfl vf ?_
    exact ewp_LTab_empty.mp (lendM_frame (Ψi := noTick) (Ψo := noTick) hTL hL h0
      (fun _ _ _ h => by simp [OpTab.empty] at h) Nv Dv hQd ℓ A δ hD Qx _
      (fun ls v σ hσ => ewp_LTab_empty.mpr (hret (opTable_mono _) ls v σ hσ))
      (fun _ _ _ _ _ h => h.elim) (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ h => h.elim) ls₁
      (ewp_LTab_empty.mpr hX) vℓ ρP' ρb ρlP τ hPv houtP (fun _ => Iff.rfl) hb' hBM hclP hcρ)
  · -- a row that holds `Div`: by coinduction
    refine cwp_roll (withborUE_beta (divTab_mono _ _ _) hdc (.loc ℓ) rfl vf (cwp_out ?_))
    exact cwp_lendM hTL hL h0 Nv Dv hQd ℓ A δ hD Qx _
      (fun ls v σ hσ => cwp_roll (hret (divTab_mono _ _ _) ls v σ hσ))
      (Or.inl ⟨_, BM, ls₁, vℓ, ρP', ρb, ρlP, hPv, houtP, rfl, hX, fun _ => Iff.rfl, hb', hBM, hclP,
        hcρ⟩)

end BoCa.Fig16.LogRel.Core

end
