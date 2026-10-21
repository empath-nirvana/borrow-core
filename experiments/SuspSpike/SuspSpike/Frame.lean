import SuspSpike.FrameAt

/-!
# SuspSpike — class 1's frame: a lend across call-like stops, lent again at the same lifetime

`ewpTS_M_frameC` is `[TR]` 6.65 over `ewpTS` at a class-1 table (`CallRow`): every stop of the
callback is a call-like operation, whose continuation is owed only at lists with the stop's
members. At a stop the lend ends as at a return (`wpG_M_frameAt`, the printed exit); the frame's
stop owes its continuation the owner. At the resumption the frame lends again **at the lifetime
it lent at, with the cell the stop held**, so the callback's continuation gets back exactly the
resource it stopped with. No value is moved to another lifetime.

* `frameAt`: the induction on the callback's `ewpTS`;
* `ownerFrame`: the callback no longer holds the view at a stop (it dropped it); the frame keeps
  the owner beside it and gives it to the callback's return (mode B of `DESIGN.md` §4);
* `wpG_viewStrat`: at the end of a run started from `Res_α ● ℓ ↦ mut(α, …)`, the share less the
  cell at `ℓ` is in `Res_α`. It is proved from `Six27S`, 6.27's stratum with the cell set aside, a
  statement about `↭` alone, not derived here (`Six27S` is a hypothesis of this file's theorems).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace SuspSpike
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Kont Step1N performE raiseE opPayload)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### The stratum with the cell set aside -/

/-- **6.27's stratum with the cell set aside.** If `@ρ ⊐ α` and
`ρ ● ℓ ↦ mut(α, v, ρ_v, P̂) ↭ ρ′`, then `ρ′/ℓ ∈ Res_α`: `↭` keeps every borrow (its two clauses),
and the only borrow of the left side not in `Res_α` is the one at `ℓ`. Stated, not derived here. -/
def Six27S : Prop :=
  ∀ (l : BoCa.Loc) (α : Life) (v : BoCa.Val) (ρ ρv M ρ' : WRes) (h : ρv.InStratum α)
    (P : BoCa.Val → SPropS BoCa.Loc BoCa.Val α) (hw : P v ⟨ρv, h⟩),
    ρ.InStratum α → ResU.CompS ρ (ResU.single l (CellU.mutOf α v ρv h P hw)) M →
    ResU.UpdV M ρ' → (ρ'.del l).InStratum α

/-- A table's arguments lie in `Res_α` (closed data). -/
def ArgIn (α : Life) (T : OpTab) : Prop :=
  ∀ n i en, T n i = some en → en.abort = false → ∀ ls w τ, en.PA ls w τ → τ.InStratum α

theorem del_inStratum_left {ρ₁ ρ₂ ρ : WRes} (h : ResU.CompS ρ₁ ρ₂ ρ) {α : Life} {l : BoCa.Loc}
    (hρ : (ρ.del l).InStratum α) : (ρ₁.del l).InStratum α := by
  intro m ψ e
  by_cases hm : m = l
  · subst hm; rw [ResU.del_get_self] at e; cases e
  · rw [ResU.del_get_ne _ hm] at e
    exact ResU.CompS.inStratum_left_at h
      (fun φ hφ => hρ m φ (by rw [ResU.del_get_ne _ hm]; exact hφ)) e

/-- At the end of a run started from `Res_α ● ℓ ↦ mut(α, …)`, the share less `ℓ` is in `Res_α`. -/
theorem wpG_viewStrat (hS : Six27S) {l : BoCa.Loc} {α : Life} {v : BoCa.Val} {ρv : WRes}
    {h : ρv.InStratum α} {P : BoCa.Val → SPropS BoCa.Loc BoCa.Val α} {hw : P v ⟨ρv, h⟩}
    {ρb ρ : WRes} (hout : ρb.InStratum α)
    (hcomp : ResU.CompS ρb (ResU.single l (CellU.mutOf α v ρv h P hw)) ρ)
    {ls : List SRec} {e : Expr} {Q : List SRec → Expr → WProp} (hq : wpG ls e Q ρ) :
    wpG ls e (fun ls' t σ => Q ls' t σ ∧ (σ.del l).InStratum α) ρ := by
  intro ρf fρ ps h1 h2 h3 h4 A k
  obtain ⟨ρ', ρp, fρ', fρ'p, π, t, μ, μ', ps', ls', a1, a2, a3, a4, a5, a6, a7, a8, a9, a10,
    a11, a12, a13, a14, a15⟩ := hq ρf fρ ps h1 h2 h3 h4 A k
  exact ⟨ρ', ρp, fρ', fρ'p, π, t, μ, μ', ps', ls', a1, a2, a3, a4, a5, a6, a7, a8, a9, a10,
    a11, a12, a13, a14, a15, del_inStratum_left a8 (hS l α v ρb ρv ρ π h P hw hout hcomp a9)⟩

/-! ### The stored predicate in scope -/

theorem QsAt_congr {T : VTy} {δ : LSub} {ls ls' : List SRec} (hs : SameMem ls ls') (A : Life) :
    QsAt T δ ls A = QsAt T δ ls' A := by
  funext w r
  exact propext ⟨fun h => vC_local true T (ext_of_same hs r.1) h,
    fun h => vC_local true T (ext_of_same hs.symm r.1) h⟩

theorem mutOf_congr {A : Life} {v : BoCa.Val} {ρP : WRes} {h : ρP.InStratum A}
    {Q Q' : BoCa.Val → SPropS BoCa.Loc BoCa.Val A} (hQ : Q = Q') (hw : Q v ⟨ρP, h⟩)
    (hw' : Q' v ⟨ρP, h⟩) : CellU.mutOf A v ρP h Q hw = CellU.mutOf A v ρP h Q' hw' := by
  subst hQ; rfl

/-- The cell a lend holds is the same at two lists with the same members. -/
theorem viewCell_congr {l : BoCa.Loc} {T : VTy} {δ : LSub} {ls ls' : List SRec} (hs : SameMem ls ls')
    {A : Life} {v : BoCa.Val} {ρP : WRes} {h : ρP.InStratum A} (hw : vC true T ls δ v ρP)
    (hw' : vC true T ls' δ v ρP) : viewCell l T δ ls A v ρP h hw = viewCell l T δ ls' A v ρP h hw' :=
  congrArg (ResU.single l) (mutOf_congr (QsAt_congr hs A) hw hw')

/-! ### Stops at a class-1 table -/

theorem stopC_dest {T : OpTab} {C : Grade} (hC : CallRow T C) {ls : List SRec} {t : Expr}
    {Φ : List SRec → Expr → WProp} {ρ : WRes} (h : opTableC T C ls t Φ ρ) :
    ∃ (K : Kont) (n i : UInt32) (v : Val) (en : OpEnt) (ρa ρk : WRes),
      t = K.plug (performE (.val (opPayload n i v))) ∧ K.HasHnd n = false ∧ T n i = some en ∧
      en.abort = false ∧ ResU.CompS ρa ρk ρ ∧ en.PA ls v ρa ∧ contShareC en ls K Φ ρk := by
  rcases h with ⟨K, n, i, v, en, hp⟩ | ⟨K, n, i, v, en, hp⟩
  · obtain ⟨⟨ht, hK, hT, ha⟩, ρa, ρk, hc, hA, hk⟩ := pure_sep_iff.mp hp
    rw [shareAt_true (hC.1 n i en hT).1] at hk
    exact ⟨K, n, i, v, en, ρa, ρk, ht, hK, hT, ha, hc, hA, hk⟩
  · obtain ⟨⟨-, -, hT, ha⟩, -⟩ := pure_sep_iff.mp hp
    exact absurd ha (by rw [(hC.1 n i en hT).2.2]; decide)

theorem stopC_mk {T : OpTab} {C : Grade} (hC : CallRow T C) {ls : List SRec}
    {Φ : List SRec → Expr → WProp} {K : Kont} {n i : UInt32} {v : Val} {en : OpEnt}
    {ρa ρk ρ : WRes} (hK : K.HasHnd n = false) (hT : T n i = some en) (ha : en.abort = false)
    (hc : ResU.CompS ρa ρk ρ) (hA : en.PA ls v ρa) (hk : contShareC en ls K Φ ρk) :
    opTableC T C ls (K.plug (performE (.val (opPayload n i v)))) Φ ρ :=
  Or.inl ⟨K, n, i, v, en, pure_sep_mk ⟨rfl, hK, hT, ha⟩
    ⟨ρa, ρk, hc, hA, by rw [shareAt_true (hC.1 n i en hT).1]; exact hk⟩⟩

/-! ### The owner, and the callback's post -/

/-- The lender's place, owned: `∃w. ℓ ↦ w ⋆ 𝒱⟦T⟧(ls)δ(w)`. -/
def owner (l : BoCa.Loc) (T : VTy) (δ : LSub) (ls : List SRec) : WProp :=
  ex fun w => ptoOwn l w ⋆ vC true T ls δ w

theorem owner_same {l : BoCa.Loc} {T : VTy} {δ : LSub} {ls ls' : List SRec} (hs : SameMem ls ls')
    {ρ : WRes} (h : owner l T δ ls ρ) : owner l T δ ls' ρ := by
  obtain ⟨w, ρ₁, ρ₂, hc, ho, hv⟩ := h
  exact ⟨w, ρ₁, ρ₂, hc, ho, vC_local true T (ext_of_same hs ρ₂) hv⟩

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

/-! ### Mode B: the owner held beside the callback -/

/-- **The owner beside a callback that holds no lend.** A callback at a class-1 table whose
return hands the owner back (`postA`), run beside the owner, is in `ewpTS` at the table. At each
stop the owner joins the continuation's share; at the return it is handed to the callback's post.
-/
theorem ownerFrame {T : OpTab} {C : Grade} (hC : CallRow T C) (l : BoCa.Loc) (Tt : VTy)
    (δ : LSub) (α : Life) (Q : List SRec → Val → WProp) :
    ∀ {ls : List SRec} {e : Expr} {ρc : WRes}, ewpTS ls e (opTableC T C) (postA l Tt δ α Q) ρc →
      ∀ {ρo ρ : WRes}, owner l Tt δ ls ρo → ResU.CompS ρc ρo ρ →
        ewpTS ls e (opTableC T C) Q ρ := by
  have hM := opTableC_mono T C
  intro ls e ρc h
  refine ewp_ind (fun ls e ρc => ∀ {ρo ρ : WRes}, owner l Tt δ ls ρo → ResU.CompS ρc ρo ρ →
    ewpTS ls e (opTableC T C) Q ρ) ?_ h
  intro ls e ρc hs ρo ρ ho hc
  refine ewp_fold hM ?_
  have h₁ := wpG_frame (e := e) (owner l Tt δ) (fun ls' hs' => fun _ h => owner_same hs' h) ρ
    ⟨ρc, ρo, hc, hs, ho⟩
  refine wpG_mono (fun ls' t σ ht => ?_) h₁
  obtain ⟨σ₁, σ₂, hcσ, hp, ho'⟩ := ht
  rcases hp with ⟨v, rfl, hv⟩ | hp
  · exact Or.inl ⟨v, rfl, postA_apply hv ho' hcσ⟩
  · obtain ⟨K, n, i, v, en, ρa, ρk, rfl, hK, hT, ha, hck, hA, hk⟩ := stopC_dest hC hp
    obtain ⟨ρk', hk', hcσ'⟩ := compS_reassoc hck hcσ
    refine Or.inr (stopC_mk hC hK hT ha hcσ' hA fun ls'' hs'' w τ₁ τ₂ hB hcτ => ?_)
    obtain ⟨z, hz, hcz⟩ := compS_exch hk' hcτ
    exact hk ls'' hs'' w τ₁ z hB hz (owner_same hs'' ho') hcz

/-! ### Class 1's frame -/

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

/-- **Class 1's frame at the lend's lifetime.** A callback at a class-1 table, run from
`ρ_b ● ℓ ↦ mut(α, v, ρ_P, P̂)` with `ρ_b ∈ Res_α`, whose return hands the owner back
(`postA`), is in `ewpTS` at the table from `ℓ ↦ own(v) ● ρ_P ● ρ_b`. At each stop the lend ends
(`wpG_M_frameAt`); the continuation's share keeps the owner; at the resumption, at a list with the
stop's members, the lend is made again at `α` with the cell the stop held, and the callback's own
continuation runs from exactly the resource it stopped with. A stop at which the callback no longer
holds the cell continues with the owner beside it (`ownerFrame`). -/
theorem frameAt (hS : Six27S) {T : OpTab} {C : Grade} (hC : CallRow T C)
    (hArg : ∀ α, ArgIn α T) (l : BoCa.Loc) (Tt : VTy) (δ : LSub) (α β : Life) (hαβ : α ⊏ β)
    (hP : ∀ ls w σ, vC true Tt ls δ w σ → σ.InStratum β) (Q : List SRec → Val → WProp)
    (ls₀ : List SRec) :
    ∀ {ls : List SRec} {e : Expr} {ρc : WRes},
      ewpTS ls e (opTableC T C) (postA l Tt δ α Q) ρc →
      ∀ (v : Val) (ρP ρb ρlP ρ : WRes) (hPv : vC true Tt ls₀ δ v ρP) (houtP : ρP.InStratum α),
        SameMem ls₀ ls → ρb.InStratum α →
        ResU.CompS ρb (viewCell l Tt δ ls₀ α v ρP houtP hPv) ρc →
        ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP → ResU.CompS ρlP ρb ρ →
        ewpTS ls e (opTableC T C) Q ρ := by
  have hM := opTableC_mono T C
  intro ls e ρc h
  refine (ewp_ind (fun ls e ρc => ewpTS ls e (opTableC T C) (postA l Tt δ α Q) ρc ∧
    ∀ (v : Val) (ρP ρb ρlP ρ : WRes) (hPv : vC true Tt ls₀ δ v ρP) (houtP : ρP.InStratum α),
        SameMem ls₀ ls → ρb.InStratum α →
        ResU.CompS ρb (viewCell l Tt δ ls₀ α v ρP houtP hPv) ρc →
        ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP → ResU.CompS ρlP ρb ρ →
        ewpTS ls e (opTableC T C) Q ρ) ?_ h).2
  intro ls e ρc hs
  refine ⟨ewp_fold hM (ewpStep_mono hM (fun _ _ _ h => h.1) hs), ?_⟩
  intro v ρP ρb ρlP ρ hPv houtP hs₀ hb hcb hclP hcρ
  have hPv' : vC true Tt ls δ v ρP := vC_local true Tt (ext_of_same hs₀ ρP) hPv
  have hcell : viewCell l Tt δ ls α v ρP houtP hPv' = viewCell l Tt δ ls₀ α v ρP houtP hPv :=
    viewCell_congr hs₀.symm hPv' hPv
  have hrun := wpG_sameMem (wpG_viewStrat hS hb hcb hs)
  have hex := wpG_M_frameAt l Tt δ α β hαβ hP v e ls ρP ρb ρlP ρ hPv' houtP hb hclP hcρ _
    (fun BM hBM => by
      rw [hcell] at hBM
      cases ResU.CompS.functional hBM hcb
      exact hrun)
  refine ewp_fold hM (wpG_mono (fun ls'' t R hx => ?_) hex)
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
  rcases hq with ⟨v', rfl, hv⟩ | hq
  · -- a return: the box puts the cell in the leftover
    rcases hcase with ⟨-, rfl⟩ | hc1
    · exact Or.inl ⟨v', rfl, hv.1 v'' _ y rfl hy₁ χ R hχv hy₂⟩
    · exact (hnot ρ' hv.2 (ResU.CompS.get_left_of_ne_imm (ResU.CompS.comm hc1)
        (ResU.single_get_self _ _) hkm).2).elim
  obtain ⟨K, n, i, va, en, ρa, ρk, rfl, hK, hT, ha, hck, hA, hk⟩ := stopC_dest hC hq
  have hsm₀ : SameMem ls₀ ls'' := hs₀.trans hsm
  -- the owner the exit hands back
  obtain ⟨W, hW, hρ₁W⟩ := compS_reassoc hy₁ hy₂
  have hownk : (CellU.ownOf v'' : CellU BoCa.Loc BoCa.Val).kind ≠ Kind.imm := by
    rw [CellU.kind_ownOf]; exact fun c => Kind.noConfusion c
  have hWl : W.get l = some (CellU.ownOf v'') :=
    (ResU.CompS.get_left_of_ne_imm hW (ResU.single_get_self _ _) hownk).2
  have hown : ∀ ls3, SameMem ls'' ls3 → owner l Tt δ ls3 W := fun ls3 h' =>
    ⟨v'', _, χ, hW, rfl, vC_local true Tt (ext_of_same h' χ) hχv⟩
  rcases hcase with ⟨-, rfl⟩ | hc1
  · -- the callback has left the cell behind: the owner goes on beside it
    obtain ⟨kS, hkS, hR⟩ := compS_reassoc hck hρ₁W
    refine Or.inr (stopC_mk hC hK hT ha hR hA fun ls3 hs3 w τ₁ τ₂ hB hcτ => ?_)
    obtain ⟨z, hz, hcz⟩ := compS_exch hkS hcτ
    exact ownerFrame hC l Tt δ α Q (hk ls3 hs3 w τ₁ z hB hz).1 (hown ls3 hs3) hcz
  · -- the callback holds the cell: it is in the continuation's share
    have hρ'l := (ResU.CompS.get_left_of_ne_imm (ResU.CompS.comm hc1)
      (ResU.single_get_self _ _) hkm).2
    have hρ₁l : ρ₁.get l = none := (ResU.CompS.get_left_of_ne_imm (ResU.CompS.comm hc1)
      (ResU.single_get_self _ _) hkm).1
    have hρkl : ρk.get l = some (CellU.mutOf α v'' χ hχ (QsAt Tt δ ls α) hw) := by
      rcases ResU.CompS.get_split_of_ne_imm hck hρ'l hkm with ⟨ha', -⟩ | ⟨-, hk'⟩
      · exact (hnot ρa (hArg α n i en hT ha ls'' va ρa hA) ha').elim
      · exact hk'
    have hk₁ := ResU.del_compS hρkl
    obtain ⟨X, hX, hXc⟩ := compS_reassoc' hk₁ hck
    have hXl : X.get l = none :=
      (ResU.CompS.get_left_of_ne_imm (ResU.CompS.comm hXc) (ResU.single_get_self _ _) hkm).1
    -- `ρ₁` is `ρ_a ● ρ_k/ℓ`: both are `ρ′` less the cell
    have hX₁ : ρ₁ = X := by
      apply PMap.ext; intro m
      by_cases hm : m = l
      · subst hm; rw [hρ₁l, hXl]
      · rw [← get_off_single hc1 hm, ← get_off_single hXc hm]
    subst hX₁
    obtain ⟨kS, hkS, hR⟩ := compS_reassoc hX hρ₁W
    have hstrk : (ρk.del l).InStratum α := del_inStratum_left (ResU.CompS.comm hck) hstr
    refine Or.inr (stopC_mk hC hK hT ha hR hA fun ls3 hs3 w τ₁ τ₂ hB hcτ => ?_)
    obtain ⟨z, hz⟩ := compS_exists_swap hkS hcτ hk₁ hWl hownk
    have hτα : τ₁.InStratum α := hC.2 α n i en hT ha ls3 w τ₁ hB
    obtain ⟨b', hb', hb'z⟩ := compS_exch hk₁ hz
    obtain ⟨bc, hbc, hWbc⟩ := compS_reassoc (ResU.CompS.comm hkS) hcτ
    cases ResU.CompS.functional hbc hb'
    have hw₀ : vC true Tt ls₀ δ v'' χ := vC_local true Tt (ext_of_same hs₀.symm χ) hw
    have hcell' : ResU.single l (CellU.mutOf α v'' χ hχ (QsAt Tt δ ls α) hw) =
        viewCell l Tt δ ls₀ α v'' χ hχ hw₀ := viewCell_congr hs₀.symm hw hw₀
    rw [hcell'] at hb'z
    exact (hk ls3 hs3 w τ₁ z hB hz).2 v'' χ b' W τ₂ hw₀ hχ (hsm₀.trans hs3)
      (inStratum_compS hb' hstrk hτα) hb'z hW hWbc

/-- **Class 1's frame: `[TR]` 6.65 over `ewpTS` at a class-1 table.** The precondition is 6.65's,
and its callback is Core's (`∀'x`, a wand over the view, answering in `[α] ∀v′. ℓ ↦ v′ ─⋆ P̂ ─⋆
Q`). The first lend is 6.65's entry as printed, H4 choosing its lifetime; from then on the frame
is `frameAt` at that lifetime. -/
theorem ewpTS_M_frameC (hS : Six27S) {T : OpTab} {C : Grade} (hC : CallRow T C)
    (hArg : ∀ α, ArgIn α T) (l : BoCa.Loc) (Tt : VTy) (δ : LSub) (β : Life)
    (hP : ∀ ls w σ, vC true Tt ls δ w σ → σ.InStratum β) (v : Val) (e : Expr) (ls : List SRec)
    (Q : List SRec → Val → WProp) :
    Entails
      (ptoOwn l v ⋆ vC true Tt ls δ v ⋆
        fresh (fun α => ptoMutS l α ls (fun ls₀ => vC true Tt ls₀ δ) ─⋆
          ewpTS ls e (opTableC T C) (postA l Tt δ α Q)))
      (ewpTS ls e (opTableC T C) Q) := by
  intro ρ hH2
  obtain ⟨γ, hγ⟩ := fresh_frame (ptoOwn l v ⋆ vC true Tt ls δ v) _ ρ
    (BoLo.sep_assoc' _ _ _ ρ hH2)
  -- H4: a lifetime shorter than `γ`, `β` and every tag
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
  -- the lend's cell composes with the rest: `ρ_b` holds nothing at `ℓ`
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
  exact frameAt hS hC hArg l Tt δ A β hAβ hP Q ls (hwand _ BM hcellm hBM) v ρP ρb ρlP ρ hPv houtP
    (SameMem.refl ls) houtb hBM hclP hcρ

end SuspSpike

end
