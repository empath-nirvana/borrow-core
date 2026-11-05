import Core.Chain.SI.LendX
import Core.Chain.SI.Uncapture

/-!
# The counted `imm` lend across stops, at `erwpX`  `[spec §62]`

`docs/new-core/scope-821-loans.md`, stage 2. An `imm` lend whose cell `ℓ` is masked at the lend's
authority (`Auth.lend κ`, held by a whole token `[κ]_1` the lender keeps) is opened at the start of one segment and ended at the
start of a later one. Between them it is held across any number of stops: the run's continuation
is the same `erwpX` at the same mask, and `↭` is not read at `ℓ`.

* **Open** (`rwpGX_lendOpen`): `ℓ ↦ own(v)` becomes `ℓ ↦ imm({α}, v, ∅)` at a fresh `α`, its record
  joins the records proper (`capture_world`), and `[α]_1` is minted. The run from the lent
  resource is the run from the owned one: they differ only at `ℓ`, which is masked, and in the
  record at `ℓ`, which the records clause does not compare (`RecAgree`).
* **End** (`rwpGX_lendEnd`): holding `[α]_1` and the cell, the record is ended
  (`uncapture_world`), `ℓ ↦ own(v)` is back and `[α]_1` is consumed.

**What the end reads of the frame** (`lendEnd_frame`). The end is at a mask holding `ℓ`, so `↭`
through the body says nothing at `ℓ` (`rwpGX_lend` reads it there through 6.38). The facts come
from the tokens, the world and the mask instead:

1. no frame carries `α`: `WF_C` with `[α]_1` held;
2. the record is a record proper, and every cell at `ℓ` carries only `α`: the tag `(p, α)` gives a
   record proper `q` with `FrameLife W q α`; the cell at `q`'s location carries `α`, so it is the
   lender's cell at `ℓ`, whose witness is empty, so `q = p`;
3. no frame holds an `own` or `mut` cell at `ℓ`, at any depth of its flattening: `MaskOff`, the
   condition the relation puts on every frame at a location lent across stops.

So the frame's flattening is undefined at `ℓ` (a cell there would be an `imm` cell carrying only
`α`), which is `ρ_f # ℓ ↦ own(v)` (`hash_own_of_flat_none`), what `uncapture_world` asks.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Kont)
open BoCa.Lifetime (LSub)

/-! ### Singletons -/

/-- The flattening of `ℓ ↦ imm(s, v, ∅)` is itself. -/
theorem flat_single_imm_eq {l : Loc} {s : LSet} {v : Val}
    {h : ResU.InStratum s.join (PMap.empty : WRes)} {τ : WRes}
    (hτ : ResU.Flat (ResU.single l (CellU.immOf s v PMap.empty h)) τ) :
    τ = ResU.single l (CellU.immOf s v PMap.empty h) := by
  obtain ⟨e, a, he, ha, hc'⟩ := hτ
  have he0 : e = PMap.empty := ExS.functional he (ExW.empty_of_all_imm (fun y ψ hy => by
    obtain ⟨-, rfl⟩ := ResU.single_get_eq_some hy; exact CellU.kind_immOf _ _ _ _))
  obtain ⟨ev, av, p, hev, hav, hp, hpa⟩ := AgW.single_imm_inv ha
  obtain rfl : ev = PMap.empty := ExR.functional hev exW_empty
  obtain rfl : av = PMap.empty := AgW.functional hav agW_empty
  obtain rfl : p = PMap.empty := ResU.CompR.functional hp (ResU.comp_empty_right _)
  obtain rfl : a = ResU.single l (CellU.immOf s v PMap.empty h) :=
    ResU.CompR.functional hpa (ResU.comp_empty_right _)
  subst he0
  exact eq_of_compS_empty_left hc'

theorem flat_single_own_eq {l : Loc} {v : Val} {τ : WRes}
    (hτ : ResU.Flat (ResU.single l (CellU.ownOf v)) τ) :
    τ = ResU.single l (CellU.ownOf v) :=
  ResU.Flat.functional hτ (ResU.flat_single_own l v)

theorem maskShallow_single_imm (L : Set Loc) {l : Loc} {s : LSet} {v : Val}
    {h : ResU.InStratum s.join (PMap.empty : WRes)} :
    MaskShallow L (ResU.single l (CellU.immOf s v PMap.empty h)) := by
  intro m _ t u χ hh ⟨τ, hτ, hg⟩
  obtain rfl := flat_single_imm_eq hτ
  by_cases hm : m = l
  · subst hm
    rw [ResU.single_get_self] at hg
    exact (CellU.immOf_inj (Option.some.inj hg)).2.2.symm
  · rw [ResU.single_get_ne _ hm] at hg; cases hg

theorem maskShallow_single_own (L : Set Loc) (l : Loc) (v : Val) :
    MaskShallow L (ResU.single l (CellU.ownOf v)) := by
  intro m _ t u χ hh ⟨τ, hτ, hg⟩
  obtain rfl := flat_single_own_eq hτ
  by_cases hm : m = l
  · subst hm
    rw [ResU.single_get_self] at hg
    exact absurd (Option.some.inj hg) CellU.ownOf_ne_immOf
  · rw [ResU.single_get_ne _ hm] at hg; cases hg

/-! ### Two resources that differ only at `ℓ` -/

/-- **Off `ℓ`, a composite with a singleton at `ℓ` flattens as the rest**: `⦇ρᵢ ● X⦈ = ⦇ρᵢ⦈ ○ ⦇X⦈`
and `⦇ρᵢ⦈` holds nothing off `ℓ`. -/
theorem flatAt_off_swap {ρ₁ ρ₂ X A B : WRes} {l : Loc}
    (h₁ : ∀ τ, ResU.Flat ρ₁ τ → ∀ m, m ≠ l → τ.get m = none)
    (h₂ : ∀ τ, ResU.Flat ρ₂ τ → ∀ m, m ≠ l → τ.get m = none)
    (hA : ResU.CompS ρ₁ X A) (hB : ResU.CompS ρ₂ X B) (hvA : A.Valid) (hvB : B.Valid)
    {m : Loc} (hm : m ≠ l) (ψ : CellU Loc Val) : A.FlatAt m ψ ↔ B.FlatAt m ψ := by
  have key : ∀ {ρ₁ ρ₂ A B : WRes},
      (∀ τ, ResU.Flat ρ₁ τ → ∀ m, m ≠ l → τ.get m = none) →
      (∀ τ, ResU.Flat ρ₂ τ → ∀ m, m ≠ l → τ.get m = none) →
      ResU.CompS ρ₁ X A → ResU.CompS ρ₂ X B → B.Valid → A.FlatAt m ψ → B.FlatAt m ψ := by
    intro ρ₁ ρ₂ A B h₁ h₂ hA hB hvB ⟨σ, hσ, hg⟩
    obtain ⟨σ₁, σX, hσ₁, hσX, hR⟩ := flat_compR hA hσ
    obtain ⟨σB, hσB⟩ := hvB
    obtain ⟨σ₂, σX', hσ₂, hσX', hR'⟩ := flat_compR hB hσB
    obtain rfl := ResU.Flat.functional hσX' hσX
    refine ⟨σB, hσB, ?_⟩
    rw [ResU.Comp.get_of_left_none hR' (h₂ _ hσ₂ m hm), ← hg,
      ResU.Comp.get_of_left_none hR (h₁ _ hσ₁ m hm)]
  exact ⟨key h₁ h₂ hA hB hvB, key h₂ h₁ hB hA hvA⟩

theorem single_imm_off {l : Loc} {s : LSet} {v : Val}
    {h : ResU.InStratum s.join (PMap.empty : WRes)} :
    ∀ τ, ResU.Flat (ResU.single l (CellU.immOf s v PMap.empty h)) τ → ∀ m, m ≠ l →
      τ.get m = none := by
  intro τ hτ m hm
  rw [flat_single_imm_eq hτ, ResU.single_get_ne _ hm]

theorem single_own_off {l : Loc} {v : Val} :
    ∀ τ, ResU.Flat (ResU.single l (CellU.ownOf v)) τ → ∀ m, m ≠ l → τ.get m = none := by
  intro τ hτ m hm
  rw [flat_single_own_eq hτ, ResU.single_get_ne _ hm]

/-- `↭` from a resource that flattens as another outside the mask. -/
theorem UpdVNm.of_flatAt_off {Φ : LocFam} {n : Nat} {L : Set Loc} {A B π : WRes}
    (h : UpdVNm Φ n L B π) (hvA : A.Valid)
    (hAB : ∀ m, m ∉ L → ∀ ψ, A.FlatAt m ψ ↔ B.FlatAt m ψ) : UpdVNm Φ n L A π := by
  refine ⟨⟨fun m hm s v χ hh => (hAB m hm _).trans (h.1.1 m hm s v χ hh),
    fun m hm ψ hψ hk => h.1.2.1 m hm ψ ((hAB m hm ψ).mp hψ) hk,
    fun m hm ψ' hψ hk => ?_⟩, hvA, h.2.2⟩
  obtain ⟨ψ, hψB, hs⟩ := h.1.2.2 m hm ψ' hψ hk
  exact ⟨ψ, (hAB m hm ψ).mpr hψB, hs⟩

/-- The lend masks `ℓ`. -/
theorem Mask.lendLocs_sub (M : Mask) : M.lendLocs ⊆ M.locs := fun _ ⟨_, h⟩ => ⟨_, h⟩

/-! ### `ρ # ℓ ↦ own(v)` from a flattening undefined at `ℓ` -/

/-- **A valid resource whose flattening is undefined at `ℓ` composes with `ℓ ↦ own(v)`.** The
converse direction of `ResU.walks_none_of_hash_own`: `⦇ρ ● ℓ ↦ own(v)⦈ = (ex(ρ)_● ● ℓ ↦ own(v)) ●
ag(ρ)`, defined because neither walk of `ρ` reaches `ℓ`. -/
theorem hash_own_of_flat_none {ρ : WRes} (hv : ρ.Valid) {l : Loc}
    (h : ∀ ψ, ¬ ρ.FlatAt l ψ) (v : Val) : ResU.Hash ρ (ResU.single l (CellU.ownOf v)) := by
  obtain ⟨σ, e, a, he, ha, hc⟩ := hv
  have hσl : σ.get l = none := by
    cases hg : σ.get l with
    | none => rfl
    | some ψ => exact absurd ⟨σ, ⟨e, a, he, ha, hc⟩, hg⟩ (h ψ)
  obtain ⟨hel, hal⟩ := (ResU.Comp.eq_none_iff hc l).mp hσl
  have hρl : ρ.get l = none := by
    cases hg : ρ.get l with
    | none => rfl
    | some ψ =>
        obtain ⟨χ, hχ, -⟩ := ResU.Flat.get ⟨e, a, he, ha, hc⟩ hg
        rw [hσl] at hχ; cases hχ
  have hcomp : ResU.CompatS ρ (ResU.single l (CellU.ownOf v)) := by
    intro m ψ₁ ψ₂ e₁ e₂
    obtain ⟨rfl, -⟩ := ResU.single_get_eq_some e₂
    rw [hρl] at e₁; cases e₁
  obtain ⟨T, hT⟩ := (ResU.compS_defined_iff _ _).mpr hcomp
  have hce : ResU.CompatS e (ResU.single l (CellU.ownOf v)) := by
    intro m ψ₁ ψ₂ e₁ e₂
    obtain ⟨rfl, -⟩ := ResU.single_get_eq_some e₂
    rw [hel] at e₁; cases e₁
  obtain ⟨E, hE⟩ := (ResU.compS_defined_iff _ _).mpr hce
  have hexT : ExS T E := (ExS.split hT).mpr ⟨e, _, he, ExW.single_own l v, hE⟩
  have hagT : AgW T a := (AgW.split hT).mpr ⟨a, _, ha, AgW.single_own l v,
    ResU.comp_empty_right a⟩
  have hEa : ResU.CompatS E a := by
    intro m ψ₁ ψ₂ e₁ e₂
    by_cases hm : m = l
    · subst hm; rw [hal] at e₂; cases e₂
    · have : E.get m = e.get m :=
        ResU.Comp.get_of_right_none hE (ResU.single_get_ne _ hm)
      rw [this] at e₁
      exact hc.1 m ψ₁ ψ₂ e₁ e₂
  obtain ⟨σ', hσ'⟩ := (ResU.compS_defined_iff _ _).mpr hEa
  exact ⟨hcomp, T, hT, σ', E, a, hexT, hagT, hσ'⟩

/-! ### What the end reads of the frame -/

/-- **The frame at a lend's end in a later segment.** At the start of a run holding `[α]_1` and
`S ● ℓ ↦ imm(s, v, ∅)`, with `S` carrying no `α`, in a world where the list tags the lend's record
`p` at `α`: `p` is a record proper, and the frame composes with `ℓ ↦ own(v)`. -/
theorem lendEnd_frame {M : Mask} {l : Loc} (hl : l ∈ M.lendLocs) {v : Val} {T : VTy} {δ : LSub}
    {α : Life} {s : LSet} {hs : ResU.InStratum s.join (PMap.empty : WRes)}
    {ρf S ρres W : WRes} {gf g : GRes} {ps : List FrameRec} {ls : List SRec}
    (hres : ResU.CompS S (ResU.single l (CellU.immOf s v PMap.empty hs)) ρres)
    (hW : ResU.CompS ρf ρres W) (hT : TWNC W ps (rsOf ls)) (htg : Tagged W ps ls)
    (hmem : ((⟨l, v, PMap.empty, T, δ⟩ : FrameRec), α) ∈ ls)
    (hv : (gf + g).Valid) (hα : g.tok α = 1)
    (hwf : WFC (gf + g).counted (ρf, gf)) (hoff : MaskOff M ρf) (hS : ¬ Carries S α) :
    (⟨l, v, PMap.empty, T, δ⟩ : FrameRec) ∈ ps ∧
      ResU.Hash ρf (ResU.single l (CellU.ownOf v)) := by
  set p : FrameRec := ⟨l, v, PMap.empty, T, δ⟩ with hpdef
  have hvW : W.Valid := hT.valid
  have hvρf : ρf.Valid := (ResU.Valid.split hW hvW).1
  -- 1. the frame carries no `α`
  have hfα : ¬ Carries ρf α := by
    intro hc
    have hαC : α ∈ (gf + g).counted := by
      show 0 < gf.tok α + g.tok α
      rw [hα]; exact lt_of_lt_of_le zero_lt_one le_add_self
    have h0 := hwf α hαC hc
    have h1 := hv.tok α
    simp only [GRes.tok_add, hα] at h1
    have : gf.tok α = 0 := by
      have h' : gf.tok α + 1 ≤ 0 + 1 := by simpa using h1
      exact le_antisymm (le_of_add_le_add_right h') (by positivity)
    exact absurd h0 (by rw [this]; exact lt_irrefl 0)
  -- the flattening of the world and its walks
  obtain ⟨σ, eW, aW, heW, haW, hcW⟩ := hvW
  have hfree : eW.ImmFree := ExS.immFree heW
  -- an `imm` cell of `ag(W)` at `m` carrying `α` is the lender's, at `ℓ`, with empty witness
  have atL : ∀ m (t : LSet) (u : Val) (χ : WRes) (hh : χ.InStratum t.join),
      aW.get m = some (CellU.immOf t u χ hh) → t.mem α → m = l ∧ χ = PMap.empty := by
    intro m t u χ hh hg ht
    have hσm : W.FlatAt m (CellU.immOf t u χ hh) :=
      ⟨σ, ⟨eW, aW, heW, haW, hcW⟩, flat_of_ag_imm heW hcW hg⟩
    rcases flatAt_comp_imm_split hW hσm ht with ⟨t₁, h₁, hf₁, hm₁⟩ | ⟨t₂, h₂, hf₂, hm₂⟩
    · exact absurd ⟨m, t₁, u, χ, h₁, hf₁, hm₁⟩ hfα
    · rcases flatAt_comp_imm_split hres hf₂ hm₂ with ⟨t₃, h₃, hf₃, hm₃⟩ | ⟨t₄, h₄, hf₄, -⟩
      · exact absurd ⟨m, t₃, u, χ, h₃, hf₃, hm₃⟩ hS
      · obtain ⟨τ, hτ, hgτ⟩ := hf₄
        rw [flat_single_imm_eq hτ] at hgτ
        by_cases hml : m = l
        · subst hml
          rw [ResU.single_get_self] at hgτ
          exact ⟨rfl, (CellU.immOf_inj (Option.some.inj hgτ)).2.2.symm⟩
        · rw [ResU.single_get_ne _ hml] at hgτ; cases hgτ
  -- 2. the record is a record proper
  obtain ⟨q, hq, hqd, hfq⟩ := htg _ hmem
  obtain ⟨ψ, hψ, hkψ, -, hwψ⟩ := hT.inv.2.1 q hq aW haW
  obtain ⟨t, ht, hψeq⟩ := CellU.imm_eta hkψ
  obtain ⟨y, hy⟩ := LSet.nonempty t
  have hyα : y = α :=
    hfq.1 aW haW ψ t hψ (by rw [hψeq, CellU.lsOf_immOf]) y hy
  rw [hyα] at hy
  rw [hψeq] at hψ
  obtain ⟨hql, hqR⟩ := atL q.le t ψ.erase ψ.wit ht hψ hy
  have hqp : q = p := by
    have : q.R = PMap.empty := hwψ.symm.trans hqR
    exact (descR_empty this hqd).symm
  subst hqp
  refine ⟨hq, hash_own_of_flat_none hvρf (fun φ hφ => ?_) v⟩
  -- 3. a frame cell at `ℓ` is a copy (`MaskOff`), so it carries only `α`, so the frame carries `α`
  have hkφ := hoff l hl φ hφ
  obtain ⟨t', ht', hφeq⟩ := CellU.imm_eta hkφ
  rw [hφeq] at hφ
  obtain ⟨t'', h'', hW'', hsub⟩ := flatAt_comp_imm_left hW ⟨σ, eW, aW, heW, haW, hcW⟩ hφ
  obtain ⟨σ₀, hσ₀, hg₀⟩ := hW''
  obtain rfl := ResU.Flat.functional hσ₀ ⟨eW, aW, heW, haW, hcW⟩
  have hag : aW.get l = some (CellU.immOf t'' φ.erase φ.wit h'') :=
    (flat_imm_iff_ag hfree hcW).mp hg₀
  obtain ⟨z, hz⟩ := LSet.nonempty t'
  have hzα : z = α :=
    hfq.1 aW haW _ t'' (by rw [← hql] at hag; exact hag) (by rw [CellU.lsOf_immOf]) z
      (hsub z hz)
  rw [hzα] at hz
  exact hfα ⟨l, t', φ.erase, φ.wit, ht', hφ, hz⟩

/-! ### `MaskOff` along another task's run -/

/-- **A run not masked at `ℓ` keeps its resource's flattening free of `own` and `mut` cells at
`ℓ`**, in a world whose `ag` holds a cell at `ℓ` (a record proper at `ℓ`, by `LeInv`). A `mut`
cell at the end was at the start (`↭`'s `mut` clause at `ℓ`). An `own` cell at the end is in
`ex(π)_●`, which `ex_ag_disjoint` refutes in the world, or beneath an `imm` cell of `ag(π)`, whose
ancestor is unmasked (`MaskShallow`) and so at the start, where the start's flattening is then
defined at `ℓ`, hence an `imm` cell there, which `↭`'s `imm` clause carries to the end. This is
what a pool reads to keep the frame condition `MaskOff` of the lender's frames. -/
theorem maskOff_of_upd {Φ : LocFam} {n : Nat} {L : Set Loc} {l : Loc} (hlL : l ∉ L)
    {ρ π R W : WRes} (hU : UpdVNm Φ n L ρ π) (hshπ : MaskShallow L π)
    (hoffρ : ∀ ψ, ρ.FlatAt l ψ → ψ.kind = Kind.imm) (hW : ResU.CompS π R W)
    (hag : ∀ a, AgW W a → ∃ ψ, a.get l = some ψ) (hvW : W.Valid) :
    ∀ ψ, π.FlatAt l ψ → ψ.kind = Kind.imm := by
  intro ψ hψ
  cases hk : ψ.kind with
  | imm => rfl
  | «mut» =>
      obtain ⟨ψ₀, hψ₀, hs⟩ := hU.1.2.2 l hlL ψ hψ hk
      have := hoffρ ψ₀ hψ₀
      rw [hs.1] at this; cases this
  | own =>
      exfalso
      obtain ⟨σπ, ⟨eπ, aπ, heπ, haπ, hcπ⟩, hgπ⟩ := hψ
      have hko : ψ.kind ≠ Kind.imm := by rw [hk]; simp
      rcases ResU.Comp.get hcπ l with ⟨-, -, f⟩ | ⟨ζ, f₁, f₂, f⟩ | ⟨ζ, f₁, f₂, f⟩ |
          ⟨ζ₁, ζ₂, ζ, f₁, f₂, f, hC⟩
      · rw [hgπ] at f; cases f
      · -- in `ex(π)_●`: refuted in the world
        rw [hgπ] at f; cases Option.some.inj f
        obtain ⟨σW, eW, aW, heW, haW, hcW⟩ := hvW
        obtain ⟨e₁, e₂, he₁, he₂, hec⟩ := (ExS.split hW).mp heW
        obtain rfl := ExS.functional he₁ heπ
        have heWl : eW.get l = some ψ := (ResU.CompS.get_left_of_ne_imm hec f₁ hko).2
        obtain ⟨φ, hφ⟩ := hag aW haW
        exact ex_ag_disjoint ⟨σW, eW, aW, heW, haW, hcW⟩ heW haW heWl hφ
      · -- beneath an `imm` cell of `ag(π)`: its ancestor is at the start
        rw [hgπ] at f; cases Option.some.inj f
        obtain ⟨σρ, eρ, aρ, heρ, haρ, hcρ⟩ := hU.2.1
        obtain ⟨χ, ev, av, p, z, ξ, -, -, -, hz, hpl, -, -, -⟩ :=
          updImmM_ag_nonimm_transfer (updImmM_symm hU.1.1) hshπ heπ haπ hcπ heρ haρ hcρ f₂ hko
        obtain ⟨ζa, hζa⟩ := comp_some hz hpl
        obtain ⟨ζσ, hζσ⟩ := comp_some_r hcρ hζa
        have hkσ := hoffρ ζσ ⟨σρ, ⟨eρ, aρ, heρ, haρ, hcρ⟩, hζσ⟩
        obtain ⟨t, ht, hζeq⟩ := CellU.imm_eta hkσ
        rw [hζeq] at hζσ
        obtain ⟨σπ', hσπ', hgπ'⟩ := (hU.1.1 l hlL t _ _ ht).mp
          ⟨σρ, ⟨eρ, aρ, heρ, haρ, hcρ⟩, hζσ⟩
        obtain rfl := ResU.Flat.functional hσπ' ⟨eπ, aπ, heπ, haπ, hcπ⟩
        rw [hgπ] at hgπ'
        have := congrArg CellU.kind (Option.some.inj hgπ')
        rw [hk, CellU.kind_immOf] at this
        cases this
      · rw [hgπ] at f; cases Option.some.inj f
        exact hko (CellU.CompS.kind hC)

/-! ### Ghost facts -/

theorem GRes.counted_mono_add (g h : GRes) : g.counted ⊆ (g + h).counted := by
  intro α hα
  show 0 < g.tok α + h.tok α
  exact lt_of_lt_of_le hα le_self_add

/-- An empty escrow has no proper sub-record. -/
theorem not_desc_empty {p d : FrameRec} (hR : p.R = PMap.empty) : ¬ Desc p d := by
  rintro ⟨path, hne, hp⟩
  cases hp with
  | nil => exact hne rfl
  | cons hsub _ =>
      obtain ⟨-, -, ζ, eζ, -⟩ := hsub
      rw [hR, PMap.empty_get] at eζ
      cases eζ

/-! ### Minting a whole token -/

/-- **`[κ]_1` minted at a fresh `κ` at the start of a run**: below the resource and the frame, with
no token anywhere. A ghost change the frame cannot see: it holds no fraction of `κ` and carries
no copy at `κ`. A lender mints the authority of a loan it will hold across stops this way, before
the task that holds the loan is spawned. -/
theorem rwpGX_mint {Φ : LocFam} {M : Mask} {Q : PostGX} {n : Nat} {ls : List SRec} {e : Expr}
    {ρ : WRes} {g : GRes}
    (hbody : ∀ κ : Life, ρ.InStratum κ → g.tok κ = 0 →
      rwpGX (ℍ := ℍ) Φ M Q n ls e (ρ, g + GRes.life κ)) :
    rwpGX (ℍ := ℍ) Φ M Q n ls e (ρ, g) := by
  intro xf sρ ps μ hH3 hsρ hv hwf hwx hsh hau hoff hT htg hlow hfd jr μ' e' hj hrun
  obtain ⟨ar, har⟩ := ρ.exists_atLife
  obtain ⟨af, haf⟩ := xf.1.exists_atLife
  obtain ⟨κ, hlt, htokκ⟩ := GRes.exists_fresh_life (hv := hv) (ar ⊓ af)
  have houtr : ResU.InStratum κ ρ := outlives_of_atLife har (lt_of_lt_of_le hlt inf_le_left)
  have houtf : ResU.InStratum κ xf.1 := outlives_of_atLife haf (lt_of_lt_of_le hlt inf_le_right)
  have htokg : g.tok κ = 0 := by
    have := htokκ; simp only [GRes.tok_add] at this
    exact (add_eq_zero.mp this).2
  have hVin : (xf.2 + (g + GRes.life κ)).Valid := by
    rw [← GRes.add_assoc]; exact GRes.valid_add_life hv htokκ
  have hcin : ∀ α, α ∈ (xf.2 + (g + GRes.life κ)).counted → α ≠ κ →
      α ∈ (xf.2 + g).counted := by
    intro α hα hne
    simp only [GRes.counted, Set.mem_ofPred_eq, GRes.tok_add, GRes.tok_life, if_neg hne,
      _root_.add_zero] at hα ⊢
    exact hα
  have hWf : WFC (xf.2 + (g + GRes.life κ)).counted xf := by
    intro α hα hc
    by_cases hακ : α = κ
    · subst hακ; exact absurd hc (not_carries_of_inStratum houtf)
    · exact hwf α (hcin α hα hακ) hc
  have hWx : WFC (xf.2 + (g + GRes.life κ)).counted (ρ, g + GRes.life κ) := by
    intro α hα hc
    show 0 < g.tok α + (GRes.life κ).tok α
    by_cases hακ : α = κ
    · subst hακ; exact absurd hc (not_carries_of_inStratum houtr)
    · exact lt_of_lt_of_le (hwx α (hcin α hα hακ) hc) le_self_add
  have hr := hbody κ houtr htokg xf sρ ps μ hH3 hsρ hVin hWf hWx hsh
    (hau.add_right (GRes.Valid.right hVin)) hoff hT htg hlow hfd jr μ' e' hj hrun
  refine ⟨hr.1, fun hfin => ?_⟩
  obtain ⟨ρ', ρp, fρ', fρ'p, π, g', gp, ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, hU, hNo, hT', htg',
    hps', hls', hV, hN, hW', hWp, hS', hSπ, hAu, hOff, hq⟩ := hr.2 hfin
  refine ⟨ρ', ρp, fρ', fρ'p, π, g', gp, ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, hU, hNo, hT', htg',
    hps', hls', hV, fun α hα hα₀ => ?_, hW', hWp, hS', hSπ, hAu, hOff, hq⟩
  by_cases hακ : α = κ
  · subst hακ; exact not_carries_of_inStratum houtf
  · exact hN α hα (fun h => hα₀ (hcin α h hακ))

theorem erwpX_mint {Φ : LocFam} {M : Mask} {Tb : TableX} {Q : PostX} {n : Nat}
    {ls : List SRec} {e : Expr} {ρ : WRes} {g : GRes}
    (hbody : ∀ κ : Life, ρ.InStratum κ → g.tok κ = 0 →
      erwpX (ℍ := ℍ) Φ M Tb Q n ls e (ρ, g + GRes.life κ)) :
    erwpX (ℍ := ℍ) Φ M Tb Q n ls e (ρ, g) := by
  rw [erwpX_eq]
  refine rwpGX_mint (fun κ h₁ h₂ => ?_)
  have hb := hbody κ h₁ h₂
  rwa [erwpX_eq] at hb

/-! ### The open -/

/-- **A counted lend opened at the start of a run, at a mask holding it.** `ℓ ↦ own(v)` with an
empty payload is lent at a fresh `α`: the run continues from `ρ_b ● ℓ ↦ imm({α}, v, ∅)` holding
`[α]_1`, at the list with the lend's record tagged `α`, and may stop any number of times with the
lend open. Every end of that run is an end of the run from `ℓ ↦ own(v) ● ρ_b`: the two starts
flatten alike off `ℓ`, which is masked, and differ in the records only at `ℓ`. -/
theorem rwpGX_lendOpen {Φ : LocFam} {M : Mask} {Q : PostGX} {n : Nat} (l : Loc)
    (hl : l ∈ M.lendLocs) (T : VTy) (δ : LSub) (hadm : AdmWf T δ) (v : Val)
    (hshape : vShape T δ v (PMap.empty : WRes)) (e : Expr) (ls : List SRec)
    {ρb ρ : WRes} {g : GRes}
    (hcρ : ResU.CompS (ResU.single l (CellU.ownOf v)) ρb ρ)
    (hbody : ∀ A : Life, ρb.InStratum A → (∀ x ∈ ls, x.2 ⊐ A) → g.tok A = 0 →
      ∀ (h : ResU.InStratum (LSet.singleton A).join (PMap.empty : WRes)) (BI : WRes),
        ResU.CompS ρb (ResU.single l (CellU.immOf (LSet.singleton A) v PMap.empty h)) BI →
        rwpGX (ℍ := ℍ) Φ M Q n (((⟨l, v, PMap.empty, T, δ⟩ : FrameRec), A) :: ls) e
          (BI, g + GRes.life A)) :
    rwpGX (ℍ := ℍ) Φ M Q n ls e (ρ, g) := by
  classical
  intro xf sρ ps μ hH3 hsρ hv hwf hwx hsh hau hoff hT htg hlow hfd jr μ' e' hj hrun
  have hvρ : ResU.Valid ρ := (hash_valid hH3).2
  set ρf : WRes := xf.1 with hρfdef
  -- the fresh lifetime: below `ρ_b`, the frame and every tag, with no token anywhere
  obtain ⟨ab, hab⟩ := ρb.exists_atLife
  obtain ⟨af, haf⟩ := ρf.exists_atLife
  obtain ⟨b₀, hb₀⟩ := exists_fresh ls
  obtain ⟨A, hAlt, htokA⟩ := GRes.exists_fresh_life (hv := hv) (ab ⊓ af ⊓ b₀)
  have hAb : ab ⊐ A := lt_of_lt_of_le hAlt (le_trans inf_le_left inf_le_left)
  have hAf : af ⊐ A := lt_of_lt_of_le hAlt (le_trans inf_le_left inf_le_right)
  have hAtag : ∀ x ∈ ls, x.2 ⊐ A := fun x hx => lt_of_lt_of_le
    (lt_of_lt_of_le hAlt inf_le_right) (le_of_lt (hb₀ x hx))
  have houtb : ResU.InStratum A ρb := outlives_of_atLife hab hAb
  have houtf : ResU.InStratum A ρf := outlives_of_atLife haf hAf
  have htokg : g.tok A = 0 := by
    have := htokA; simp only [GRes.tok_add] at this
    exact (add_eq_zero.mp this).2
  have houtP : ResU.InStratum (LSet.singleton A).join (PMap.empty : WRes) :=
    ResU.inStratum_empty _
  set p : FrameRec := ⟨l, v, PMap.empty, T, δ⟩ with hpdef
  have hds : ∀ d, d ∈ ([] : List FrameRec) ↔ Desc p d :=
    fun d => ⟨fun h => absurd h (by simp), fun h => absurd h (not_desc_empty rfl)⟩
  -- the entry's world (`capture_world`)
  obtain ⟨BI, fρ, hBI, hH17, h4, -, hTin, htgin, hlowin⟩ :=
    capture_world l T δ hadm v (A := A) houtP (ResU.comp_empty_right _) hcρ hshape hds
      (O := []) (psF := ps) hH3 hsρ ⟨fun q => by simp, fun q hq => by simp at hq⟩ hT htg hlow
  have hfl : frameList p [] A ls = (p, A) :: ls := by simp [frameList]
  rw [hfl] at hTin htgin
  have hvBI : ResU.Valid BI := (hash_valid hH17).2
  -- the body's ghost premises: `[α]_1` minted at the fresh `α`
  have hVin : (xf.2 + (g + GRes.life A)).Valid := by
    rw [← GRes.add_assoc]; exact GRes.valid_add_life hv htokA
  have hcin : ∀ α, α ∈ (xf.2 + (g + GRes.life A)).counted → α ≠ A →
      α ∈ (xf.2 + g).counted := by
    intro α hα hne
    simp only [GRes.counted, Set.mem_ofPred_eq, GRes.tok_add, GRes.tok_life, if_neg hne,
      _root_.add_zero] at hα ⊢
    exact hα
  have hWfin : WFC (xf.2 + (g + GRes.life A)).counted (ρf, xf.2) := by
    intro α hα hc
    by_cases hαA : α = A
    · subst hαA; exact absurd hc (not_carries_of_inStratum houtf)
    · exact hwf α (hcin α hα hαA) hc
  have hWxin : WFC (xf.2 + (g + GRes.life A)).counted (BI, g + GRes.life A) := by
    intro α hα hc
    show 0 < g.tok α + (GRes.life A).tok α
    by_cases hαA : α = A
    · subst hαA; simp
    · rcases carries_comp_split hBI hc with hc' | hc'
      · exact lt_of_lt_of_le (hwx α (hcin α hα hαA) (carries_comp_right hcρ hvρ hc'))
          le_self_add
      · exact absurd (carries_single_imm hc') hαA
  have hshBI : MaskShallow M.locs BI :=
    maskShallow_comp hBI (maskShallow_right hcρ hvρ hsh) (maskShallow_single_imm _)
  have hauIn : MaskAuth M (g + GRes.life A) := hau.add_right (GRes.Valid.right hVin)
  have hr := hbody A houtb hAtag htokg houtP BI hBI (ρf, xf.2) fρ (p :: ps) μ hH17 h4 hVin
    hWfin hWxin hshBI hauIn hoff hTin htgin hlowin hfd jr μ' e' hj hrun
  refine ⟨hr.1, fun hfin => ?_⟩
  obtain ⟨ρ', ρp, fρ', fρ'p, π, g', gp, ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, hU, hNo, hT', htg',
    hps', hls', hV, hN, hW', hWp, hS', hSπ, hAu, hOff, hq⟩ := hr.2 hfin
  have hpl : p.le ∈ M.lendLocs := hl
  refine ⟨ρ', ρp, fρ', fρ'p, π, g', gp, ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, ?_, hNo, hT', htg',
    fun q hq => ?_, fun y hy => ?_, hV, ?_, hW', hWp, hS', hSπ, hAu, hOff, hq⟩
  · refine UpdVNm.of_flatAt_off hU hvρ (fun m hm ψ => ?_)
    have hml : m ≠ l := fun h => hm (h ▸ Mask.lendLocs_sub M hl)
    exact flatAt_off_swap single_own_off single_imm_off hcρ (ResU.CompS.comm hBI) hvρ hvBI hml ψ
  · have hqp : q ≠ p := fun h => hq (h ▸ hpl)
    rw [hps' q hq]; simp [hqp]
  · have hyp : y ≠ (p, A) := fun h => hy (h ▸ hpl)
    rw [hls' y hy]; simp [hyp]
  · intro α hα hα₀
    by_cases hαA : α = A
    · subst hαA; exact not_carries_of_inStratum houtf
    · exact hN α hα (fun h => hα₀ (hcin α h hαA))

/-! ### The end -/

/-- **A counted lend ended at the start of a run, at a mask holding it.** Holding `[α]_1` and
`S ● ℓ ↦ imm(s, v, ∅)`, with `S` carrying no `α` and composing with `ℓ ↦ own(v)`, in a list that
tags the lend's record at `α`: the record is ended (`uncapture_world`, with the frame's half from
`lendEnd_frame`), `[α]_1` is consumed, and the run continues from `S ● ℓ ↦ own(v)` at the list
without the record. Every end of that run is an end of the run from the lent resource. -/
theorem rwpGX_lendEnd {Φ : LocFam} {M : Mask} {Q : PostGX} {n : Nat} {l : Loc}
    (hl : l ∈ M.lendLocs) {v : Val} {T : VTy} {δ : LSub} {α : Life} {s : LSet}
    {hs : ResU.InStratum s.join (PMap.empty : WRes)} (e : Expr) {ls ls' : List SRec}
    (hmem : ((⟨l, v, PMap.empty, T, δ⟩ : FrameRec), α) ∈ ls)
    (hls' : ∀ x, x ∈ ls' ↔ x ∈ ls ∧ x.1 ≠ ⟨l, v, PMap.empty, T, δ⟩)
    {S ρ : WRes} {g : GRes}
    (hres : ResU.CompS S (ResU.single l (CellU.immOf s v PMap.empty hs)) ρ)
    (hS : ¬ Carries S α) (hSo : ResU.Hash S (ResU.single l (CellU.ownOf v)))
    (hau₀ : MaskAuth M g)
    (hbody : ∀ ρo, ResU.CompS S (ResU.single l (CellU.ownOf v)) ρo →
      rwpGX (ℍ := ℍ) Φ M Q n ls' e (ρo, g)) :
    rwpGX (ℍ := ℍ) Φ M Q n ls e (ρ, g + GRes.life α) := by
  classical
  intro xf sρ ps μ hH3 hsρ hv hwf hwx hsh hau hoff hT htg hlow hfd jr μ' e' hj hrun
  have hvρ : ResU.Valid ρ := (hash_valid hH3).2
  set p : FrameRec := ⟨l, v, PMap.empty, T, δ⟩ with hpdef
  -- `[α]_1` is the resource's whole token
  have hgα : g.tok α = 0 := by
    have h1 := (GRes.Valid.right hv).tok α
    simp only [GRes.tok_add, GRes.tok_life] at h1
    have h' : g.tok α + 1 ≤ 0 + 1 := by simpa using h1
    exact le_antisymm (le_of_add_le_add_right h') (by positivity)
  have hα1 : (g + GRes.life α).tok α = 1 := by simp [hgα]
  obtain ⟨hp, hfo⟩ := lendEnd_frame hl hres hsρ hT htg hmem hv hα1 hwf hoff hS
  obtain ⟨ρo, W', ps', hρo, hHf, hW', hps', hTW', htgW', hlowW'⟩ :=
    uncapture_world hp hres hsρ hT htg hlow hfo hSo ls' hls'
  have hvρo : ResU.Valid ρo := (hash_valid hHf).2
  have hGa : xf.2 + (g + GRes.life α) = xf.2 + g + GRes.life α := (GRes.add_assoc _ _ _).symm
  have hV0 : (xf.2 + g).Valid := by rw [hGa] at hv; exact hv.left
  have hsub : (xf.2 + g).counted ⊆ (xf.2 + (g + GRes.life α)).counted := by
    rw [hGa]; exact GRes.counted_mono_add _ _
  have hwx0 : WFC (xf.2 + g).counted (ρo, g) := by
    intro β hβ hc
    rcases carries_comp_split hρo hc with hc' | hc'
    · have hβα : β ≠ α := fun h => hS (h ▸ hc')
      have := hwx β (hsub hβ) (carries_comp_left hres hvρ hc')
      simpa [GRes.tok_life, hβα] using this
    · exact absurd hc' (not_carries_single_own l v β)
  have hsh0 : MaskShallow M.locs ρo :=
    maskShallow_comp hρo (maskShallow_left hres hvρ hsh) (maskShallow_single_own _ _ _)
  have hr := hbody ρo hρo xf W' ps' μ hHf hW' hV0 (hwf.mono hsub) hwx0 hsh0 hau₀ hoff hTW'
    htgW' hlowW' hfd jr μ' e' hj hrun
  refine ⟨hr.1, fun hfin => ?_⟩
  obtain ⟨ρ', ρp, fρ', fρ'p, π, g', gp, ps'', ls'', h₁, h₂, h₃, h₄, h₅, h₆, hU, hNo, hT', htg',
    hps'', hls'', hV, hN, hW'', hWp, hS', hSπ, hAu, hOff, hq⟩ := hr.2 hfin
  have hpl : p.le ∈ M.lendLocs := hl
  refine ⟨ρ', ρp, fρ', fρ'p, π, g', gp, ps'', ls'', h₁, h₂, h₃, h₄, h₅, h₆, ?_, hNo, hT', htg',
    fun q hq => ?_, fun y hy => ?_, hV, fun β hβ hβ₀ => hN β hβ (fun h => hβ₀ (hsub h)), hW'',
    hWp, hS', hSπ, hAu, hOff, hq⟩
  · refine UpdVNm.of_flatAt_off hU hvρ (fun m hm ψ => ?_)
    have hml : m ≠ l := fun h => hm (h ▸ Mask.lendLocs_sub M hl)
    exact flatAt_off_swap single_imm_off single_own_off (ResU.CompS.comm hres)
      (ResU.CompS.comm hρo) hvρ hvρo hml ψ
  · have hqp : q ≠ p := fun h => hq (h ▸ hpl)
    rw [hps'' q hq, hps' q]; exact ⟨fun h => h.1, fun h => ⟨h, hqp⟩⟩
  · have hyp : y.1 ≠ p := fun h => hy (h ▸ hpl)
    rw [hls'' y hy, hls' y]; exact ⟨fun h => h.1, fun h => ⟨h, hyp⟩⟩

/-! ### At `erwpX` -/

/-- **`rwpGX_lendOpen` at `erwpX`**: the lend opened, then held across every stop of the run and
of its continuations, which are the same `erwpX` at the same mask. -/
theorem erwpX_lendOpen {Φ : LocFam} {M : Mask} {Tb : TableX} {Q : PostX} {n : Nat} (l : Loc)
    (hl : l ∈ M.lendLocs) (T : VTy) (δ : LSub) (hadm : AdmWf T δ) (v : Val)
    (hshape : vShape T δ v (PMap.empty : WRes)) (e : Expr) (ls : List SRec)
    {ρb ρ : WRes} {g : GRes}
    (hcρ : ResU.CompS (ResU.single l (CellU.ownOf v)) ρb ρ)
    (hbody : ∀ A : Life, ρb.InStratum A → (∀ x ∈ ls, x.2 ⊐ A) → g.tok A = 0 →
      ∀ (h : ResU.InStratum (LSet.singleton A).join (PMap.empty : WRes)) (BI : WRes),
        ResU.CompS ρb (ResU.single l (CellU.immOf (LSet.singleton A) v PMap.empty h)) BI →
        erwpX (ℍ := ℍ) Φ M Tb Q n (((⟨l, v, PMap.empty, T, δ⟩ : FrameRec), A) :: ls) e
          (BI, g + GRes.life A)) :
    erwpX (ℍ := ℍ) Φ M Tb Q n ls e (ρ, g) := by
  rw [erwpX_eq]
  refine rwpGX_lendOpen l hl T δ hadm v hshape e ls hcρ (fun A h₁ h₂ h₃ h BI hBI => ?_)
  have hb := hbody A h₁ h₂ h₃ h BI hBI
  rwa [erwpX_eq] at hb

/-- **`rwpGX_lendEnd` at `erwpX`**: the lend ended at the start of any segment holding `[α]_1`. -/
theorem erwpX_lendEnd {Φ : LocFam} {M : Mask} {Tb : TableX} {Q : PostX} {n : Nat} {l : Loc}
    (hl : l ∈ M.lendLocs) {v : Val} {T : VTy} {δ : LSub} {α : Life} {s : LSet}
    {hs : ResU.InStratum s.join (PMap.empty : WRes)} (e : Expr) {ls ls' : List SRec}
    (hmem : ((⟨l, v, PMap.empty, T, δ⟩ : FrameRec), α) ∈ ls)
    (hls' : ∀ x, x ∈ ls' ↔ x ∈ ls ∧ x.1 ≠ ⟨l, v, PMap.empty, T, δ⟩)
    {S ρ : WRes} {g : GRes}
    (hres : ResU.CompS S (ResU.single l (CellU.immOf s v PMap.empty hs)) ρ)
    (hS : ¬ Carries S α) (hSo : ResU.Hash S (ResU.single l (CellU.ownOf v)))
    (hau₀ : MaskAuth M g)
    (hbody : ∀ ρo, ResU.CompS S (ResU.single l (CellU.ownOf v)) ρo →
      erwpX (ℍ := ℍ) Φ M Tb Q n ls' e (ρo, g)) :
    erwpX (ℍ := ℍ) Φ M Tb Q n ls e (ρ, g + GRes.life α) := by
  rw [erwpX_eq]
  refine rwpGX_lendEnd hl e hmem hls' hres hS hSo hau₀ (fun ρo hρo => ?_)
  have hb := hbody ρo hρo
  rwa [erwpX_eq] at hb

/-! ### The `mut` loan: the cell moves, the lender keeps the loan's authority

A `mut` loan of `ℓ` is masked at `Auth.mloan κ`, held by the lender's `[κ]_1`. Its open folds `ℓ ↦ own(v)` into the borrow cell
`ℓ ↦ mut(β, v, ∅, P̂)` (`TWNC.mutFold`), which the run may hand to another task at a stop; its end
unfolds the cell, given back, into `ℓ ↦ own(w)` (`TWNC.mutUnfold`). No record is made. The frame's
half of the end needs no world argument: a frame composing with the borrow cell composes with
`ℓ ↦ own(w)` (`[TR]` 6.24). -/

theorem flat_single_mut_eq {l : Loc} {β : Life} {v : Val}
    {hstr : ResU.InStratum β (PMap.empty : WRes)} {P : Val → SPropS Loc Val β}
    {hw : P v ⟨PMap.empty, hstr⟩} {τ : WRes}
    (hτ : ResU.Flat (ResU.single l (CellU.mutOf β v PMap.empty hstr P hw)) τ) :
    τ = ResU.single l (CellU.mutOf β v PMap.empty hstr P hw) := by
  obtain ⟨e, a, he, ha, hc⟩ := hτ
  obtain ⟨e₀, he₀, hce⟩ := ExW.single_mut_inv he
  obtain rfl : e₀ = PMap.empty := ExS.functional he₀ exW_empty
  obtain rfl : ResU.single l (CellU.mutOf β v PMap.empty hstr P hw) = e :=
    ResU.eq_of_comp_empty_right hce
  obtain rfl : a = PMap.empty := AgW.functional (AgW.single_mut_inv ha) agW_empty
  exact (ResU.eq_of_comp_empty_right hc).symm

theorem single_mut_off {l : Loc} {β : Life} {v : Val}
    {hstr : ResU.InStratum β (PMap.empty : WRes)} {P : Val → SPropS Loc Val β}
    {hw : P v ⟨PMap.empty, hstr⟩} :
    ∀ τ, ResU.Flat (ResU.single l (CellU.mutOf β v PMap.empty hstr P hw)) τ → ∀ m, m ≠ l →
      τ.get m = none := by
  intro τ hτ m hm
  rw [flat_single_mut_eq hτ, ResU.single_get_ne _ hm]

theorem maskShallow_single_mut (L : Set Loc) {l : Loc} {β : Life} {v : Val}
    {hstr : ResU.InStratum β (PMap.empty : WRes)} {P : Val → SPropS Loc Val β}
    {hw : P v ⟨PMap.empty, hstr⟩} :
    MaskShallow L (ResU.single l (CellU.mutOf β v PMap.empty hstr P hw)) := by
  intro m _ t u χ hh ⟨τ, hτ, hg⟩
  obtain rfl := flat_single_mut_eq hτ
  by_cases hm : m = l
  · subst hm
    rw [ResU.single_get_self] at hg
    exact absurd (Option.some.inj hg) (Ne.symm CellU.immOf_ne_mutOf)
  · rw [ResU.single_get_ne _ hm] at hg; cases hg

theorem not_carries_single_mut {l : Loc} {β : Life} {v : Val}
    {hstr : ResU.InStratum β (PMap.empty : WRes)} {P : Val → SPropS Loc Val β}
    {hw : P v ⟨PMap.empty, hstr⟩} (α : Life) :
    ¬ Carries (ResU.single l (CellU.mutOf β v PMap.empty hstr P hw)) α := by
  rintro ⟨m, t, u, χ, hh, ⟨τ, hτ, hg⟩, -⟩
  obtain rfl := flat_single_mut_eq hτ
  by_cases hm : m = l
  · subst hm
    rw [ResU.single_get_self] at hg
    exact CellU.immOf_ne_mutOf (Option.some.inj hg).symm
  · rw [ResU.single_get_ne _ hm] at hg; cases hg

theorem Mask.locs_of_mem {M : Mask} {l : Loc} {a : Auth} (h : (l, a) ∈ M) : l ∈ M.locs :=
  ⟨a, h⟩

/-- **A `mut` loan opened at the start of a run, at a mask holding its authority.** -/
theorem rwpGX_mutLoanOpen {Φ : LocFam} {M : Mask} {Q : PostGX} {n : Nat} {l : Loc}
    {κ : Life} (hl : (l, Auth.mloan κ) ∈ M) {β : Life} {v : Val} {hstr : ResU.InStratum β (PMap.empty : WRes)}
    {P : Val → SPropS Loc Val β} (hw : P v ⟨PMap.empty, hstr⟩) (e : Expr) (ls : List SRec)
    {ρa ρ : WRes} {g : GRes}
    (hcρ : ResU.CompS (ResU.single l (CellU.ownOf v)) ρa ρ)
    (hbody : ∀ ρm, ResU.CompS (ResU.single l (CellU.mutOf β v PMap.empty hstr P hw)) ρa ρm →
      rwpGX (ℍ := ℍ) Φ M Q n ls e (ρm, g)) :
    rwpGX (ℍ := ℍ) Φ M Q n ls e (ρ, g) := by
  classical
  intro xf sρ ps μ hH2 hsρ hv hwf hwx hsh hau hoff hT htg hlow hfd jr μ' e' hj hrun
  set ρf : WRes := xf.1 with hρfdef
  set mc : WRes := ResU.single l (CellU.mutOf β v PMap.empty hstr P hw) with hmcdef
  set W : WRes := ResU.single l (CellU.ownOf v) with hWdef
  have hW : ResU.CompS (PMap.empty : WRes) W W := compS_empty_left _
  have hvW : ResU.Valid W := ResU.valid_single_own l v
  have hvm : ResU.Valid mc := ResU.valid_single_mut_of_wit hW hvW
  have hvsρ : ResU.Valid sρ := hash_valid_comp hH2 hsρ
  have hvρ : ResU.Valid ρ := (ResU.Valid.split hsρ hvsρ).2
  -- `sρ = (ρ_f ● ρ_a) ● ℓ ↦ own(v)`
  obtain ⟨Z, hZ, hZo⟩ := (ResU.CompS.assoc ρf ρa W sρ).mp ⟨ρ, ResU.CompS.comm hcρ, hsρ⟩
  have hZW : ResU.Hash Z W := ⟨hZo.1, sρ, hZo, hvsρ⟩
  have hZm : ResU.Hash Z mc := (ResU.six24 hW).mpr hZW
  obtain ⟨W', hW'c, hvW'⟩ := hZm.2
  -- the borrow cell beside `ρ_a`
  obtain ⟨ρm, hρm, hfm⟩ := (ResU.CompS.assoc ρf ρa mc W').mpr ⟨Z, hZ, hW'c⟩
  have hvρm : ResU.Valid ρm := (ResU.Valid.split hfm hvW').2
  have hHf : ResU.Hash ρf ρm := ⟨hfm.1, W', hfm, hvW'⟩
  have hX : ResU.CompS (ResU.single l (CellU.ownOf v)) (PMap.empty : WRes) W :=
    ResU.comp_empty_right _
  have hTin : TWNC W' ps (rsOf ls) :=
    TWNC.mutFold hT hX (ResU.CompS.comm hZo) (ResU.CompS.comm hW'c) hvW'
  have htgin : Tagged W' ps ls := tagged_of_ag (fun a ha =>
    (mut_fold_ag hX (ResU.CompS.comm hZo) (ResU.CompS.comm hW'c) a).mpr ha) htg
  have hlowin : ResU.Lower W' μ :=
    (ResU.lower_swap_mut_own hW hvm hvW hW'c hZm hZo hZW).mpr hlow
  have hwxm : WFC (xf.2 + g).counted (ρm, g) := by
    intro α hα hc
    rcases carries_comp_split hρm hc with h | h
    · exact hwx α hα (carries_comp_right hcρ hvρ h)
    · exact absurd h (not_carries_single_mut α)
  have hshm : MaskShallow M.locs ρm :=
    maskShallow_comp hρm (maskShallow_right hcρ hvρ hsh) (maskShallow_single_mut _)
  have hr := hbody ρm (ResU.CompS.comm hρm) xf W' ps μ hHf hfm hv hwf hwxm hshm hau hoff hTin
    htgin hlowin hfd jr μ' e' hj hrun
  refine ⟨hr.1, fun hfin => ?_⟩
  obtain ⟨ρ', ρp, fρ', fρ'p, π, g', gp, ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, hU, hNo, hT', htg',
    hps', hls', hV, hN, hW'', hWp, hS', hSπ, hAu, hOff, hq⟩ := hr.2 hfin
  refine ⟨ρ', ρp, fρ', fρ'p, π, g', gp, ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, ?_, hNo, hT', htg',
    hps', hls', hV, hN, hW'', hWp, hS', hSπ, hAu, hOff, hq⟩
  refine UpdVNm.of_flatAt_off hU hvρ (fun m hm ψ => ?_)
  have hml : m ≠ l := fun h => hm (h ▸ Mask.locs_of_mem hl)
  exact flatAt_off_swap single_own_off single_mut_off hcρ (ResU.CompS.comm hρm) hvρ hvρm hml ψ

/-- **A `mut` loan ended at the start of a run, at a mask holding its authority**: the borrow cell,
given back, unfolds into `ℓ ↦ own(v)`. -/
theorem rwpGX_mutLoanEnd {Φ : LocFam} {M : Mask} {Q : PostGX} {n : Nat} {l : Loc}
    {κ : Life} (hl : (l, Auth.mloan κ) ∈ M) {β : Life} {v : Val} {hstr : ResU.InStratum β (PMap.empty : WRes)}
    {P : Val → SPropS Loc Val β} {hw : P v ⟨PMap.empty, hstr⟩} (e : Expr) (ls : List SRec)
    {ρa ρ : WRes} {g : GRes}
    (hcρ : ResU.CompS (ResU.single l (CellU.mutOf β v PMap.empty hstr P hw)) ρa ρ)
    (hbody : ∀ ρo, ResU.CompS (ResU.single l (CellU.ownOf v)) ρa ρo →
      rwpGX (ℍ := ℍ) Φ M Q n ls e (ρo, g)) :
    rwpGX (ℍ := ℍ) Φ M Q n ls e (ρ, g) := by
  classical
  intro xf sρ ps μ hH2 hsρ hv hwf hwx hsh hau hoff hT htg hlow hfd jr μ' e' hj hrun
  set ρf : WRes := xf.1 with hρfdef
  set mc : WRes := ResU.single l (CellU.mutOf β v PMap.empty hstr P hw) with hmcdef
  set W : WRes := ResU.single l (CellU.ownOf v) with hWdef
  have hW : ResU.CompS (PMap.empty : WRes) W W := compS_empty_left _
  have hvW : ResU.Valid W := ResU.valid_single_own l v
  have hvm : ResU.Valid mc := ResU.valid_single_mut_of_wit hW hvW
  have hvsρ : ResU.Valid sρ := hash_valid_comp hH2 hsρ
  have hvρ : ResU.Valid ρ := (ResU.Valid.split hsρ hvsρ).2
  -- `sρ = (ρ_f ● ρ_a) ● ℓ ↦ mut(β, v, ∅, P̂)`
  obtain ⟨Z, hZ, hZm⟩ := (ResU.CompS.assoc ρf ρa mc sρ).mp ⟨ρ, ResU.CompS.comm hcρ, hsρ⟩
  have hZmH : ResU.Hash Z mc := ⟨hZm.1, sρ, hZm, hvsρ⟩
  have hZW : ResU.Hash Z W := (ResU.six24 hW).mp hZmH
  obtain ⟨W', hW'c, hvW'⟩ := hZW.2
  obtain ⟨ρo, hρo, hfo⟩ := (ResU.CompS.assoc ρf ρa W W').mpr ⟨Z, hZ, hW'c⟩
  have hvρo : ResU.Valid ρo := (ResU.Valid.split hfo hvW').2
  have hHf : ResU.Hash ρf ρo := ⟨hfo.1, W', hfo, hvW'⟩
  have hX : ResU.CompS (ResU.single l (CellU.ownOf v)) (PMap.empty : WRes) W :=
    ResU.comp_empty_right _
  have hTin : TWNC W' ps (rsOf ls) :=
    TWNC.mutUnfold hT (ResU.CompS.comm hZm) hX (ResU.CompS.comm hW'c) hvW'
  have htgin : Tagged W' ps ls := tagged_of_ag (fun a ha =>
    (mut_fold_ag hX (ResU.CompS.comm hW'c) (ResU.CompS.comm hZm) a).mp ha) htg
  have hlowin : ResU.Lower W' μ :=
    (ResU.lower_swap_mut_own hW hvm hvW hZm hZmH hW'c hZW).mp hlow
  have hwxo : WFC (xf.2 + g).counted (ρo, g) := by
    intro α hα hc
    rcases carries_comp_split hρo hc with h | h
    · exact hwx α hα (carries_comp_right hcρ hvρ h)
    · exact absurd h (not_carries_single_own l v α)
  have hsho : MaskShallow M.locs ρo :=
    maskShallow_comp hρo (maskShallow_right hcρ hvρ hsh) (maskShallow_single_own _ _ _)
  have hr := hbody ρo (ResU.CompS.comm hρo) xf W' ps μ hHf hfo hv hwf hwxo hsho hau hoff hTin
    htgin hlowin hfd jr μ' e' hj hrun
  refine ⟨hr.1, fun hfin => ?_⟩
  obtain ⟨ρ', ρp, fρ', fρ'p, π, g', gp, ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, hU, hNo, hT', htg',
    hps', hls', hV, hN, hW'', hWp, hS', hSπ, hAu, hOff, hq⟩ := hr.2 hfin
  refine ⟨ρ', ρp, fρ', fρ'p, π, g', gp, ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, ?_, hNo, hT', htg',
    hps', hls', hV, hN, hW'', hWp, hS', hSπ, hAu, hOff, hq⟩
  refine UpdVNm.of_flatAt_off hU hvρ (fun m hm ψ => ?_)
  have hml : m ≠ l := fun h => hm (h ▸ Mask.locs_of_mem hl)
  exact flatAt_off_swap single_mut_off single_own_off hcρ (ResU.CompS.comm hρo) hvρ hvρo hml ψ

theorem erwpX_mutLoanOpen {Φ : LocFam} {M : Mask} {Tb : TableX} {Q : PostX} {n : Nat}
    {l : Loc} {κ : Life} (hl : (l, Auth.mloan κ) ∈ M) {β : Life} {v : Val}
    {hstr : ResU.InStratum β (PMap.empty : WRes)} {P : Val → SPropS Loc Val β}
    (hw : P v ⟨PMap.empty, hstr⟩) (e : Expr) (ls : List SRec) {ρa ρ : WRes} {g : GRes}
    (hcρ : ResU.CompS (ResU.single l (CellU.ownOf v)) ρa ρ)
    (hbody : ∀ ρm, ResU.CompS (ResU.single l (CellU.mutOf β v PMap.empty hstr P hw)) ρa ρm →
      erwpX (ℍ := ℍ) Φ M Tb Q n ls e (ρm, g)) :
    erwpX (ℍ := ℍ) Φ M Tb Q n ls e (ρ, g) := by
  rw [erwpX_eq]
  refine rwpGX_mutLoanOpen hl hw e ls hcρ (fun ρm hρm => ?_)
  have hb := hbody ρm hρm
  rwa [erwpX_eq] at hb

theorem erwpX_mutLoanEnd {Φ : LocFam} {M : Mask} {Tb : TableX} {Q : PostX} {n : Nat}
    {l : Loc} {κ : Life} (hl : (l, Auth.mloan κ) ∈ M) {β : Life} {v : Val}
    {hstr : ResU.InStratum β (PMap.empty : WRes)} {P : Val → SPropS Loc Val β}
    {hw : P v ⟨PMap.empty, hstr⟩} (e : Expr) (ls : List SRec) {ρa ρ : WRes} {g : GRes}
    (hcρ : ResU.CompS (ResU.single l (CellU.mutOf β v PMap.empty hstr P hw)) ρa ρ)
    (hbody : ∀ ρo, ResU.CompS (ResU.single l (CellU.ownOf v)) ρa ρo →
      erwpX (ℍ := ℍ) Φ M Tb Q n ls e (ρo, g)) :
    erwpX (ℍ := ℍ) Φ M Tb Q n ls e (ρ, g) := by
  rw [erwpX_eq]
  refine rwpGX_mutLoanEnd hl e ls hcρ (fun ρo hρo => ?_)
  have hb := hbody ρo hρo
  rwa [erwpX_eq] at hb

end BoCa.Fig16.LogRel.Core.Chain.SI

end
