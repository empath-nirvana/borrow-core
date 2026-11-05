import Core.TreeConsume

/-!
# The two roots of #791: a garbage part, and a growth-only store typing  `[spec §62]`

`docs/new-core/scope-791.md` traces its stopped statements to two departures from Core's chain
world. This file decides each in Lean.

**Q1, a garbage part (D4).** Core's `wpTS` ends at `ρ′` and garbage `ρ⁺` with `NoOwn ρ⁺`
(`Core/World.lean`); its world is `ρ_f ● ρ′ ● ρ⁺` and `↭` reads `ρ ↭ ρ′ ● ρ⁺`. The tree's `EndT`
already reads `↭` and the world at the run's whole end resource, so Core's end is `EndT` at a
postcondition that reads only the part without the garbage (`TPost.garb`). `twpG` is `twp` at that
postcondition, closed under garbage beside the start: the garbage stays with the run (it is part
of the run's resource for the continuation, `twpG_bind`), so no frame condition ever reads it.
Core's garbage rules hold by definition: `twpG_bind`, `twpG_forget` (6.148/6.149's shared
argument, `wpTS_frame_noOwn`) and `twpG_garbage` (`wpG_garbage`).
* `twpG_refuses_lendEnd_live_copy`: a lend still does not end while the frame holds a copy.
* `mfPostG_of_mut_false`, `mfPostG_none_false`, `twpG_admits_borrow_in_garbage`: Core's `MFPost`
  (the result in `Res_α`, the borrow handed back) is never met by an end that keeps the borrow,
  is not met at `False` by an end without it, and is met by the borrowed run `val ()` with the
  borrow left as garbage.
* `twpG_admits_drop_last_copy` and `twpG_ends_record_live`: the semantic change. The last copy of
  a view may be left as garbage, so a run may end holding nothing while it still owns a lend
  record whose location is allocated. `twp` refuses both (`twp_refuses_last_copy`,
  `not_twp_ends_record_live`).

**Q2, a growth-only store typing.** `TWd.GrowExt`: the tree kept, and every typed location kept
at its code. It excludes the extension `not_cerwpTMFrame` and `antiInnerVal_retypes` start from
(`not_growExt_wU_wE`). It does not survive location reuse: a start world that types a location
the memory misses is a growth extension of the empty world (`growExt_wE_wU`, `winv_wU_empty`,
`recInv_wU_empty`), `alloc` may return that location (`alloc_returns_one`), and no growth
extension types it at another code (`not_allocThenTypeG`). The tree's `TWd.Ext` admits the
re-typing Core's Mut Frame makes for its borrowed run (`ext_retypes_unheld`).

**Q2, narrowed.** `TWd.PinExt` pins every location the carried resource holds a cell at, `own`
included, and still re-types a location nothing holds (`pinExt_retypes_unheld`). It excludes the
same extension (`not_pinExt_wU_wE`), and a held `own` location keeps its code
(`pinExt_keeps_held`, `not_ownThenTypeP`), so a Mut Frame reads a code fixed before the location
was held.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.Tree.Wp
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Kont)

/-! ## Q1. A garbage part -/

/-- `NoOwn` at the tree carrier: no `own` cell at the top. -/
def NoOwnT {K : WCactus} (ρ : TRes K) : Prop := ∀ l ψ, ρ.get l = some ψ → ψ.kind ≠ Kind.own

theorem noOwnT_empty {K : WCactus} : NoOwnT (PMap.empty : TRes K) := fun _ _ e => by simp at e

theorem NoOwnT.compS {K : WCactus} {a b c : TRes K} (h : ResUT.CompS a b c) (ha : NoOwnT a)
    (hb : NoOwnT b) : NoOwnT c := by
  intro l ψ e
  rcases ResUT.Comp.get h l with ⟨-, -, f⟩ | ⟨χ, f₁, -, f⟩ | ⟨χ, -, f₂, f⟩ |
      ⟨χ₁, χ₂, χ, -, -, f, hC⟩
  · rw [f] at e; cases e
  · rw [f] at e; cases e; exact ha l _ f₁
  · rw [f] at e; cases e; exact hb l _ f₂
  · rw [f] at e; cases e
    obtain ⟨s₁, s₂, v, ρ, h₁, h₂, h₃, -, -, rfl⟩ := hC
    simp

theorem NoOwnT.rr {Θ : LocTy} {K K' : WCactus} {ρ : TRes K} {ρ' : TRes K'} (h : RR Θ ρ ρ')
    (hn : NoOwnT ρ) : NoOwnT ρ' := by
  intro l ψ' e
  obtain ⟨ψ, e₀, hr⟩ := h.get_some' e
  rw [hr.kind]
  exact hn l ψ e₀

theorem noOwnT_single {K : WCactus} {l : BoCa.Loc} {ψ : TCell K} (hk : ψ.kind ≠ Kind.own) :
    NoOwnT (ResUT.single l ψ) := by
  classical
  intro m φ e
  by_cases hm : m = l
  · subst hm; rw [ResUT.single_get_self] at e; cases e; exact hk
  · rw [ResUT.single_get_ne _ hm] at e; cases e

/-- **A postcondition read at the end without its garbage**: the end resource is `ρ₁ ● ρ⁺`,
`NoOwn ρ⁺`, and `Q` reads `ρ₁`. With `EndT` this is Core's post-configuration: `EndT` reads the
world and `↭` at the whole end resource, which is Core's `ρ′ ● ρ⁺`. -/
def TPost.garb (Q : TPost) : TPost := fun k w ls O t ρ' =>
  ∃ ρ₁ g : TRes w.K, ResUT.CompS ρ₁ g ρ' ∧ NoOwnT g ∧ Q k w ls O t ρ₁

/-- **`twp` with a garbage part**: from every start that adds garbage beside `ρ`, a run whose end
is read without its garbage. The garbage is the run's: a frame condition never reads it. -/
def twpG (F : TFrame) (Q : TPost) (n : Nat) (w : TWd) (ls : List (SRecT w.K))
    (O : List (FrameRecT w.K)) (e : Expr) (ρ : TRes w.K) : Prop :=
  ∀ g ρg : TRes w.K, NoOwnT g → ResUT.CompS ρ g ρg → twp (ℍ := ℍ) F Q.garb n w ls O e ρg

/-- **Bind with garbage**, at the premise of `twp_bind`: the first run's garbage is handed to the
continuation as garbage beside its start, not to its frame. -/
theorem twpG_bind {F : TFrame} (hFm : F.Mono) {Q : TPost} (K : Kont) {n : Nat} {w : TWd}
    {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)} {e : Expr} {ρ : TRes w.K}
    (hw : twpG (ℍ := ℍ) F (fun k w' ls' O' t => twpG (ℍ := ℍ) F Q k w' ls' O' (K.plug t)) n w
      ls O e ρ) :
    twpG (ℍ := ℍ) F Q n w ls O (K.plug e) ρ := by
  intro g ρg hg hc
  refine twp_bind hFm K (twp_mono (fun k w' ls' O' t ρ' h => ?_) (hw g ρg hg hc))
  obtain ⟨ρ₁, g', hc', hg', hK⟩ := h
  exact hK g' ρ' hg' hc'

/-- **A part with no `own` cell passes through a run** (`wpTS_frame_noOwn`, 6.148/6.149's shared
argument): it joins the garbage. -/
theorem twpG_forget {F : TFrame} {Q : TPost} {n : Nat} {w : TWd} {ls : List (SRecT w.K)}
    {O : List (FrameRecT w.K)} {e : Expr} {ρ g ρ' : TRes w.K} (hg : NoOwnT g)
    (hc : ResUT.CompS ρ g ρ') (h : twpG (ℍ := ℍ) F Q n w ls O e ρ) :
    twpG (ℍ := ℍ) F Q n w ls O e ρ' := by
  intro g₂ ρg hg₂ hc₂
  obtain ⟨x, hx, hρx⟩ := (ResUT.CompS.assoc ρ g g₂ ρg).mpr ⟨ρ', hc, hc₂⟩
  exact h x ρg (hg.compS hx hg₂) hρx

/-- **Garbage at the end of a run** (`wpG_garbage`). -/
theorem twpG_garbage {F : TFrame} {Q : TPost} {n : Nat} {w : TWd} {ls : List (SRecT w.K)}
    {O : List (FrameRecT w.K)} {e : Expr} {ρ : TRes w.K}
    (h : twpG (ℍ := ℍ) F Q.garb n w ls O e ρ) : twpG (ℍ := ℍ) F Q n w ls O e ρ := by
  intro g ρg hg hc
  refine twp_mono (fun k w' ls' O' t ρ' hq => ?_) (h g ρg hg hc)
  obtain ⟨ρ₁, g₁, hc₁, hg₁, ρ₂, g₂, hc₂, hg₂, hQ⟩ := hq
  obtain ⟨x, hx, h₂x⟩ := (ResUT.CompS.assoc ρ₂ g₂ g₁ ρ').mpr ⟨ρ₁, hc₂, hc₁⟩
  exact ⟨ρ₂, x, h₂x, hg₂.compS hx hg₁, hQ⟩

/-- A final term whose whole end, re-read, may be left as garbage. -/
theorem twpG_here_drop {F : TFrame} {Q : TPost} {n : Nat} {w : TWd} {ls : List (SRecT w.K)}
    {O : List (FrameRecT w.K)} {e : Expr} {ρ : TRes w.K} (hfin : ∀ μ, Final (ℍ := ℍ) μ e)
    (hn : NoOwnT ρ)
    (hQ : ∀ (w₀ : TWd) (ls₀ : List (SRecT w₀.K)) (O₀ : List (FrameRecT w₀.K)),
      RecsRR w₀.Θ O O₀ → Q n w₀ ls₀ O₀ e PMap.empty) :
    twpG (ℍ := ℍ) F Q n w ls O e ρ := by
  intro g ρg hg hc
  refine twp_here hfin fun w₀ ρ₀ ls₀ O₀ _ hr _ hO => ?_
  exact ⟨PMap.empty, ρ₀, ResUT.CompS.comm (ResUT.compS_empty_right _),
    (hn.compS hc hg).rr hr, hQ w₀ ls₀ O₀ hO⟩

/-! ### (ii) A lend still does not end while the frame holds a copy -/

/-- **`twp_refuses_lendEnd_live_copy` at `twpG`**: the lender holds the lend cell and owns the
record, the frame holds a copy; no run ends with `ℓ ↦ own(())` in the part read by the
postcondition. The `own` cell is in the end resource beside the garbage, and the end world would
compose the frame's copy with it. `↭` is not read. -/
theorem twpG_refuses_lendEnd_live_copy (F : TFrame) (hF : F wE (viewRes (lfE 1) 1)) :
    ¬ twpG (ℍ := ℍ) F QOwnBack 1 wE lsOne [lendRec 1] (.val .unit) (viewRes (lfE 1) 1) := by
  intro hG
  have h := hG PMap.empty _ noOwnT_empty (ResUT.compS_empty_right _)
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
  obtain ⟨w', ρf', ρ', fρ', psF', ps', O', ls', -, hrf, -, -, hc', -, -, -,
      ⟨ρ₁, g', hρ₁g, -, hρ₁⟩, -, -, -⟩ :=
    h wE (viewRes (lfE 1) 1) (viewRes (lfE 1) 1) (viewRes (lfE 1) 1) lsOne [lendRec 1]
      [lendRec 1] [] _ (TWd.Ext.refl _ _) rr_view (.cons ⟨lendRec_rr 1, rfl⟩ .nil)
      (.cons (lendRec_rr 1) .nil) hF ⟨hdup.1, _, hdup, hI₁.valid⟩ hdup hS hR₁ hI₁ hfd 0 _ _
      (by omega) (.refl _ _) (LogRel.Core.final_val _ Val.unit)
  have hρ₁' : ρ₁ = ResUT.single 1 (CellUT.ownOf BoCa.Val.unit) := hρ₁
  subst hρ₁'
  obtain ⟨-, hρ'1⟩ := ResUT.CompS.get_left_of_ne_imm hρ₁g (ResUT.single_get_self _ _)
    (by simp [CellUT.ownOf, CellUT.kind])
  obtain rfl := rr_view_eq hrf
  rcases ResUT.Comp.get hc' 1 with ⟨f, -, -⟩ | ⟨χ, -, f, -⟩ | ⟨χ, f, -, -⟩ |
      ⟨χ₁, χ₂, χ, -, f₂, -, hC⟩
  · simp [viewRes] at f
  · rw [hρ'1] at f; cases f
  · simp [viewRes] at f
  · rw [hρ'1] at f₂
    cases f₂
    obtain ⟨s₁, s₂, v, ρ, h₁, h₂, h₃, -, e₂, -⟩ := hC
    exact absurd (congrArg CellUT.kind e₂) (by simp [CellUT.ownOf, CellUT.kind, CellUT.immOf])

/-! ### What a garbage part admits that `twp` refuses -/

/-- **The last copy may be left as garbage**: the configuration of `twp_refuses_last_copy`
(the frame owns the record and holds nothing, the run holds the only copy), admitted. -/
theorem twpG_admits_drop_last_copy (F : TFrame) (n : Nat) :
    twpG (ℍ := ℍ) F QGiveUp n wE lsOne [] (.val .unit) (viewRes (lfE 1) 1) :=
  twpG_here_drop (fun μ => LogRel.Core.final_val μ Val.unit)
    (noOwnT_single (by simp [viewCell, CellUT.kind, CellUT.immOf]))
    fun _ _ _ hO => by cases hO; exact ⟨rfl, rfl⟩

/-- The postcondition of a closed program at `TopAdequacyT`: the result holds nothing. -/
def QNothing : TPost := fun _ _ _ _ _ ρ => ρ = PMap.empty

/-- **A run may end holding nothing while it owns a live lend record**: the run holds the lend's
view and owns `lendRec 1`; it ends at `()` with the view left as garbage. Its end memory is its
start memory, which holds `1`. `TopAdequacyT`'s premise on `Q` (`ρ = ∅`) does not see the
record. -/
theorem twpG_ends_record_live (F : TFrame) (n : Nat) :
    twpG (ℍ := ℍ) F QNothing n wE lsOne [lendRec 1] (.val .unit) (viewRes (lfE 1) 1) :=
  twpG_here_drop (fun μ => LogRel.Core.final_val μ Val.unit)
    (noOwnT_single (by simp [viewCell, CellUT.kind, CellUT.immOf])) fun _ _ _ _ => rfl

/-- **`twp` refuses it**: the end resource is empty and the frame holds nothing, so the end world
is empty and lowers to the empty memory, while the run, at `()`, ends at its start memory, which
holds `1`. -/
theorem not_twp_ends_record_live (F : TFrame) (hF : F wE PMap.empty) :
    ¬ twp (ℍ := ℍ) F QNothing 1 wE lsOne [lendRec 1] (.val .unit) (viewRes (lfE 1) 1) := by
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
  have hS : SplitT [lendRec (K := wE.K) 1] [lendRec 1] [] :=
    ⟨fun p => by simp, fun p _ q hq => by simp at hq⟩
  obtain ⟨w', ρf', ρ', fρ', psF', ps', O', ls', -, hrf, -, -, hc', -, -, hI', hρ', -, -, -⟩ :=
    h wE (viewRes (lfE 1) 1) PMap.empty (viewRes (lfE 1) 1) lsOne [lendRec 1] [lendRec 1] [] _
      (TWd.Ext.refl _ _) rr_view (.cons ⟨lendRec_rr 1, rfl⟩ .nil) (.cons (lendRec_rr 1) .nil)
      hF ⟨hc.1, _, hc, hI₁.valid⟩ hc hS hR₁ hI₁ hfd 0 _ _ (by omega) (.refl _ _)
      (LogRel.Core.final_val _ Val.unit)
  have hρ'' : ρ' = PMap.empty := hρ'
  subst hρ''
  obtain rfl := RR.of_empty hrf
  obtain rfl := ResUT.CompS.functional hc' (ResUT.compS_empty_right _)
  obtain ⟨σ, hσ, hμ⟩ := hI'.2
  have := hμ 1
  rw [flat_empty_get hσ 1] at this
  simp [BoCa.BoLo.Heap.upd] at this

/-! ### (iii) Core's `MFPost`, read without the garbage -/

/-- **Core's `MFPost`** (WpN.lean:604, branch `tree-inv`) at the tree: the part read by the
postcondition lies in `Res_α`, and the borrow handed back as `ℓ ↦ own(u)` beside content in the
location's code satisfies `Q`. `MFPostT` (`Core/TreeMutFrame.lean`, branch `tree-791`) is the
second conjunct. -/
def MFPostG (l : BoCa.Loc) (α : Life) (A : KTy) (Q : TPost) : TPost := fun k w ls O t ρ' =>
  ρ'.InStratum (TSet.single α) ∧
  ∀ (u : BoCa.Val) (Y : TRes w.K), ResUT.CompS ρ' (ResUT.single l (CellUT.ownOf u)) Y →
    ∀ σ, (A.interp w.Θ).P w.K u σ → ∀ Z, ResUT.CompS Y σ Z → Q k w ls O t Z

/-- A `mut` cell at `{α}` is not in `Cell_{α}`. -/
theorem mut_single_not_inStratum {K : WCactus} {α : Life} {v : BoCa.Val} {ρP : TRes K}
    {hP : ρP.InStratum (TSet.single α)} {P : BoCa.Val → SPropST BoCa.Loc BoCa.Val K (TSet.single α)}
    {hw : P v ⟨ρP, hP⟩} :
    ¬ (CellUT.mutOf (TSet.single α) v ρP hP P hw).InStratum (TSet.single α) := by
  intro h
  have := h α (by simp [TSet.single_set]) α (by simp [TSet.single_set])
  exact Cactus.lt_irrefl _ _ this

/-- **An end keeping the borrow does not meet `MFPostG`**: the route `mfPostT_of_get` took is
closed. -/
theorem mfPostG_of_mut_false {l : BoCa.Loc} {α : Life} {A : KTy} {Q : TPost} {k : Nat} {w : TWd}
    {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)} {t : Expr} {ρ' : TRes w.K}
    {v : BoCa.Val} {ρP : TRes w.K} {hP : ρP.InStratum (TSet.single α)}
    {P : BoCa.Val → SPropST BoCa.Loc BoCa.Val w.K (TSet.single α)} {hw : P v ⟨ρP, hP⟩}
    (e : ρ'.get l = some (CellUT.mutOf (TSet.single α) v ρP hP P hw)) :
    ¬ MFPostG l α A Q k w ls O t ρ' :=
  fun h => mut_single_not_inStratum (h.1 l _ e)

/-- The postcondition that refuses every end. -/
def QFalse : TPost := fun _ _ _ _ _ _ => False

/-- **An end without the borrow reads `Q`**: at `A = unit`, nothing at `ℓ` in the part read, the
handed-back `ℓ ↦ own(())` with empty content is a composite `Q` must accept, so at `False` the
postcondition fails. -/
theorem mfPostG_none_false {l : BoCa.Loc} {α : Life} {k : Nat} {w : TWd}
    {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)} {t : Expr} {ρ' : TRes w.K}
    (e : ρ'.get l = none) : ¬ MFPostG l α KTy.unit QFalse k w ls O t ρ' := by
  rintro ⟨-, h⟩
  obtain ⟨Y, hY⟩ := (ResUT.compS_defined_iff ρ' (ResUT.single l (CellUT.ownOf BoCa.Val.unit))).mpr
    (compatS_single_of_get_noneT e)
  exact h BoCa.Val.unit Y hY PMap.empty ⟨rfl, rfl⟩ Y (ResUT.compS_empty_right _)

/-- The code typing typing location `1` at `unit`. -/
def ΘU : CodeTy := fun x => if x = 1 then some KTy.unit else none

/-- The chain world typing `1` at `unit`. -/
abbrev wU : TWd := ⟨chainP, ΘU, tmplT _ ΘU⟩

/-- A cell's invariant read off its location's code. -/
def codePG (w : TWd) (A : KTy) (b : TSet) : BoCa.Val → SPropST BoCa.Loc BoCa.Val w.K b :=
  fun u r => (A.interp w.Θ).P w.K u r.val

theorem hP1 : ResUT.InStratum (TSet.single (lfE 1)) (PMap.empty : TRes wU.K) :=
  ResUT.inStratum_empty _

theorem hw1 : codePG wU KTy.unit (TSet.single (lfE 1)) BoCa.Val.unit ⟨PMap.empty, hP1⟩ :=
  ⟨rfl, rfl⟩

/-- The borrow of `not_cerwpTMFrameC`'s configuration: `1 ↦ mut({1}, (), ∅)` at the code `unit`. -/
def BM1 : TRes wU.K :=
  ResUT.single 1 (CellUT.mutOf (TSet.single (lfE 1)) BoCa.Val.unit PMap.empty hP1
    (codePG wU KTy.unit (TSet.single (lfE 1))) hw1)

/-- The lender's postcondition: the `own` cell is back at `1`. -/
def QBack : TPost := fun _ _ _ _ _ Z => ∃ u, Z.get 1 = some (CellUT.ownOf u)

/-- **The borrowed run of `not_cerwpTMFrameC`'s configuration meets Core's `MFPost` by leaving
the borrow as garbage**, at every frame condition and index, and the postcondition read is the
lender's, at the handed-back `own` cell. -/
theorem twpG_admits_borrow_in_garbage (F : TFrame) (n : Nat) :
    twpG (ℍ := ℍ) F (MFPostG 1 (lfE 1) KTy.unit QBack) n wU [] [] (.val .unit) BM1 := by
  refine twpG_here_drop (fun μ => LogRel.Core.final_val μ Val.unit)
    (noOwnT_single (by simp [CellUT.mutOf, CellUT.kind])) fun w₀ _ _ _ => ?_
  refine ⟨ResUT.inStratum_empty _, fun u Y hY σ _ Z hZ => ?_⟩
  obtain rfl := ResUT.CompS.functional hY (ResUT.CompS.comm (ResUT.compS_empty_right _))
  exact ⟨u, (ResUT.CompS.get_left_of_ne_imm hZ (ResUT.single_get_self _ _)
    (by simp [CellUT.ownOf, CellUT.kind])).2⟩

/-! ## Q2. A growth-only store typing -/

/-- **Growth-only extension of worlds**: the tree kept, every typed location kept at its code. -/
def _root_.BoCa.Fig16.Tree.TWd.GrowExt (w w' : TWd) : Prop :=
  w.K.Ext w'.K ∧ ∀ l A, w.Θ l = some A → w'.Θ l = some A

theorem _root_.BoCa.Fig16.Tree.TWd.GrowExt.refl (w : TWd) : w.GrowExt w := ⟨WCactus.Ext.refl _, fun _ _ h => h⟩

theorem _root_.BoCa.Fig16.Tree.TWd.GrowExt.trans {w₁ w₂ w₃ : TWd} (h₁ : w₁.GrowExt w₂) (h₂ : w₂.GrowExt w₃) :
    w₁.GrowExt w₃ :=
  ⟨WCactus.Ext.trans h₁.1 h₂.1, fun l A h => h₂.2 l A (h₁.2 l A h)⟩

/-- **The extension `not_cerwpTMFrame` and `antiInnerVal_retypes` start from is not a growth**:
from `1` typed at `unit` to `1` untyped. -/
theorem not_growExt_wU_wE : ¬ wU.GrowExt wE := fun h => by
  have := h.2 1 KTy.unit (by simp [ΘU])
  simp at this

/-- Typing a location the empty typing misses is a growth. -/
theorem growExt_wE_wU : wE.GrowExt wU := ⟨WCactus.Ext.refl _, fun _ _ h => by simp at h⟩

/-- `wU` with nothing held and the empty memory is a world: `1` is typed and not allocated (as
after `1` was allocated, lent at `unit`, and freed). -/
theorem winv_wU_empty : WInv wU (PMap.empty : TRes wU.K) (fun _ => none) :=
  ⟨fun _ _ e => by simp at e, lower_emptyT⟩

theorem recInv_wU_empty : RecInv wU (PMap.empty : TRes wU.K) [] [] :=
  ⟨.empty, fun _ hx => by simp at hx⟩

/-- **`alloc` may return `1`** at the empty memory, in every context. -/
theorem alloc_returns_one (Kc : Kont) (v : BoCa.Val) :
    BoCa.BoLo.Step1 (ℍ := ℍ) (fun _ => none) (Kc.plug (.app (.val (.prim .alloc)) (.val v)))
      (BoCa.BoLo.Heap.upd (fun _ => none) 1 v) (Kc.plug (.val (.loc 1))) :=
  (step1_alloc_iff Kc v).2 ⟨1, rfl, rfl, rfl⟩

/-- **What a `mut` lend of an allocated location asks of a growth-only typing**: at every start
world a run from the empty world may begin at (a growth of `wE`, with its invariants), and every
location the memory misses (which `alloc` may return), a growth types the location at `A`. A Mut
Frame at `A` reads `w.Θ ℓ = some A` at its world (`CerwpTMFrame`), and every world after the
start is a growth of it. -/
def AllocThenTypeG (A : KTy) : Prop :=
  ∀ (w₀ : TWd) (μ : Heap) (l : BoCa.Loc), wE.GrowExt w₀ → WInv w₀ PMap.empty μ →
    RecInv w₀ PMap.empty [] [] → μ l = none → ∃ w' : TWd, w₀.GrowExt w' ∧ w'.Θ l = some A

/-- **Refused at any code but `unit`**: start at `wU` (`1` typed at `unit`, not allocated); `alloc`
may return `1` (`alloc_returns_one`); no growth of `wU` types `1` at `unit + unit`. -/
theorem not_allocThenTypeG : ¬ AllocThenTypeG (KTy.sum KTy.unit KTy.unit) := by
  intro h
  obtain ⟨w', hg, hA⟩ := h wU (fun _ => none) 1 growExt_wE_wU winv_wU_empty recInv_wU_empty rfl
  rw [hg.2 1 KTy.unit (by simp [ΘU])] at hA
  cases hA

/-- **The tree's `TWd.Ext` admits the re-typing Core's Mut Frame makes** (`Φ.set l A F`,
StopFrameN.lean:156 on `tree-inv`): a location no `mut` cell of the carried resource is at may
take another code. -/
theorem ext_retypes_unheld :
    wU.Ext ⟨chainP, fun x => if x = 1 then some (KTy.sum KTy.unit KTy.unit) else none,
      tmplT _ (fun x => if x = 1 then some (KTy.sum KTy.unit KTy.unit) else none)⟩
      (ResUT.single 1 (CellUT.ownOf BoCa.Val.unit)) :=
  ⟨WCactus.Ext.refl _, fun _ hl => absurd hl not_holdsMut_own⟩

/-! ### Q2, narrowed: re-typing only where the carried resource holds no cell -/

/-- **Extension pinning every held location**: `TWd.Ext`, and every location the carried resource
holds a cell at keeps its code. A location no cell of the resource is at (a freed one) may still
be re-typed. -/
def _root_.BoCa.Fig16.Tree.TWd.PinExt (w w' : TWd) (ρ : TRes w.K) : Prop :=
  w.Ext w' ρ ∧ ∀ l ψ, ρ.get l = some ψ → w'.Θ l = w.Θ l

/-- The extension `not_cerwpTMFrame` and `antiInnerVal_retypes` start from is not pinned: the
run holds `1 ↦ own(())`, and `wE` drops `1`'s code. -/
theorem not_pinExt_wU_wE :
    ¬ wU.PinExt wE (ResUT.single 1 (CellUT.ownOf BoCa.Val.unit)) := fun h => by
  have := h.2 1 _ (ResUT.single_get_self _ _)
  simp [ΘU] at this

/-- The typing with `1` at `unit + unit`. -/
def ΘS : CodeTy := fun x => if x = 1 then some (KTy.sum KTy.unit KTy.unit) else none

/-- **A location nothing holds is re-typed**: reuse of a freed location is kept. -/
theorem pinExt_retypes_unheld :
    wU.PinExt ⟨chainP, ΘS, tmplT _ ΘS⟩ (PMap.empty : TRes wU.K) :=
  ⟨⟨WCactus.Ext.refl _, fun _ hl => by cases hl <;> simp_all⟩, fun _ _ e => by simp at e⟩

/-- **A held `own` location keeps its code**: the re-typing Core's Mut Frame makes for the
borrowed run (`Φ.set l A F`) is not a pinned extension, so the code a Mut Frame reads must be
the location's code from before it was held. -/
theorem pinExt_keeps_held {w' : TWd}
    (h : wU.PinExt w' (ResUT.single 1 (CellUT.ownOf BoCa.Val.unit))) :
    w'.Θ 1 = some KTy.unit := by
  rw [h.2 1 _ (ResUT.single_get_self _ _)]
  simp [ΘU]

/-- **What a `mut` lend of an allocated location asks of a pinned typing**, at the run's own
`own` cell: some pinned extension carrying it types the location at `A`. -/
def OwnThenTypeP (A : KTy) : Prop :=
  ∀ w' : TWd, wU.PinExt w' (ResUT.single 1 (CellUT.ownOf BoCa.Val.unit)) → w'.Θ 1 = some A

/-- **Refused at any code but the one held**. -/
theorem not_ownThenTypeP : ¬ OwnThenTypeP (KTy.sum KTy.unit KTy.unit) := by
  intro h
  have := h wU ⟨TWd.Ext.refl _ _, fun _ _ _ => rfl⟩
  simp [ΘU] at this

end BoCa.Fig16.Tree.Wp

end
