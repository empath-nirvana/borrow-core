import DtorUnwind.TreeWp.Cactus
import DtorUnwind.Tree.Port.Six34to39
import DtorUnwind.Tree.Port.ReborrowLowering
import DtorUnwind.Tree.Graft

/-!
# The world operations over the tree world

Each operation changes the world under every frame and keeps `WInv` (the cactus invariant's
world part) and the memory. The resource changes are the printed lemmas, read over the
tree-stratified carrier (`Tree/Port/`):

* **fresh lend, `imm`**: `ℓ ↦ own(v) ● ρ_v` becomes `ℓ ↦ imm({α}, v, ρ_v)`: `#` by 6.34, `⟦·⟧`
  by 6.26 and 6.8 (`immLend_world`);
* **fresh lend, `mut`**: `ℓ ↦ mut({α}, v, ρ_v, 𝒱⟦Θ ℓ⟧_K)`: `#` by 6.23, `⟦·⟧` by 6.25; the cell
  is covered because its invariant is `Θ ℓ` read at the current tree (`mutLend_world`);
* **end of a `mut` lend**: back to `own(v) ● ρ_v`: `#` by 6.22, `⟦·⟧` by 6.25 (`mutEnd_world`);
* **fresh child, graft**: `ParentFn.graftOf` moves a subtree's root under a new parent; when the
  old parent is above the new one the tree is extended (`TWd.graft_ext`), and `cactusT_extend`
  re-reads every branch. A fresh child is the graft of an unused leaf from `⊤`
  (`TWd.fresh_ext`).
* **the store typing grows** at a `mut` lend of a location it does not type (`TWd.addTy`,
  `TWd.addTy_ext`); `Cov`, `RC`, `RR` read at the old typing hold at the new (`Cov.mono`,
  `RR.mono`). A location keeps its type for the whole run: `LocTy.Le` is growth only.
* **capture** is `cactusT_move`.

`winv_swap` is the shape all resource changes share: a part `A` of the world replaced by `B`,
with `#` against the rest carried from `A` to `B` and the two lowering equally.
-/

noncomputable section

namespace BoCa.Fig16.Tree.Wp
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree

/-! ### Coverage of a composite -/

theorem CovR.compS {Θ : LocTy} {K : WCactus} {a b y : TRes K} (ha : CovR Θ K a)
    (hb : CovR Θ K b) (hc : ResUT.CompS a b y) : CovR Θ K y := by
  intro l ψ e
  have hl := hc.2 l
  rw [e] at hl
  cases ea : a.get l <;> cases eb : b.get l <;> rw [ea, eb] at hl <;>
    simp only [G.OptComp] at hl
  · cases hl
  · cases hl; exact hb l _ eb
  · cases hl; exact ha l _ ea
  · obtain ⟨ψ', e', s₁, s₂, v, χ, a₁, a₂, a₃, h₁, h₂, h₃⟩ := hl
    cases e'
    subst h₃
    rw [h₁] at ea
    exact Cov.immOf_iff.mpr (Cov.immOf_iff.mp (ha l _ ea))

/-! ### A part of the world replaced -/

/-- **A part `A` of the world replaced by `B`**: `#` against the rest carried over, the two
lowering equally, `B` covered when `A` is. The world invariant and the memory are kept. -/
theorem winv_swap {w : TWd} {X A B fρ : TRes w.K} {μ : BoCa.Loc → Option BoCa.Val}
    (hc : ResUT.CompS X A fρ) (hI : WInv w fρ μ) (hh : ResUT.Hash X A → ResUT.Hash X B)
    (hl : ResUT.Valid B → ResUT.Valid A →
      ∀ m, ResUT.Lower B m ↔ ResUT.Lower A m)
    (hcov : CovR w.Θ w.K A → CovR w.Θ w.K B) :
    ∃ fρ', ResUT.CompS X B fρ' ∧ WInv w fρ' μ ∧ ResUT.Hash X B := by
  have hXA : ResUT.Hash X A := hash_of_inv hc hI
  have hXB := hh hXA
  obtain ⟨fρ', hc', hv'⟩ := hXB.2
  have hvA := (ResUT.Valid.split hc hI.valid).2
  have hvB := (ResUT.Valid.split hc' hv').2
  have hL := ResUT.lower_congr_iff (fun m => (hl hvB hvA m).symm) hc hXA hc' hXB
  refine ⟨fρ', hc', ⟨CovR.compS (covf_of_comp hc hI) (hcov (cov_of_comp hc hI)) hc', hI.2.1,
    (hL μ).mp hI.2.2⟩, hXB⟩

/-! ### Lends -/

/-- **A fresh `imm` lend at the world**: `ℓ ↦ own(v)` beside the payload `ρ_v` becomes
`ℓ ↦ imm(s, v, ρ_v)` (6.34, 6.26, 6.8). -/
theorem immLend_world {w : TWd} {X W fρ ρv : TRes w.K} {μ : BoCa.Loc → Option BoCa.Val}
    {l : BoCa.Loc} {s : TSet} {v : BoCa.Val} (hs : ρv.InStratum s)
    (hW : ResUT.CompS ρv (ResUT.single l (CellUT.ownOf v)) W) (hc : ResUT.CompS X W fρ)
    (hI : WInv w fρ μ) :
    ∃ fρ', ResUT.CompS X (ResUT.single l (CellUT.immOf s v ρv hs)) fρ' ∧ WInv w fρ' μ ∧
      ResUT.Hash X (ResUT.single l (CellUT.immOf s v ρv hs)) := by
  refine winv_swap hc hI (fun h => ResUT.six34 hW h) (fun hvB hvA m => ResUT.six26 hW hvB hvA)
    fun hcW => ?_
  intro m ψ e
  have hcv : CovR w.Θ w.K ρv := CovR.of_compS_left hW hcW
  rw [ResUT.single, PMap.sng_get] at e
  split_ifs at e with hm
  cases e
  exact Cov.immOf_iff.mpr hcv

/-- The invariant a `mut` cell at `ℓ` stores at the tree `K`: `Θ ℓ = τ` read at `K`. -/
def tyPred (τ : KSem) (K : WCactus) (s : TSet) : BoCa.Val → SPropST BoCa.Loc BoCa.Val K s :=
  fun v r => τ.P K v r.val

/-- **A fresh `mut` lend at the world**: `ℓ ↦ own(v)` beside `ρ_v` becomes
`ℓ ↦ mut(s, v, ρ_v, 𝒱⟦τ⟧_K)` where `Θ ℓ = τ` (6.23, 6.25, 6.8). The payload is in `τ` at the
current tree (`hτ`): that is the lender's obligation. -/
theorem mutLend_world {w : TWd} {X W fρ ρv : TRes w.K} {μ : BoCa.Loc → Option BoCa.Val}
    {l : BoCa.Loc} {s : TSet} [Fact (w.K.Anti s)] {v : BoCa.Val} {τ : KSem} (hΘ : w.Θ l = some τ)
    (hs : ρv.InStratum s) (hτ : τ.P w.K v ρv)
    (hW : ResUT.CompS ρv (ResUT.single l (CellUT.ownOf v)) W) (hc : ResUT.CompS X W fρ)
    (hI : WInv w fρ μ) :
    ∃ fρ', ResUT.CompS X (ResUT.single l
        (CellUT.mutOf s v ρv hs (tyPred τ w.K s) hτ)) fρ' ∧ WInv w fρ' μ ∧
      ResUT.Hash X (ResUT.single l (CellUT.mutOf s v ρv hs (tyPred τ w.K s) hτ)) := by
  refine winv_swap hc hI (fun h => ResUT.six23 hW h) (fun hvB hvA m => ResUT.six25 hW hvB hvA)
    fun hcW => ?_
  intro m ψ e
  have hcv : CovR w.Θ w.K ρv := CovR.of_compS_left hW hcW
  rw [ResUT.single, PMap.sng_get] at e
  split_ifs at e with hm
  cases e
  subst hm
  refine .mut _ _ τ hΘ (fun w' r => ?_) (fun k ψ e => hcv k ψ ?_)
  · show tyPred τ w.K s w' r.toS ↔ τ.P w.K w' r.toU
    rfl
  · simpa [MutT.res, ResST.toU_toRes] using e

/-- **The end of a `mut` lend at the world**: `ℓ ↦ mut(s, v, ρ_v, P̂)` back to `ℓ ↦ own(v)` beside
`ρ_v` (6.22, 6.25, 6.8). Nothing is asked of the frame: a `mut` cell is exclusive. -/
theorem mutEnd_world {w : TWd} {X W fρ ρv : TRes w.K} {μ : BoCa.Loc → Option BoCa.Val}
    {l : BoCa.Loc} {s : TSet} [Fact (w.K.Anti s)] {v : BoCa.Val} (hs : ρv.InStratum s)
    {P : BoCa.Val → SPropST BoCa.Loc BoCa.Val w.K s} {hw : P v ⟨ρv, hs⟩}
    (hW : ResUT.CompS ρv (ResUT.single l (CellUT.ownOf v)) W)
    (hc : ResUT.CompS X (ResUT.single l (CellUT.mutOf s v ρv hs P hw)) fρ) (hI : WInv w fρ μ) :
    ∃ fρ', ResUT.CompS X W fρ' ∧ WInv w fρ' μ ∧ ResUT.Hash X W := by
  refine winv_swap hc hI (fun h => ResUT.six22 hW h)
    (fun hvB hvA m => (ResUT.six25 hW hvA hvB).symm) fun hcm => ?_
  have hcv : CovR w.Θ w.K ρv := by
    intro k ψ e
    have h := hcm l _ (by rw [ResUT.single, PMap.sng_get, if_pos rfl])
    cases h with
    | «mut» _ _ _ _ _ hw' => exact hw' k ψ (by simpa [MutT.res, ResST.toU_toRes] using e)
  exact CovR.compS hcv (fun k ψ e => by
    rw [ResUT.single, PMap.sng_get] at e
    split_ifs at e
    cases e; exact .own _ _) hW

end BoCa.Fig16.Tree.Wp

namespace BoCa.Fig16.Tree

/-! ### The tree grows: a graft, a fresh child -/

open Classical in
/-- **`r`'s subtree moved under `t`**: `r`'s parent becomes `t`; the ranks of `r`'s subtree are
shifted past `t`'s so parents still decrease them. -/
def ParentFn.graftOf (P : ParentFn) (r t : Nat) (hr : r ≠ 0) (ht : ¬ P.Anc t r) : ParentFn where
  par n := if n = r then t else P.par n
  rank n := if P.Anc n r then P.rank n + (P.rank t + 1) else P.rank n
  par_zero := by rw [if_neg (Ne.symm hr)]; exact P.par_zero
  rank_lt n hn := by
    by_cases hnr : n = r
    · subst hnr
      rw [if_pos rfl, if_neg ht, if_pos (.refl n)]
      omega
    · rw [if_neg hnr]
      by_cases hA : P.Anc n r
      · have hp : P.Anc (P.par n) r := by
          cases hA with
          | refl => exact absurd rfl hnr
          | up h => exact h
        rw [if_pos hp, if_pos hA]
        have := P.rank_lt n hn
        omega
      · have hp : ¬ P.Anc (P.par n) r := fun h => hA (.up h)
        rw [if_neg hp, if_neg hA]
        exact P.rank_lt n hn

theorem ParentFn.graftOf_graft (P : ParentFn) {r t : Nat} (hr : r ≠ 0) (ht : ¬ P.Anc t r) :
    P.Graft (P.graftOf r t hr ht) r t :=
  ⟨by simp [ParentFn.graftOf], fun n hn => by simp [ParentFn.graftOf, hn]⟩

/-- The world with `r`'s subtree grafted under `t`. -/
def TWd.graft (w : TWd) (r t : Nat) (hr : r ≠ 0) (ht : ¬ w.P.Anc t r) : TWd :=
  ⟨w.P.graftOf r t hr ht, w.Θ⟩

/-- **A graft whose capture point is above the resume point extends the world** (`graft_mono`). -/
theorem TWd.graft_ext (w : TWd) {r t : Nat} (hr : r ≠ 0) (ht : ¬ w.P.Anc t r)
    (hc : w.P.Anc t (w.P.par r)) : w.Ext (w.graft r t hr ht) :=
  ⟨fun {_ _} h => ⟨ParentFn.graft_mono (w.P.graftOf_graft hr ht) hc ht h.1, h.2⟩,
    LocTy.Le.refl _⟩

/-- After the graft, `r` is nested in `t`. -/
theorem TWd.graft_lt (w : TWd) {r t : Nat} (hr : r ≠ 0) (ht : ¬ w.P.Anc t r) (hrt : r ≠ t) :
    (w.graft r t hr ht).K.lt (OrderDual.toDual r) (OrderDual.toDual t) :=
  ⟨.up (by simp [TWd.graft, ParentFn.graftOf]; exact .refl t),
    fun e => hrt (OrderDual.toDual.injective e)⟩

/-- An unused lifetime: a leaf whose parent is `⊤`. -/
def TWd.Unused (w : TWd) (a : Nat) : Prop :=
  a ≠ 0 ∧ w.P.par a = 0 ∧ ∀ x, w.P.Anc x a → x = a

/-- **A fresh child of `n`**: an unused leaf grafted under `n` extends the world, and is nested
in `n` after. -/
theorem TWd.fresh_ext (w : TWd) {a n : Nat} (hu : w.Unused a) (hn : n ≠ a) :
    ∃ (ht : ¬ w.P.Anc n a), w.Ext (w.graft a n hu.1 ht) ∧
      (w.graft a n hu.1 ht).K.lt (OrderDual.toDual a) (OrderDual.toDual n) := by
  have ht : ¬ w.P.Anc n a := fun h => hn (hu.2.2 n h)
  refine ⟨ht, w.graft_ext hu.1 ht ?_, w.graft_lt hu.1 ht (Ne.symm hn)⟩
  rw [hu.2.1]
  exact w.P.anc_zero n

/-! ### The store typing grows -/

open Classical in
/-- `Θ[ℓ ↦ τ]`, at a location `Θ` does not type. -/
def TWd.addTy (w : TWd) (l : BoCa.Loc) (τ : KSem) : TWd :=
  ⟨w.P, fun m => if m = l then some τ else w.Θ m⟩

theorem TWd.addTy_ext (w : TWd) {l : BoCa.Loc} {τ : KSem} (hl : w.Θ l = none) :
    w.Ext (w.addTy l τ) := by
  refine ⟨WCactus.Ext.refl _, fun m τ' e => ?_⟩
  show (if m = l then some τ else w.Θ m) = some τ'
  rw [if_neg (fun h => by subst h; rw [hl] at e; cases e)]
  exact e

/-- **The types stay carried** when the new one is. -/
theorem TWd.addTy_monoUp (w : TWd) {l : BoCa.Loc} {τ : KSem} (hl : w.Θ l = none)
    (hM : MonoUp w.Θ) (hτ : KMonoUp (w.addTy l τ).Θ τ) : MonoUp (w.addTy l τ).Θ := by
  intro m τ' e Θ'' hΘ
  by_cases hm : m = l
  · subst hm
    have : τ' = τ := by simpa [TWd.addTy] using e.symm
    subst this
    exact hτ Θ'' hΘ
  · have e' : w.Θ m = some τ' := by simpa [TWd.addTy, hm] using e
    exact hM m τ' e' Θ'' ((w.addTy_ext hl).2.trans hΘ)

end BoCa.Fig16.Tree

end
