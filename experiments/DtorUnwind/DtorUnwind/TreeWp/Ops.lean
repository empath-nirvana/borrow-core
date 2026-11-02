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
* **fresh lend, `mut`**: `ℓ ↦ mut({α}, v, ρ_v, ⟦Θ ℓ⟧_K)`: `#` by 6.23, `⟦·⟧` by 6.25; the cell
  is covered because its invariant is the code `Θ ℓ` read at the current tree (`mutLend_world`);
* **end of a `mut` lend**: back to `own(v) ● ρ_v`: `#` by 6.22, `⟦·⟧` by 6.25 (`mutEnd_world`);
* **fresh child, graft**: `ParentFn.graftOf` moves a subtree's root under a new parent; when the
  old parent is above the new one the tree is extended (`TWd.graft_ext`), and `cactusT_extend`
  re-reads every branch. A fresh child is the graft of an unused leaf from `⊤`
  (`TWd.fresh_ext`).
* **a location re-typed** (`TWd.setTy`): the world extends carrying any resource that holds no
  `mut` cell there (`TWd.setTy_ext`, from `agreeOn_set`), so a fresh or freed location takes a
  new code, and `cactusT_extend` re-reads every branch.
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
    (hcov : CovR (sem w.Θ) w.K A → CovR (sem w.Θ) w.K B) :
    ∃ fρ', ResUT.CompS X B fρ' ∧ WInv w fρ' μ ∧ ResUT.Hash X B := by
  have hXA : ResUT.Hash X A := hash_of_inv hc hI
  have hXB := hh hXA
  obtain ⟨fρ', hc', hv'⟩ := hXB.2
  have hvA := (ResUT.Valid.split hc hI.valid).2
  have hvB := (ResUT.Valid.split hc' hv').2
  have hL := ResUT.lower_congr_iff (fun m => (hl hvB hvA m).symm) hc hXA hc' hXB
  refine ⟨fρ', hc', ⟨CovR.compS (covf_of_comp hc hI) (hcov (cov_of_comp hc hI)) hc',
    (hL μ).mp hI.2⟩, hXB⟩

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
  have hcv : CovR (sem w.Θ) w.K ρv := CovR.of_compS_left hW hcW
  rw [ResUT.single, PMap.sng_get] at e
  split_ifs at e with hm
  cases e
  exact Cov.immOf_iff.mpr hcv

/-- The invariant a `mut` cell at `ℓ` stores at the tree `K`: `Θ ℓ = τ` read at `K`. -/
def tyPred (τ : KSem) (K : WCactus) (s : TSet) : BoCa.Val → SPropST BoCa.Loc BoCa.Val K s :=
  fun v r => τ.P K v r.val

/-- **A fresh `mut` lend at the world**: `ℓ ↦ own(v)` beside `ρ_v` becomes
`ℓ ↦ mut(s, v, ρ_v, ⟦A⟧_K)` where `Θ ℓ = A` (6.23, 6.25, 6.8). The payload is in `A` at the
current tree (`hτ`): that is the lender's obligation. -/
theorem mutLend_world {w : TWd} {X W fρ ρv : TRes w.K} {μ : BoCa.Loc → Option BoCa.Val}
    {l : BoCa.Loc} {s : TSet} [Fact (w.K.Anti s)] {v : BoCa.Val} {A : KTy} (hΘ : w.Θ l = some A)
    (hs : ρv.InStratum s) (hτ : (A.interp w.Θ).P w.K v ρv)
    (hW : ResUT.CompS ρv (ResUT.single l (CellUT.ownOf v)) W) (hc : ResUT.CompS X W fρ)
    (hI : WInv w fρ μ) :
    ∃ fρ', ResUT.CompS X (ResUT.single l
        (CellUT.mutOf s v ρv hs (tyPred (A.interp w.Θ) w.K s) hτ)) fρ' ∧ WInv w fρ' μ ∧
      ResUT.Hash X (ResUT.single l
        (CellUT.mutOf s v ρv hs (tyPred (A.interp w.Θ) w.K s) hτ)) := by
  refine winv_swap hc hI (fun h => ResUT.six23 hW h) (fun hvB hvA m => ResUT.six25 hW hvB hvA)
    fun hcW => ?_
  intro m ψ e
  have hcv : CovR (sem w.Θ) w.K ρv := CovR.of_compS_left hW hcW
  rw [ResUT.single, PMap.sng_get] at e
  split_ifs at e with hm
  cases e
  subst hm
  refine .mut _ _ _ (sem_of hΘ) (fun w' r => ?_) (fun k ψ e => hcv k ψ ?_)
  · show tyPred (A.interp w.Θ) w.K s w' r.toS ↔ (A.interp w.Θ).P w.K w' r.toU
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
  have hcv : CovR (sem w.Θ) w.K ρv := by
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
open BoCa.Fig16.Tree.Wp

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

/-- **A graft whose capture point is above the resume point extends the world**, carrying every
resource (`graft_mono`). -/
theorem TWd.graft_ext (w : TWd) {r t : Nat} (hr : r ≠ 0) (ht : ¬ w.P.Anc t r)
    (hc : w.P.Anc t (w.P.par r)) (ρ : TRes w.K) : w.Ext (w.graft r t hr ht) ρ :=
  ⟨fun {_ _} h => ⟨ParentFn.graft_mono (w.P.graftOf_graft hr ht) hc ht h.1, h.2⟩,
    AgreeOn.refl _ _⟩

/-- After the graft, `r` is nested in `t`. -/
theorem TWd.graft_lt (w : TWd) {r t : Nat} (hr : r ≠ 0) (ht : ¬ w.P.Anc t r) (hrt : r ≠ t) :
    (w.graft r t hr ht).K.lt (OrderDual.toDual r) (OrderDual.toDual t) :=
  ⟨.up (by simp [TWd.graft, ParentFn.graftOf]; exact .refl t),
    fun e => hrt (OrderDual.toDual.injective e)⟩

/-- An unused lifetime: a leaf whose parent is `⊤`. -/
def TWd.Unused (w : TWd) (a : Nat) : Prop :=
  a ≠ 0 ∧ w.P.par a = 0 ∧ ∀ x, w.P.Anc x a → x = a

/-- **A fresh child of `n`**: an unused leaf grafted under `n` extends the world, carrying every
resource, and is nested in `n` after. -/
theorem TWd.fresh_ext (w : TWd) {a n : Nat} (hu : w.Unused a) (hn : n ≠ a) :
    ∃ (ht : ¬ w.P.Anc n a), (∀ ρ : TRes w.K, w.Ext (w.graft a n hu.1 ht) ρ) ∧
      (w.graft a n hu.1 ht).K.lt (OrderDual.toDual a) (OrderDual.toDual n) := by
  have ht : ¬ w.P.Anc n a := fun h => hn (hu.2.2 n h)
  refine ⟨ht, w.graft_ext hu.1 ht ?_, w.graft_lt hu.1 ht (Ne.symm hn)⟩
  rw [hu.2.1]
  exact w.P.anc_zero n

/-! ### A location re-typed -/

open Classical in
/-- `Θ[ℓ ↦ B]`. -/
def TWd.setTy (w : TWd) (l : BoCa.Loc) (B : Option KTy) : TWd :=
  ⟨w.P, fun m => if m = l then B else w.Θ m⟩

/-- **Re-typing a location no `mut` cell of `ρ` is at extends the world carrying `ρ`.** -/
theorem TWd.setTy_ext (w : TWd) {l : BoCa.Loc} (B : Option KTy) {ρ : TRes w.K}
    (h : ¬ HoldsMut ρ l) : w.Ext (w.setTy l B) ρ :=
  ⟨WCactus.Ext.refl _, agreeOn_set w.Θ B h⟩

/-- Re-typing a location to the code it has is the identity. -/
theorem TWd.setTy_self (w : TWd) (l : BoCa.Loc) : w.setTy l (w.Θ l) = w := by
  obtain ⟨P, Θ⟩ := w
  simp only [TWd.setTy, TWd.mk.injEq, true_and]
  funext m
  by_cases h : m = l
  · subst h; simp
  · simp [h]

end BoCa.Fig16.Tree

end
