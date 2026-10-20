import Support.Dynamics.Machine
import Support.Dynamics.Arrays

/-!
# Support — Dynamics — the counted loop over data visits every element  `[spec §16]`

The relation proves that a `for` over data is total (`countTry_compatX`); it does not say that
the loop sees every element. That is a fact about the machine's steps, proved here once, on the
step relation, for the loops the elaboration makes (`forData` in `Frontend/Sugar.lean`):

* **The loop visits every index below its bound, in order, once each** (`countTry_runs`): if the
  step answers `inl` at each index, `count_try (f, (n, (i, s)))` runs it at `i, i + 1, …,
  len(n) − 1` and answers `inl` of the last state (`countRun`); no index is skipped and the loop
  does not stop before the bound. When the step answers `inr e`, the loop answers it at once
  (`countTry_exit`).
* **The bound of a view is its number of elements** (`arrLen_eq_of_lt`): a family `(ℓ, n)` of
  the relation has `n < 2³¹` (SPEC §9, the length bound), so `len(n) = n`.
* **At each index below the bound, `next` answers that element; at the bound it ends.** A shared
  view's step reads index `i` with `idx`, which answers the leaf `ℓ + i` exactly when `i < n`
  (`idxAns_lt`, `idxAns_ge`). An exclusive view's step splits the first leaf off the rest; after
  `i` steps the rest is `(ℓ + i, n − i)`, whose split answers the leaf `ℓ + i` while `i < n`
  (`splitFirst_lt`) and ends exactly at `i = n` (`splitFirst_end`).
* **A loop with no exit** is `count_fold`, which visits the same indices (`countFold_runs`) and
  answers the last state.
* **A count** `a..b` is the loop over `len(b − a)` from `0`, whose element at index `i` is
  `a + i`, or, at a literal start `a` in `[0, 2³¹)`, the loop over `len(b)` from `a`, whose
  element is the index: the indices it visits are those of `countTry_runs` or `countFold_runs`.

So the bound equals the number of elements: every element is visited, and none is dropped.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.BoLo
open BoCa

/-- The states a loop that never exits goes through: `F` at `i, i + 1, …, i + k − 1`, from the
state `s` and the memory `μ`.  `[spec §16]` -/
def countRun (F : UInt32 → Val → Heap → Heap × Val) : Nat → UInt32 → Val → Heap → Heap × Val
  | 0, _, s, μ => (μ, s)
  | k + 1, i, s, μ => countRun F k (i + 1) (F i s μ).2 (F i s μ).1

/-- `count_try` at a value: the redex. -/
abbrev countTryE (f : Val) (n i : UInt32) (s : Val) : Expr :=
  .app (.val (.prim .countTry)) (.val (Val.pair f (Val.pair (Val.i32 n) (Val.pair (Val.i32 i) s))))

/-- **The loop visits every index below its bound, in order.** If at every index `j` from `i` to
`len(n) − 1` the step runs from `(j, s)` to `inl` of `F j s μ`'s state, in its memory, the loop
from `i` runs to `inl` of the state after `F` at each of those indices, once each, in order.
`[spec §16]` -/
theorem countTry_runs (f : Val) (n : UInt32) (F : UInt32 → Val → Heap → Heap × Val)
    (hF : ∀ (j : UInt32) (s : Val) (μ : Heap), j < arrLen n →
      Steps μ (.app (.val f) (.val (Val.pair (Val.i32 j) s))) (F j s μ).1
        (.val (Val.inj₁ (F j s μ).2))) :
    ∀ (k : Nat) (i : UInt32) (s : Val) (μ : Heap), (arrLen n).toNat - i.toNat = k →
      Steps μ (countTryE f n i s) (countRun F k i s μ).1 (.val (Val.inj₁ (countRun F k i s μ).2)) := by
  intro k
  induction k with
  | zero =>
      intro i s μ hk
      have hi : ¬ i < arrLen n := by rw [UInt32.lt_iff_toNat_lt]; omega
      refine .more (.head (Head.countTry μ f n i s)) ?_
      unfold countTryNext
      rw [if_neg hi]
      exact .refl _ _
  | succ k ih =>
      intro i s μ hk
      have hi : i < arrLen n := by rw [UInt32.lt_iff_toNat_lt]; omega
      have hb : (arrLen n).toNat < 2 ^ 32 := UInt32.toNat_lt _
      have hi1 : (i + 1).toNat = i.toNat + 1 := by
        rw [UInt32.toNat_add]
        have : i.toNat < (arrLen n).toNat := UInt32.lt_iff_toNat_lt.mp hi
        simp only [UInt32.toNat_one]
        exact Nat.mod_eq_of_lt (by omega)
      refine .more (.head (Head.countTry μ f n i s)) ?_
      unfold countTryNext
      rw [if_pos hi]
      let K : Kont := .case .hole (.app (.val (.prim .countTry)) (.pair (.val (f.shift 1 0))
        (.pair (.val (.i32 n)) (.pair (.val (.i32 (i + 1))) (.var 0))))) (.inj₂ (.var 0))
      have h₁ := Steps.plug K (hF i s μ hi)
      refine Steps.trans h₁ (.more (.head (Head.case₁ _ (F i s μ).2 _ _)) ?_)
      rw [countTry_cont_subst]
      exact ih (i + 1) (F i s μ).2 (F i s μ).1 (by omega)

/-- **The loop's exit.** When the step answers `inr e` at index `i < len(n)`, the loop answers
`inr e`.  `[spec §16]` -/
theorem countTry_exit (f : Val) (n i : UInt32) (s e : Val) (μ μ' : Heap) (hi : i < arrLen n)
    (hf : Steps μ (.app (.val f) (.val (Val.pair (Val.i32 i) s))) μ' (.val (Val.inj₂ e))) :
    Steps μ (countTryE f n i s) μ' (.val (Val.inj₂ e)) := by
  refine .more (.head (Head.countTry μ f n i s)) ?_
  unfold countTryNext
  rw [if_pos hi]
  let K : Kont := .case .hole (.app (.val (.prim .countTry)) (.pair (.val (f.shift 1 0))
    (.pair (.val (.i32 n)) (.pair (.val (.i32 (i + 1))) (.var 0))))) (.inj₂ (.var 0))
  refine Steps.trans (Steps.plug K hf) (.more (.head (Head.case₂ _ e _ _)) ?_)
  exact .refl _ _

/-- `count_fold` at a value: the redex. -/
abbrev countE (f : Val) (n i : UInt32) (s : Val) : Expr :=
  .app (.val (.prim .count)) (.val (Val.pair f (Val.pair (Val.i32 n) (Val.pair (Val.i32 i) s))))

/-- **A loop with no exit visits every index below its bound, in order.** If at every index `j`
from `i` to `len(n) − 1` the step runs from `(j, s)` to `F j s μ`'s state, in its memory,
`count_fold` from `i` runs to the state after `F` at each of those indices, once each, in order.
`[spec §16]` -/
theorem countFold_runs (f : Val) (n : UInt32) (F : UInt32 → Val → Heap → Heap × Val)
    (hF : ∀ (j : UInt32) (s : Val) (μ : Heap), j < arrLen n →
      Steps μ (.app (.val f) (.val (Val.pair (Val.i32 j) s))) (F j s μ).1 (.val (F j s μ).2)) :
    ∀ (k : Nat) (i : UInt32) (s : Val) (μ : Heap), (arrLen n).toNat - i.toNat = k →
      Steps μ (countE f n i s) (countRun F k i s μ).1 (.val (countRun F k i s μ).2) := by
  intro k
  induction k with
  | zero =>
      intro i s μ hk
      have hi : ¬ i < arrLen n := by rw [UInt32.lt_iff_toNat_lt]; omega
      refine .more (.head (Head.count μ f n i s)) ?_
      unfold countNext
      rw [if_neg hi]
      exact .refl _ _
  | succ k ih =>
      intro i s μ hk
      have hi : i < arrLen n := by rw [UInt32.lt_iff_toNat_lt]; omega
      have hb : (arrLen n).toNat < 2 ^ 32 := UInt32.toNat_lt _
      have hi1 : (i + 1).toNat = i.toNat + 1 := by
        rw [UInt32.toNat_add]
        have : i.toNat < (arrLen n).toNat := UInt32.lt_iff_toNat_lt.mp hi
        simp only [UInt32.toNat_one]
        exact Nat.mod_eq_of_lt (by omega)
      refine .more (.head (Head.count μ f n i s)) ?_
      unfold countNext
      rw [if_pos hi]
      let K : Kont :=
        .appR (.val (.prim .count)) (.pairR f (.pairR (Val.i32 n) (.pairR (Val.i32 (i + 1)) .hole)))
      exact Steps.trans (Steps.plug K (hF i s μ hi)) (ih (i + 1) (F i s μ).2 (F i s μ).1 (by omega))

/-- The indices `countRun` visits: `i, i + 1, …, i + k − 1`, each once, in order. -/
theorem countRun_visits (F : UInt32 → Val → Heap → Heap × Val) :
    ∀ (k : Nat) (i : UInt32) (s : Val) (μ : Heap),
      countRun F (k + 1) i s μ = countRun F k (i + 1) (F i s μ).2 (F i s μ).1 := by
  intro k i s μ
  rfl

end BoCa.BoLo

namespace BoCa

/-- **The bound of a view is its length.** A family of the relation has `n < 2³¹` (SPEC §9), so
`len(n) = n`.  `[spec §16]` -/
theorem arrLen_eq_of_lt {n : UInt32} (hn : n.toNat < 2 ^ 31) : arrLen n = n := by
  unfold arrLen
  rw [if_pos (UInt32.lt_iff_toNat_lt.mpr (by simpa using hn))]

/-- **A shared view's element at an index below its length is that leaf.**  `[spec §16]` -/
theorem idxAns_lt (ℓ : Loc) {n i : UInt32} (h : i < n) :
    idxAns ℓ n i = Val.inj₁ (Val.loc (ℓ + i.toNat)) := by
  unfold idxAns
  rw [if_pos h]

/-- **At or past its length, a shared view has no element.**  `[spec §16]` -/
theorem idxAns_ge (ℓ : Loc) {n i : UInt32} (h : ¬ i < n) : idxAns ℓ n i = Val.inj₂ Val.unit := by
  unfold idxAns
  rw [if_neg h]

/-- An answer of `idx` that is a leaf. -/
def isLeaf (v : Val) : Bool := match v.1 with
  | .inj₁ _ => true
  | _ => false

/-- The number of indices below `n` at which `idx` answers a leaf is `n`, and past `n` there is
none: the bound is the number of elements.  `[spec §16]` -/
theorem idxAns_count (ℓ : Loc) (n : UInt32) :
    ((List.range n.toNat).filter fun j => isLeaf (idxAns ℓ n (UInt32.ofNat j))).length = n.toNat := by
  rw [List.filter_eq_self.mpr]
  · exact List.length_range
  · intro j hj
    have hj' : j < n.toNat := List.mem_range.mp hj
    have hn : n.toNat < 2 ^ 32 := UInt32.toNat_lt _
    have hlt : UInt32.ofNat j < n := by
      rw [UInt32.lt_iff_toNat_lt, UInt32.toNat_ofNat_of_lt' (by unfold UInt32.size; omega)]
      exact hj'
    rw [idxAns_lt ℓ hlt]
    rfl

/-- **An exclusive view's next element.** The rest after `i` steps of the loop over `(ℓ, n)` is
`(ℓ + i, n − i)`; while `i < n`, splitting its first leaf off answers the leaf `ℓ + i` (its one
leaf, at index `0`) and the rest after `i + 1` steps.  `[spec §16]` -/
theorem splitFirst_lt (ℓ : Loc) {n : UInt32} {i : Nat} (h : i < n.toNat) :
    splitAns (ℓ + i) (n - UInt32.ofNat i) 1 =
      Val.inj₁ (Val.pair (Val.arr (ℓ + i) 1) (Val.arr (ℓ + (i + 1)) (n - UInt32.ofNat (i + 1)))) ∧
    idxAns (ℓ + i) 1 0 = Val.inj₁ (Val.loc (ℓ + i)) := by
  have hn : n.toNat < 2 ^ 32 := UInt32.toNat_lt _
  have hi : (UInt32.ofNat i).toNat = i := UInt32.toNat_ofNat_of_lt' (by unfold UInt32.size; omega)
  have hsub : (n - UInt32.ofNat i).toNat = n.toNat - i := by
    rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le, hi]; omega), hi]
  refine ⟨?_, ?_⟩
  · unfold splitAns
    have hle : (1 : UInt32) ≤ n - UInt32.ofNat i := by
      rw [UInt32.le_iff_toNat_le, hsub]; simp; omega
    rw [if_pos hle]
    have hrest : n - UInt32.ofNat i - 1 = n - UInt32.ofNat (i + 1) := by
      apply UInt32.toNat.inj
      have hi1 : (UInt32.ofNat (i + 1)).toNat = i + 1 := UInt32.toNat_ofNat_of_lt' (by unfold UInt32.size; omega)
      rw [UInt32.toNat_sub_of_le _ _ hle, hsub,
        UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le, hi1]; omega), hi1]
      simp; omega
    simp only [UInt32.toNat_one, hrest, Nat.add_assoc]
  · unfold idxAns
    rw [if_pos (by decide)]
    simp

/-- **An exclusive view ends exactly at its length.** After `n` steps the rest is empty, and its
split answers the end.  `[spec §16]` -/
theorem splitFirst_end (ℓ : Loc) (n : UInt32) :
    splitAns (ℓ + n.toNat) (n - UInt32.ofNat n.toNat) 1 = Val.inj₂ (Val.arr (ℓ + n.toNat) 0) := by
  have hz : n - UInt32.ofNat n.toNat = 0 := by simp
  rw [hz]
  unfold splitAns
  rw [if_neg (by decide)]

end BoCa
