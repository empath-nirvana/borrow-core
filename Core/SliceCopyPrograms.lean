import Core.StepsN
import Core.Fundamental

/-!
# Core — runs of `sliceCopy`  `[spec §74]`

`sliceCopy (dst, (di, (src, (si, len))))` checks its bounds once and, in range, writes
`dst[di + k] := src[si + k]` for every `k < len` in one machine step (`Head.sliceCopy`). The memory
`μ₀` holds a destination of four cells at `0, …, 3`, each `0`, and a source of four cells at
`10, …, 13`, holding `1, 2, 3, 4`.

* `scIn`: `di = 1`, `si = 0`, `len = 2`: cells `1` and `2` become `1` and `2`, the rest are kept,
  and the answer is `(dst, inj₂ ())` (`scIn_run`, `scIn_mem`).
* `scOut`: `di = 3`, `len = 2`, past the destination's end: nothing is written and the answer is
  `(dst, inj₁ ())` (`scOut_run`). `scNeg`: `di = −1`, out of range on mathematical integers, not
  wrapped (`scNeg_run`).
* `scZero`: `len = 0` at `di = si = 4`, the arrays' ends: in range, nothing is written, and the
  answer is `(dst, inj₂ ())` (`scZero_run`).

No surface or elaborator produces `sliceCopy` yet; these are closed core terms.

The constant is typed by its rule (`CDerives.sliceCopyM`) at a persistent element, and so is in
the relation (`sliceCopy_sem`, `fundamentalC`); at a non-persistent element the rule does not
apply (`sliceCopy_not_ref`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.SliceCopyPrograms
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont copyHeap)
open BoCa.Lifetime (LifeCtx)

/-- Cells `0, …, 3` hold `0`; cells `10, …, 13` hold `1, …, 4`. -/
def μ₀ : Heap := fun k =>
  if k < 4 then some (Val.i32 0)
  else if 10 ≤ k ∧ k < 14 then some (Val.i32 (UInt32.ofNat (k - 9)))
  else none

/-- `sliceCopy ((0, 4), (di, ((10, 4), (si, len))))`. -/
def scE (di si len : UInt32) : Expr :=
  .app (.val (.prim .sliceCopy)) (.val (copyArg 0 4 di 10 4 si len))

/-- `sliceCopy` as one head step at the hole. -/
theorem sc_step (di si len : UInt32)
    (h : copyOk 4 di 4 si len = true →
      μ₀.HasRange (0 + di.toNat) len.toNat ∧ μ₀.HasRange (10 + si.toNat) len.toNat) :
    Steps (ℍ := ℍ) μ₀ (scE di si len) (copyHeap μ₀ 0 4 di 10 4 si len)
      (.val (copyAns 0 4 di 4 si len)) :=
  .more ⟨.hole, _, _, rfl, rfl, Head.sliceCopy μ₀ 0 4 di 10 4 si len h⟩ (.refl _ _)

/-- Out of range, the memory is unchanged. -/
theorem copyHeap_out {μ : Heap} {ℓd ℓs : Loc} {nd di ns si len : UInt32}
    (h : copyOk nd di ns si len = false) : copyHeap μ ℓd nd di ℓs ns si len = μ := by
  simp [copyHeap, h]

/-- At `len = 0`, the memory is unchanged. -/
theorem copyHeap_zero {μ : Heap} {ℓd ℓs : Loc} {nd di ns si : UInt32} :
    copyHeap μ ℓd nd di ℓs ns si 0 = μ := by
  unfold copyHeap
  split
  · funext k; simp [Heap.copy]
  · rfl

/-! ### In range -/

/-- `di = 1`, `si = 0`, `len = 2`. -/
def scIn : Expr := scE 1 0 2

/-- **`scIn`** copies in one step and answers `(dst, inj₂ ())`. -/
theorem scIn_run :
    Steps (ℍ := ℍ) μ₀ scIn (copyHeap μ₀ 0 4 1 10 4 0 2)
      (.val (Val.pair (Val.arr 0 4) (Val.inj₂ Val.unit))) := by
  have hok : copyOk 4 1 4 0 2 = true := by decide
  have hans : copyAns 0 4 1 4 0 2 = Val.pair (Val.arr 0 4) (Val.inj₂ Val.unit) := by
    simp [copyAns, hok]
  rw [← hans]
  have h1 : (1 : UInt32).toNat = 1 := rfl
  have h0 : (0 : UInt32).toNat = 0 := rfl
  have h2 : (2 : UInt32).toNat = 2 := rfl
  refine sc_step 1 0 2 fun _ => ⟨fun i hi => ?_, fun i hi => ?_⟩ <;>
    rw [h2] at hi <;> simp only [h0, h1] <;> interval_cases i <;> simp [μ₀]

/-- After `scIn`: cells `1` and `2` hold the source's `1` and `2`; the rest are as before. -/
theorem scIn_mem :
    copyHeap μ₀ 0 4 1 10 4 0 2 0 = some (Val.i32 0) ∧
    copyHeap μ₀ 0 4 1 10 4 0 2 1 = some (Val.i32 1) ∧
    copyHeap μ₀ 0 4 1 10 4 0 2 2 = some (Val.i32 2) ∧
    copyHeap μ₀ 0 4 1 10 4 0 2 3 = some (Val.i32 0) ∧
    (∀ k : Nat, 10 ≤ k → k < 14 → copyHeap μ₀ 0 4 1 10 4 0 2 k = μ₀ k) := by
  have hok : copyOk 4 1 4 0 2 = true := by decide
  have h1 : (1 : UInt32).toNat = 1 := rfl
  have h0 : (0 : UInt32).toNat = 0 := rfl
  have h2 : (2 : UInt32).toNat = 2 := rfl
  simp only [copyHeap, hok, if_true, Heap.copy, h0, h1, h2]
  refine ⟨by simp [μ₀], by simp [μ₀], by simp [μ₀], by simp [μ₀], fun k hk₁ hk₂ => ?_⟩
  split
  · rename_i h; have h₂ : k < 3 := h.2; omega
  · rfl

/-! ### Out of range -/

/-- `di = 3`, `si = 0`, `len = 2`: `di + len` is past the destination's length `4`. -/
def scOut : Expr := scE 3 0 2

/-- **`scOut`** writes nothing and answers `(dst, inj₁ ())`. -/
theorem scOut_run :
    Steps (ℍ := ℍ) μ₀ scOut μ₀ (.val (Val.pair (Val.arr 0 4) (Val.inj₁ Val.unit))) := by
  have hok : copyOk 4 3 4 0 2 = false := by decide
  have h := sc_step (ℍ := ℍ) 3 0 2 (fun h => absurd h (by simp [hok]))
  rwa [copyHeap_out hok, show copyAns 0 4 3 4 0 2 = Val.pair (Val.arr 0 4) (Val.inj₁ Val.unit) by simp [copyAns, hok]] at h

/-- `di = −1` (`0xFFFFFFFF`), `si = 0`, `len = 1`: negative, so out of range, though
`di + len` wraps to `0` in `i32`. -/
def scNeg : Expr := scE 0xFFFFFFFF 0 1

/-- **`scNeg`** writes nothing and answers `(dst, inj₁ ())`. -/
theorem scNeg_run :
    Steps (ℍ := ℍ) μ₀ scNeg μ₀ (.val (Val.pair (Val.arr 0 4) (Val.inj₁ Val.unit))) := by
  have hok : copyOk 4 0xFFFFFFFF 4 0 1 = false := by decide
  have h := sc_step (ℍ := ℍ) 0xFFFFFFFF 0 1 (fun h => absurd h (by simp [hok]))
  rwa [copyHeap_out hok, show copyAns 0 4 0xFFFFFFFF 4 0 1 = Val.pair (Val.arr 0 4) (Val.inj₁ Val.unit) by simp [copyAns, hok]] at h

/-! ### An empty range -/

/-- `di = si = 4`, `len = 0`: the empty range at both arrays' ends. -/
def scZero : Expr := scE 4 4 0

/-- **`scZero`** is in range, writes nothing, and answers `(dst, inj₂ ())`. -/
theorem scZero_run :
    Steps (ℍ := ℍ) μ₀ scZero μ₀ (.val (Val.pair (Val.arr 0 4) (Val.inj₂ Val.unit))) := by
  have hok : copyOk 4 4 4 4 0 = true := by decide
  have h := sc_step (ℍ := ℍ) 4 4 0 (fun _ => ⟨fun i hi => absurd hi (by simp),
    fun i hi => absurd hi (by simp)⟩)
  rwa [copyHeap_zero, show copyAns 0 4 4 4 4 0 = Val.pair (Val.arr 0 4) (Val.inj₂ Val.unit) by simp [copyAns, hok]] at h

/-! ### The rule -/

/-- `slice_copy_mut` at `I32`, typed by its rule at the empty context. -/
theorem sliceCopy_der (a b : Lifetime.Life) :
    CDerives LifeCtx.empty [] (.val sliceCopyV) (.val (sliceCopyMTy a b (.int .w32))) :=
  .sliceCopyM a b _ .nil rfl

/-- **`slice_copy_mut` at `I32` is in the relation**: `fundamentalC` at its derivation. -/
theorem sliceCopy_sem (a b : Lifetime.Life) :
    SemJ (ℍ := ℍ) LifeCtx.empty [] (.val sliceCopyV) (.val (sliceCopyMTy a b (.int .w32))) :=
  fundamentalC (sliceCopy_der a b)

/-- The rule's premise fails at `Ref I32`: a copy of an owned element would duplicate its cell. -/
theorem sliceCopy_not_ref : ¬ (VTy.ref (.int .w32)).Persistent := by
  simp [VTy.Persistent, VTy.persistent]

end BoCa.Fig16.LogRel.Core.SliceCopyPrograms

end
