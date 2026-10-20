import Frontend.Check.TDerives
import Support.Dynamics.Completeness

/-!
# Frontend — Check — what the marked derived nodes carry  `[spec §3, §16, §39]`

A marked derived node (`TExpr.divLit`, `walk`, `selfCall`, `lendCell`) is over the typed term of
the value the elaborator marks, and its typed rule says the term's erasure is the scheme's
(`divLitB`, `walkB`, `selfCallB`, `lendCellB`). Two carry a fact about the run beside it:

* **A division by a safe literal cannot fail** (`divLit_some32`, `divLit_some64`,
  `divLit_some8`): at a host that conforms (`Host.Conforms`), the operation at every dividend
  and the literal the node records answers a quotient, so the scheme's error arm is never taken.
* **A counted walk reads below its view's length** (`walk_index_lt`, `walk_fold_index_lt`,
  `walk_get_leaf`, `walk_split_first`): `count_try` and `count_fold` run their step at an index
  only when the index is below the bound (`countTryNext`, `countNext`), the bound is the view's length (`arrLen n ≤ n`), and below it the shared
  view's `idx` answers its leaf and the exclusive view's split its first leaf, so the `inr` arms
  of the step's `array_get`/`slice_split_mut` are never taken. That the step reads the view the
  bound was taken from is the scheme's (`Frontend.Sugar.forData` threads it in the loop's state);
  it is recorded in `Frontend/Check/TFacts.lean`.

One rule node carries a fact the new backend reads (SPEC §44): a `Λ` whose body erases to a λ-value
is instantiated by one β to that λ-value (`allI_inst`), so the backend compiles the `Λ` as its body
and an instantiation as its operand.
-/

namespace BoCa.Fig16.LogRel.Core.Check
open BoCa

/-- The bound of a view is at most its length. -/
theorem arrLen_le (n : UInt32) : arrLen n ≤ n := by
  unfold arrLen
  split
  · exact UInt32.le_refl n
  · exact UInt32.zero_le

/-- **A step of a counted walk runs below the bound**: `count_try (f, (n, (i, s)))` applies `f` at
`i` exactly when `i < len(n)`, and otherwise answers its state. -/
theorem walk_index_lt (f : Val) (n i : UInt32) (s : Val) (h : ¬ i < arrLen n) :
    BoCa.countTryNext f n i s = .val (.inj₁ s) := by
  unfold BoCa.countTryNext
  rw [if_neg h]

/-- **A step of a counted walk with no exit runs below the bound**: `count_fold (f, (n, (i, s)))`
applies `f` at `i` exactly when `i < len(n)`, and otherwise answers its state. -/
theorem walk_fold_index_lt (f : Val) (n i : UInt32) (s : Val) (h : ¬ i < arrLen n) :
    BoCa.countNext f n i s = .val s := by
  unfold BoCa.countNext
  rw [if_neg h]

/-- **A shared view's element below the bound is its leaf.** -/
theorem walk_get_leaf (ℓ : Loc) {n i : UInt32} (h : i < arrLen n) :
    idxAns ℓ n i = .inj₁ (.loc (ℓ + i.toNat)) :=
  idxAns_lt ℓ (UInt32.lt_of_lt_of_le h (arrLen_le n))

/-- **An exclusive view's first leaf below its length**: `splitFirst_lt`. -/
theorem walk_split_first (ℓ : Loc) {n : UInt32} {i : Nat} (h : i < n.toNat) :
    splitAns (ℓ + i) (n - UInt32.ofNat i) 1 =
      .inj₁ (.pair (Val.arr (ℓ + i) 1) (Val.arr (ℓ + (i + 1)) (n - UInt32.ofNat (i + 1)))) ∧
    idxAns (ℓ + i) 1 0 = .inj₁ (.loc (ℓ + i)) :=
  splitFirst_lt ℓ h

theorem prim_div_some {k : Nat} (o : DivOp) (a b : BitVec k) (h0 : b ≠ 0)
    (h1 : o = .div_s → b ≠ BitVec.allOnes k) : (Prim.div o a b).isSome := by
  cases o <;> simp only [Prim.div, if_neg h0]
  · rw [if_neg (fun hh => h1 rfl hh.2)]; rfl
  all_goals rfl

/-- **A safe `i32` divisor**: the division answers at every dividend. -/
theorem divLit_some32 {ℍ : Host} (hc : ℍ.Conforms) {o : DivOp} {n : UInt32}
    (h : safeDivB (.div .w32 o) (.i32 n) = true) (a : UInt32) : (ℍ.div32 o a n).isSome := by
  rw [hc.div32]
  simp only [safeDivB, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.or_eq_true] at h
  simp only [wasmHost, Option.isSome_map]
  refine prim_div_some o _ _ (fun h0 => h.1 ?_) (fun ho hb => ?_)
  · exact UInt32.toBitVec_inj.mp (by simpa using h0)
  · subst ho
    rcases h.2 with h2 | h2
    · simp at h2
    · exact h2 (UInt32.toBitVec_inj.mp (by simpa using hb))

/-- **A safe `i64` divisor**: the division answers at every dividend. -/
theorem divLit_some64 {ℍ : Host} (hc : ℍ.Conforms) {o : DivOp} {n : UInt64}
    (h : safeDivB (.div .w64 o) (.i64 n) = true) (a : UInt64) : (ℍ.div64 o a n).isSome := by
  rw [hc.div64]
  simp only [safeDivB, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.or_eq_true] at h
  simp only [wasmHost, Option.isSome_map]
  refine prim_div_some o _ _ (fun h0 => h.1 ?_) (fun ho hb => ?_)
  · exact UInt64.toBitVec_inj.mp (by simpa using h0)
  · subst ho
    rcases h.2 with h2 | h2
    · simp at h2
    · exact h2 (UInt64.toBitVec_inj.mp (by simpa using hb))

/-- **A safe `u8` divisor**: the unsigned division at `i32`, on the widened operands, answers at
every dividend. -/
theorem divLit_some8 {ℍ : Host} (hc : ℍ.Conforms) {o : DivOp} {n : UInt8}
    (h : safeDivB (.div .w32 o) (.u8 n) = true) (a : UInt32) :
    (ℍ.div32 o a (ℍ.extend8U n)).isSome := by
  rw [hc.div32, hc.extend8U]
  cases o <;> simp only [safeDivB, bne_iff_ne, ne_eq, reduceCtorEq] at h <;>
    simp only [wasmHost, Option.isSome_map] <;>
    refine prim_div_some _ _ _ (fun h0 => h ?_) (fun ho => by cases ho) <;>
    (apply UInt8.toNat_inj.mp; have := congrArg BitVec.toNat h0; simpa using this)

/-! ### Λ erased  `[spec §44]`

A `Λ` erases to `λ_. M` and an instantiation to `M ()` (`TExpr.erase` at `allI`, `allE`,
`allEV`). When `M` erases to a λ-value (`TExpr.isLam`), an instantiation is one β at every memory,
to that λ-value with the binder's slot filled: no code runs, no memory is touched, and the answer
is the body's value. So a `Λ` over such a body is represented by its body, an instantiation by
its operand, and no instantiation is compiled. -/

/-- **An instantiation of a `Λ` whose body is a λ-value is that λ-value**: one β, at every memory,
to the body's erasure with the binder's (dead) slot filled by `()`.  `[spec §44]` -/
theorem allI_inst {ℍ : Host} [HostIs ℍ] {i : TInfo} {j : Jdg} {x : Lifetime.LifeVar} {b : Lifetime.Life} {S : VTy} {C : CTy}
    {t : TExpr} (h : t.isLam = true) :
    ∃ N : Expr, t.erase = .lam N ∧
      PureSteps (ℍ := ℍ) (.app (TExpr.allI i j x b S C t).erase (.val .unit)) (.lam (N.subst 1 Val.unit)) := by
  have hl := TExpr.isLam_eq t
  rw [h] at hl
  match he : t.erase, hl with
  | .lam N, _ =>
    refine ⟨N, rfl, ?_⟩
    have := PureSteps.beta (ℍ := ℍ) (.lam N) Val.unit
    have hu : Val.shift 1 0 Val.unit = Val.unit := rfl
    simpa [TExpr.erase, he, Expr.subst, hu] using this

end BoCa.Fig16.LogRel.Core.Check
