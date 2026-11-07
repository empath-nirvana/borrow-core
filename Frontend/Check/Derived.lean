import Frontend.Check.TDerives
import Frontend.Check.Pin
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

Two rule nodes carry a fact the new backend reads:

* **A `Λ` over a value form** (SPEC §44, §63): a `Λ` whose body erases to a value form in which the
  binder's dead slot does not occur (`valFormB`) is instantiated by one β to that value form
  (`allI_inst`), so the backend compiles the `Λ` as its body and an instantiation as its operand.
* **`[lend-R]` at the empty row** (SPEC §63): with no operation in the callback's row, the
  unwinding frame never runs its finaliser, and the relaxed lend is the plain lend: the callback on
  the owner, its answer paired with the owner (`lendR_plain`).
-/

namespace BoCa.Fig16.LogRel.Core.Check
open BoCa
open BoCa.Fig16 BoCa.Fig16.BoLo
open BoCa.BoLo (Head Kont Step1N)
open Frontend.Check (valFormB lendRE)

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

/-! ### Λ erased  `[spec §44, §63]`

A `Λ` erases to `λ_. M` and an instantiation to `M ()` (`TExpr.erase` at `allI`, `allE`,
`allEV`). `[∀I]` checks `M` with the binder's slot dead (`TDerives.allI`: `⟨S, false⟩ :: Γ`).
When `M` erases to a value form whose variables are live slots, the binder's slot not among them
(`valFormB (false :: u)`; a λ-value is one whatever it mentions), an instantiation is one β at
every memory, to that value form with the binder's slot filled: no code runs, no memory is
touched, and the answer is the body's value. So a `Λ` over such a body is represented by its body,
an instantiation by its operand, and no instantiation is compiled. -/

/-- Filling a slot no variable of a value form names leaves a value form over the other slots. -/
theorem valFormB_subst_dead : ∀ {u : List Bool} {e : Expr},
    valFormB (false :: u) e = true → valFormB u (e.subst 0 Val.unit) = true
  | _, .var 0, h => by simp [valFormB] at h
  | u, .var (k + 1), h => by
      simpa [valFormB, Expr.subst] using h
  | _, .unit, _ | _, .lam _, _ | _, .loc _, _ | _, .prim _, _ => by simp [valFormB, Expr.subst]
  | _, .pair a b, h => by
      simp only [valFormB, Bool.and_eq_true] at h
      simp only [Expr.subst, valFormB, Bool.and_eq_true]
      exact ⟨valFormB_subst_dead h.1, valFormB_subst_dead h.2⟩
  | _, .inj₁ a, h => by
      simp only [valFormB] at h; simpa [Expr.subst, valFormB] using valFormB_subst_dead h
  | _, .inj₂ a, h => by
      simp only [valFormB] at h; simpa [Expr.subst, valFormB] using valFormB_subst_dead h
  | _, .app _ _, h | _, .letpair _ _, h | _, .seq _ _, h | _, .case _ _ _, h => by
      simp [valFormB] at h

/-- **An instantiation of a `Λ` whose body is a value form is that value form**: one β, at every
memory, to the body's erasure with the binder's (dead) slot filled by `()`, and the result is a
value form over the live slots `u`.  `[spec §44, §63]` -/
theorem allI_inst {ℍ : Host} [HostIs ℍ] {i : TInfo} {j : Jdg} {x : Lifetime.LifeVar} {b : Lifetime.Life} {S : VTy} {C : CTy}
    {t : TExpr} {u : List Bool} (h : valFormB (false :: u) t.erase = true) :
    PureSteps (ℍ := ℍ) (.app (TExpr.allI i j x b S C t).erase (.val .unit))
        (t.erase.subst 0 Val.unit) ∧
      valFormB u (t.erase.subst 0 Val.unit) = true :=
  ⟨PureSteps.beta (ℍ := ℍ) t.erase Val.unit, valFormB_subst_dead h⟩

/-! ### `[lend-R]` at the empty row  `[spec §63]`

R1's term at the owner `u` is `withborU d u (Λ. λm. M)` (`lendRE`): the callback
under the unwinding frame, whose finaliser `d` runs on the owner only when the callback stops at an
operation (`ewp_unwind`). At a row with no operation the table has no entry, so the callback never
stops: every end of its run is a return, where the frame pairs the owner with the answer
(`ewp_ret_pair`). So the relaxed lend is the plain lend, whatever `d` is. -/

/-- The empty row's table has no entry. -/
theorem rowTab_isEmpty {ℍ : Host} [HostIs ℍ] {S : Row} (hS : S.isEmpty = true) (δ : Lifetime.LSub) (n i : UInt32) :
    Row.tab (ℍ := ℍ) S δ n i = none := by
  cases S with
  | nil => rfl
  | cons _ _ => simp at hS

/-- **`[lend-R]` at the empty row is the plain lend**: at a row with no operation, R1's term at a
closed owner `u` (`lendRE d M`, its variable `0` filled by `u`) runs as the callback
`lendCb M` on `()` and `u`, its answer `w` paired with the owner: `(u, w)`. The finaliser `d`
never runs.  `[spec §63]` -/
theorem lendR_plain {ℍ : Host} [HostIs ℍ] {S : Row} (hS : S.isEmpty = true) (δ : Lifetime.LSub)
    {d M : Expr} (hd : closedAt 0 d = true) (hcb : closedAt 0 (lendCb M).1 = true)
    (u : Val) (hu : closedAt 0 u.1 = true) {ls : List SRec} {Q : List SRec → Val → WProp}
    {ρ : WRes}
    (h : ewpTS (ℍ := ℍ) ls (.app (.app (.val (lendCb M)) (.val .unit)) (.val u))
      (opTable (Row.tab S δ)) (fun ls w => Q ls (Val.pair u w)) ρ) :
    ewpTS (ℍ := ℍ) ls ((lendRE d M).subst 0 u) (opTable (Row.tab S δ)) Q ρ := by
  have hE := rowTab_isEmpty (ℍ := ℍ) hS δ
  have hTb := opTable_mono (Row.tab S δ)
  have hA : (Row.tab S δ).AbortOnly := fun n i en h => by rw [hE n i] at h; cases h
  have e : (lendRE d M).subst 0 u =
      .app (.app (.val (withborUV d)) (.val u)) (.val (lendCb M)) := by
    simp only [lendRE, Expr.subst, if_true]
    rw [show Expr.val (withborUV d) = withborUE d from rfl,
      subst_closedAt _ _ (withborUE_closed hd) (Nat.zero_le _),
      show Expr.val (lendCb M) = (lendCb M).1 from rfl,
      subst_closedAt _ _ hcb (Nat.zero_le _)]
  rw [e]
  refine withborUE_beta hTb hd u hu (lendCb M) ?_
  refine ewp_fold hTb (wpG_bind (ubindK _ _) _ ls _ ρ ?_)
  refine wpG_mono (fun ls' t σ ht => ?_) ((ewp_abortive (opTable_abortive hA)).mp h)
  rcases ht with ⟨v, rfl, hv⟩ | hp
  · exact ewp_unfold hTb (ewp_ret_pair hTb u hu _ v hv)
  rcases hp with ⟨K₁, n, i, v, en, hp⟩ | ⟨K₁, n, i, v, en, hp⟩
  · obtain ⟨⟨-, -, hT, -⟩, -⟩ := pure_sep_iff.mp hp
    rw [hE n i] at hT; cases hT
  · obtain ⟨⟨-, -, hT, -⟩, -⟩ := pure_sep_iff.mp hp
    rw [hE n i] at hT; cases hT

/-! ### Codata's η-thunk  `[spec §45, §65]`

A thunk that observes codata by η-expansion is the erasure of an η-tree over `f` and `s`
(`NuTree.toE`, `nuEtaB`): `&`s of the projections, `λ`s and `Λ`s, every leaf the observation of
`f s` along its path. Filling its variables with values (`NuTree.toE_subst`) gives the tree over
the values. Every observation of the thunk that reaches a subtree reaches, by pure steps, that
subtree's erasure over the observation made (`nuEta_reach`): a `&` or a `λ`, a value, with no step
that touches memory; at a leaf, the same observation of `f s` (`nuEta_obs`). When `f` is
`unfold step` (`hN`, the value `unfold step` steps to), `f s` is itself one β at every memory to
the codata `etaN C g s` (`hN_steps`), so the thunk's every observation reaches the same
observation of that value (`nuEta_unfold`): the value may be computed where the thunk is built.
With no state, the thunk's observations are `f`'s (`nuEta_var`). -/

/-- `⟨M, N⟩` observed at `inj₁ ()` is `M`, at `inj₂ ()` `N`, for closed `M`, `N`. -/
theorem withPair_obs {ℍ : Host} [HostIs ℍ] {M N : Expr} (hM : closedAt 0 M = true)
    (hN : closedAt 0 N = true) (k : Bool) :
    PureSteps (ℍ := ℍ) (.app (withPair M N) (.val (if k then .inj₂ .unit else .inj₁ .unit)))
      (if k then N else M) := by
  refine (PureSteps.beta _ _).trans ?_
  have eM : M.subst 1 (Val.shift 1 0 (if k then Val.inj₂ Val.unit else Val.inj₁ Val.unit)) = M :=
    subst_closedAt M _ hM (Nat.zero_le _)
  have eN : N.subst 1 (Val.shift 1 0 (if k then Val.inj₂ Val.unit else Val.inj₁ Val.unit)) = N :=
    subst_closedAt N _ hN (Nat.zero_le _)
  cases k
  · simp only [Expr.subst] at eM eN ⊢
    rw [eM, eN]
    refine (PureSteps.head (fun μ => BoCa.BoLo.Head.case₁ μ Val.unit _ _) rfl).trans ?_
    simp only [Expr.subst]
    rw [subst_closedAt M _ hM (Nat.zero_le _)]
    exact PureSteps.head (fun μ => BoCa.BoLo.Head.seq μ _) rfl
  · simp only [Expr.subst] at eM eN ⊢
    rw [eM, eN]
    refine (PureSteps.head (fun μ => BoCa.BoLo.Head.case₂ μ Val.unit _ _) rfl).trans ?_
    simp only [Expr.subst]
    rw [subst_closedAt N _ hN (Nat.zero_le _)]
    exact PureSteps.head (fun μ => BoCa.BoLo.Head.seq μ _) rfl

namespace NuArg

/-- The argument with the variable `j` filled by `v`. -/
def sub (j : Nat) (v : Val) : NuArg → NuArg
  | .var i => if i = j then .val v else if i > j then .var (i - 1) else .var i
  | .val w => .val w

/-- Every variable of the argument is below `k`; a value is closed. -/
def ClosedAt (k : Nat) : NuArg → Prop
  | .var i => i < k
  | .val v => closedAt 0 v.1 = true

theorem toE_subst {a : NuArg} (h : a.Closed) (j : Nat) (v : Val) :
    a.toE.subst j v = (a.sub j v).toE := by
  cases a with
  | var i => simp only [toE, sub, Expr.subst]; split_ifs <;> rfl
  | val w => exact closed_subst h j v

theorem sub_up (a : NuArg) (n j : Nat) (v : Val) : (a.up n).sub (j + n) v = (a.sub j v).up n := by
  cases a with
  | var i =>
    simp only [up, sub]
    by_cases h₁ : i = j
    · subst h₁; simp
    · by_cases h₂ : i > j
      · rw [if_neg (by omega), if_pos (by omega), if_neg h₁, if_pos h₂]
        show NuArg.var _ = NuArg.var _; congr 1; omega
      · rw [if_neg (by omega), if_neg (by omega), if_neg h₁, if_neg h₂]
  | val w => rfl

theorem sub_closed {a : NuArg} (h : a.Closed) (j : Nat) {v : Val} (hv : closedAt 0 v.1 = true) :
    (a.sub j v).Closed := by
  cases a with
  | var i => simp only [sub]; split_ifs <;> first | exact hv | trivial
  | val w => exact h

theorem sub_val (w : Val) (j : Nat) (v : Val) : (NuArg.val w).sub j v = .val w := rfl

theorem up_val (w : Val) (n : Nat) : (NuArg.val w).up n = .val w := rfl

theorem map_up_sub (xs : List NuArg) (n j : Nat) (v : Val) :
    (xs.map (·.up n)).map (·.sub (j + n) v) = (xs.map (·.sub j v)).map (·.up n) := by
  induction xs with
  | nil => rfl
  | cons a as ih => simp only [List.map_cons, ih, sub_up]

theorem omap_up_sub (s : Option NuArg) (n j : Nat) (v : Val) :
    (s.map (·.up n)).map (·.sub (j + n) v) = (s.map (·.sub j v)).map (·.up n) := by
  cases s <;> simp only [Option.map_none, Option.map_some, sub_up]

theorem map_val_up (xs : List Val) (n : Nat) : (xs.map NuArg.val).map (·.up n) = xs.map .val := by
  induction xs with
  | nil => rfl
  | cons a as ih => simp only [List.map_cons, ih, up_val]

theorem omap_val_up (s : Option Val) (n : Nat) : (s.map NuArg.val).map (·.up n) = s.map .val := by
  cases s <;> rfl

theorem map_val_sub (xs : List Val) (j : Nat) (v : Val) :
    (xs.map NuArg.val).map (·.sub j v) = xs.map .val := by
  induction xs with
  | nil => rfl
  | cons a as ih => simp only [List.map_cons, ih, sub_val]

theorem omap_val_sub (s : Option Val) (j : Nat) (v : Val) :
    (s.map NuArg.val).map (·.sub j v) = s.map .val := by
  cases s <;> rfl

theorem closedAt_toE {a : NuArg} {k : Nat} (h : a.ClosedAt k) : closedAt k a.toE = true := by
  cases a with
  | var i => have : i < k := h; simp [toE, closedAt, this]
  | val w => exact closedAt_mono _ h (Nat.zero_le _)

theorem up_closedAt {a : NuArg} {k : Nat} (h : a.ClosedAt k) (n : Nat) : (a.up n).ClosedAt (k + n) := by
  cases a with
  | var i => show i + n < k + n; have : i < k := h; omega
  | val w => exact h

end NuArg

theorem nuAppsE_subst (h : Expr) : ∀ (os : List NuArg), (∀ a ∈ os, a.Closed) → ∀ (j : Nat) (v : Val),
    (nuAppsE h os).subst j v = nuAppsE (h.subst j v) (os.map (·.sub j v))
  | [], _, _, _ => rfl
  | a :: as, hos, j, v => by
      simp only [nuAppsE, List.map_cons]
      rw [nuAppsE_subst _ as (fun x hx => hos x (List.mem_cons_of_mem _ hx))]
      simp only [Expr.subst, NuArg.toE_subst (hos a (List.mem_cons_self ..))]

theorem nuHeadE_subst {f : NuArg} {s : Option NuArg} (hf : f.Closed) (hs : ∀ a ∈ s, a.Closed)
    (j : Nat) (v : Val) : (nuHeadE f s).subst j v = nuHeadE (f.sub j v) (s.map (·.sub j v)) := by
  cases s with
  | none => exact NuArg.toE_subst hf j v
  | some a =>
    simp only [nuHeadE, Expr.subst, Option.map_some, NuArg.toE_subst hf,
      NuArg.toE_subst (hs a rfl)]

theorem val_shift_closed {v : Val} (hv : closedAt 0 v.1 = true) (n c : Nat) : v.shift n c = v :=
  Val.ext (closed_shift hv n c)

theorem withPair_subst2 (M N : Expr) {v : Val} (hv : closedAt 0 v.1 = true) (j : Nat) :
    (withPair M N).subst j v = withPair (M.subst (j + 2) v) (N.subst (j + 2) v) := by
  simp [withPair, Expr.subst, val_shift_closed hv]

theorem lam_subst (b : Expr) {v : Val} (hv : closedAt 0 v.1 = true) (j : Nat) :
    (Expr.val (.lam b)).subst j v = .val (.lam (b.subst (j + 1) v)) := by
  simp [Expr.subst, val_shift_closed hv]

/-- **Filling a variable of an η-tree's erasure** fills it in the tree's arguments. -/
theorem NuTree.toE_subst : ∀ (t : NuTree) (f : NuArg) (s : Option NuArg) (os : List NuArg),
    f.Closed → (∀ a ∈ s, a.Closed) → (∀ a ∈ os, a.Closed) → ∀ (j : Nat) {v : Val},
    closedAt 0 v.1 = true →
    (t.toE f s os).subst j v = t.toE (f.sub j v) (s.map (·.sub j v)) (os.map (·.sub j v))
  | .leaf false, f, s, os, hf, hs, hos, j, v, _ => by
      simp only [NuTree.toE]
      rw [nuAppsE_subst _ os hos, nuHeadE_subst hf hs]
  | .leaf true, f, s, os, hf, hs, hos, j, v, hv => by
      have hos' : ∀ a ∈ os.map (·.up 1), a.Closed := by
        intro a ha; simp only [List.mem_map] at ha
        obtain ⟨b, hb, rfl⟩ := ha; exact NuArg.up_closed (hos b hb) 1
      simp only [NuTree.toE]
      rw [Expr.subst, lam_subst _ hv, nuAppsE_subst _ _ hos',
        nuHeadE_subst (NuArg.var_closed 0) (NuArg.omap_up_closed hs 1), NuArg.toE_subst hf,
        NuArg.map_up_sub, NuArg.omap_up_sub]
      rfl
  | .amp l r, f, s, os, hf, hs, hos, j, v, hv => by
      simp only [NuTree.toE]
      rw [withPair_subst2 _ _ hv,
        NuTree.toE_subst l _ _ _ (NuArg.up_closed hf 2) (NuArg.omap_up_closed hs 2)
          (NuArg.map_up_closed hos 2 _ (NuArg.val_closed rfl)) _ hv,
        NuTree.toE_subst r _ _ _ (NuArg.up_closed hf 2) (NuArg.omap_up_closed hs 2)
          (NuArg.map_up_closed hos 2 _ (NuArg.val_closed rfl)) _ hv]
      simp only [List.map_append, List.map_cons, List.map_nil, NuArg.sub_val, NuArg.sub_up,
        NuArg.map_up_sub, NuArg.omap_up_sub]
  | .lam t, f, s, os, hf, hs, hos, j, v, hv => by
      simp only [NuTree.toE]
      rw [lam_subst _ hv, NuTree.toE_subst t _ _ _ (NuArg.up_closed hf 1)
        (NuArg.omap_up_closed hs 1) (NuArg.map_up_closed hos 1 _ (NuArg.var_closed 0)) _ hv]
      have e0 : (NuArg.var 0).sub (j + 1) v = .var 0 := by
        simp only [NuArg.sub]; rw [if_neg (by omega), if_neg (by omega)]
      simp only [List.map_append, List.map_cons, List.map_nil, e0, NuArg.sub_up,
        NuArg.map_up_sub, NuArg.omap_up_sub]
  | .dead t, f, s, os, hf, hs, hos, j, v, hv => by
      simp only [NuTree.toE]
      rw [lam_subst _ hv, NuTree.toE_subst t _ _ _ (NuArg.up_closed hf 1)
        (NuArg.omap_up_closed hs 1) (NuArg.map_up_closed hos 1 _ (NuArg.val_closed rfl)) _ hv]
      simp only [List.map_append, List.map_cons, List.map_nil, NuArg.sub_val, NuArg.sub_up,
        NuArg.map_up_sub, NuArg.omap_up_sub]

theorem nuAppsE_closedAt {k : Nat} : ∀ {h : Expr} (os : List NuArg), closedAt k h = true →
    (∀ a ∈ os, a.ClosedAt k) → closedAt k (nuAppsE h os) = true
  | _, [], hh, _ => hh
  | _, a :: as, hh, hos =>
      nuAppsE_closedAt as (by simp [closedAt, hh, NuArg.closedAt_toE (hos a (List.mem_cons_self ..))])
        (fun x hx => hos x (List.mem_cons_of_mem _ hx))

theorem nuHeadE_closedAt {k : Nat} {f : NuArg} {s : Option NuArg} (hf : f.ClosedAt k)
    (hs : ∀ a ∈ s, a.ClosedAt k) : closedAt k (nuHeadE f s) = true := by
  cases s with
  | none => exact NuArg.closedAt_toE hf
  | some a => simp [nuHeadE, closedAt, NuArg.closedAt_toE hf, NuArg.closedAt_toE (hs a rfl)]

theorem omap_up_closedAt {k : Nat} {s : Option NuArg} (hs : ∀ a ∈ s, a.ClosedAt k) (n : Nat) :
    ∀ a ∈ s.map (·.up n), a.ClosedAt (k + n) := by
  intro a ha
  cases s with
  | none => cases ha
  | some b => cases ha; exact NuArg.up_closedAt (hs b rfl) n

theorem map_up_closedAt {k : Nat} {os : List NuArg} (hos : ∀ a ∈ os, a.ClosedAt k) (n : Nat)
    (extra : List NuArg) (he : ∀ a ∈ extra, a.ClosedAt (k + n)) :
    ∀ a ∈ os.map (·.up n) ++ extra, a.ClosedAt (k + n) := by
  intro a ha
  simp only [List.mem_append, List.mem_map] at ha
  rcases ha with ⟨b, hb, rfl⟩ | ha
  · exact NuArg.up_closedAt (hos b hb) n
  · exact he a ha

/-- An η-tree's erasure over arguments below `k` is closed below `k`. -/
theorem NuTree.toE_closedAt : ∀ (t : NuTree) {k : Nat} {f : NuArg} {s : Option NuArg}
    {os : List NuArg}, f.ClosedAt k → (∀ a ∈ s, a.ClosedAt k) → (∀ a ∈ os, a.ClosedAt k) →
    closedAt k (t.toE f s os) = true
  | .leaf false, _, _, _, _, hf, hs, hos => nuAppsE_closedAt _ (nuHeadE_closedAt hf hs) hos
  | .leaf true, k, f, s, os, hf, hs, hos => by
      simp only [NuTree.toE, closedAt, Val.val_lam, Bool.and_eq_true]
      refine ⟨nuAppsE_closedAt _ (nuHeadE_closedAt (show 0 < k + 1 by omega)
        (omap_up_closedAt hs 1)) (by simpa using map_up_closedAt hos 1 [] (by simp)),
        NuArg.closedAt_toE hf⟩
  | .amp l r, k, f, s, os, hf, hs, hos => by
      simp only [NuTree.toE, withPair, closedAt, Val.val_lam, Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨⟨by omega, by omega, ?_⟩, by omega, ?_⟩
      · exact NuTree.toE_closedAt l (NuArg.up_closedAt hf 2) (omap_up_closedAt hs 2)
          (map_up_closedAt hos 2 _ (by simp [NuArg.ClosedAt]; rfl))
      · exact NuTree.toE_closedAt r (NuArg.up_closedAt hf 2) (omap_up_closedAt hs 2)
          (map_up_closedAt hos 2 _ (by simp [NuArg.ClosedAt]; rfl))
  | .lam t, k, f, s, os, hf, hs, hos => by
      simp only [NuTree.toE, closedAt, Val.val_lam]
      exact NuTree.toE_closedAt t (NuArg.up_closedAt hf 1) (omap_up_closedAt hs 1)
        (map_up_closedAt hos 1 _ (by simp [NuArg.ClosedAt]))
  | .dead t, k, f, s, os, hf, hs, hos => by
      simp only [NuTree.toE, closedAt, Val.val_lam]
      exact NuTree.toE_closedAt t (NuArg.up_closedAt hf 1) (omap_up_closedAt hs 1)
        (map_up_closedAt hos 1 _ (by simp [NuArg.ClosedAt]; rfl))

/-- An observation `ps` of an η-tree from `t` reaches its subtree `t'`: a projection at an `amp`,
any value at a `lam`, `()` at a `dead`. -/
inductive NuTree.Reach : NuTree → List Val → NuTree → Prop
  | refl (t : NuTree) : NuTree.Reach t [] t
  | inl {l r t : NuTree} {ps : List Val} :
      NuTree.Reach l ps t → NuTree.Reach (.amp l r) (.inj₁ .unit :: ps) t
  | inr {l r t : NuTree} {ps : List Val} :
      NuTree.Reach r ps t → NuTree.Reach (.amp l r) (.inj₂ .unit :: ps) t
  | lam {u t : NuTree} {ps : List Val} (v : Val) :
      NuTree.Reach u ps t → NuTree.Reach (.lam u) (v :: ps) t
  | dead {u t : NuTree} {ps : List Val} :
      NuTree.Reach u ps t → NuTree.Reach (.dead u) (.unit :: ps) t

/-- The observations `ps` made on `a` reduce as `a` does. -/
theorem nuAppsE_steps {ℍ : Host} [HostIs ℍ] : ∀ (ps : List Val) {a b : Expr},
    PureSteps (ℍ := ℍ) a b → PureSteps (ℍ := ℍ) (nuAppsE a (ps.map .val)) (nuAppsE b (ps.map .val))
  | [], _, _, h => h
  | v :: ps, _, _, h => nuAppsE_steps ps (PureSteps.plug (.appL .hole v) h)

theorem nuAppsE_append (h : Expr) : ∀ (xs ys : List NuArg),
    nuAppsE h (xs ++ ys) = nuAppsE (nuAppsE h xs) ys
  | [], _ => rfl
  | _ :: xs, ys => nuAppsE_append _ xs ys

theorem vals_closed {xs : List Val} (h : ∀ v ∈ xs, closedAt 0 v.1 = true) :
    ∀ a ∈ xs.map NuArg.val, a.Closed := by
  intro a ha; simp only [List.mem_map] at ha; obtain ⟨v, hv, rfl⟩ := ha; exact h v hv

theorem vals_closedAt {xs : List Val} (h : ∀ v ∈ xs, closedAt 0 v.1 = true) (k : Nat) :
    ∀ a ∈ xs.map NuArg.val, a.ClosedAt k := by
  intro a ha; simp only [List.mem_map] at ha; obtain ⟨v, hv, rfl⟩ := ha; exact h v hv

theorem oval_closed {s : Option Val} (h : ∀ v ∈ s, closedAt 0 v.1 = true) :
    ∀ a ∈ s.map NuArg.val, a.Closed := by
  intro a ha; cases s with
  | none => cases ha
  | some v => cases ha; exact h v rfl

theorem oval_closedAt {s : Option Val} (h : ∀ v ∈ s, closedAt 0 v.1 = true) (k : Nat) :
    ∀ a ∈ s.map NuArg.val, a.ClosedAt k := by
  intro a ha; cases s with
  | none => cases ha
  | some v => cases ha; exact h v rfl

theorem vals_app_closed {os : List Val} (hos : ∀ v ∈ os, closedAt 0 v.1 = true) {x : NuArg}
    (hx : x.Closed) : ∀ a ∈ os.map NuArg.val ++ [x], a.Closed := by
  intro a ha
  rcases List.mem_append.1 ha with h | h
  · exact vals_closed hos a h
  · rw [List.mem_singleton.1 h]; exact hx

theorem app_closed {os : List Val} (hos : ∀ v ∈ os, closedAt 0 v.1 = true) {x : Val}
    (hx : closedAt 0 x.1 = true) : ∀ v ∈ os ++ [x], closedAt 0 v.1 = true := by
  intro v hv
  rcases List.mem_append.1 hv with h | h
  · exact hos v h
  · rw [List.mem_singleton.1 h]; exact hx

/-- **An observation of the η-thunk reaches the subtree it reaches**: by pure steps, the
subtree's erasure over the observation made.  `[spec §45, §65]` -/
theorem nuEta_reach {ℍ : Host} [HostIs ℍ] {fv : Val} {sv : Option Val}
    (hf : closedAt 0 fv.1 = true) (hs : ∀ v ∈ sv, closedAt 0 v.1 = true) :
    ∀ {t ps t'}, NuTree.Reach t ps t' → ∀ (os : List Val), (∀ v ∈ os, closedAt 0 v.1 = true) →
      (∀ v ∈ ps, closedAt 0 v.1 = true) →
      PureSteps (ℍ := ℍ) (nuAppsE (t.toE (.val fv) (sv.map .val) (os.map .val)) (ps.map .val))
        (t'.toE (.val fv) (sv.map .val) ((os ++ ps).map .val))
  | _, _, _, .refl t, os, _, _ => by
      simp only [nuAppsE, List.map_nil, List.append_nil]; exact .refl
  | _, _, _, .inl (l := l) (r := r) (ps := ps) h, os, hos, hps => by
      have hM := NuTree.toE_closedAt l (k := 0) (f := .val fv) (s := sv.map .val)
        (os := (os ++ [Val.inj₁ Val.unit]).map .val) hf (oval_closedAt hs 0)
        (vals_closedAt (app_closed hos rfl) 0)
      have hN := NuTree.toE_closedAt r (k := 0) (f := .val fv) (s := sv.map .val)
        (os := (os ++ [Val.inj₂ Val.unit]).map .val) hf (oval_closedAt hs 0)
        (vals_closedAt (app_closed hos rfl) 0)
      have hw := withPair_obs (ℍ := ℍ) hM hN false
      simp only [Bool.false_eq_true, if_false] at hw
      have ih := nuEta_reach hf hs h (os ++ [Val.inj₁ Val.unit]) (app_closed hos rfl)
        (fun v hv => hps v (List.mem_cons_of_mem _ hv))
      simp only [List.append_assoc, List.singleton_append] at ih
      refine PureSteps.trans ?_ ih
      simp only [NuTree.toE, NuArg.up_val, NuArg.omap_val_up, NuArg.map_val_up, List.map_cons,
        nuAppsE, NuArg.toE]
      have := nuAppsE_steps (ℍ := ℍ) ps hw
      simpa [List.map_append] using this
  | _, _, _, .inr (l := l) (r := r) (ps := ps) h, os, hos, hps => by
      have hM := NuTree.toE_closedAt l (k := 0) (f := .val fv) (s := sv.map .val)
        (os := (os ++ [Val.inj₁ Val.unit]).map .val) hf (oval_closedAt hs 0)
        (vals_closedAt (app_closed hos rfl) 0)
      have hN := NuTree.toE_closedAt r (k := 0) (f := .val fv) (s := sv.map .val)
        (os := (os ++ [Val.inj₂ Val.unit]).map .val) hf (oval_closedAt hs 0)
        (vals_closedAt (app_closed hos rfl) 0)
      have hw := withPair_obs (ℍ := ℍ) hM hN true
      simp only [if_true] at hw
      have ih := nuEta_reach hf hs h (os ++ [Val.inj₂ Val.unit]) (app_closed hos rfl)
        (fun v hv => hps v (List.mem_cons_of_mem _ hv))
      simp only [List.append_assoc, List.singleton_append] at ih
      refine PureSteps.trans ?_ ih
      simp only [NuTree.toE, NuArg.up_val, NuArg.omap_val_up, NuArg.map_val_up, List.map_cons,
        nuAppsE, NuArg.toE]
      have := nuAppsE_steps (ℍ := ℍ) ps hw
      simpa [List.map_append] using this
  | _, _, _, .lam (u := u) (ps := ps) v h, os, hos, hps => by
      have hv : closedAt 0 v.1 = true := hps v (List.mem_cons_self ..)
      have ih := nuEta_reach hf hs h (os ++ [v]) (app_closed hos hv)
        (fun w hw => hps w (List.mem_cons_of_mem _ hw))
      simp only [List.append_assoc, List.singleton_append] at ih
      refine PureSteps.trans ?_ ih
      simp only [NuTree.toE, NuArg.up_val, NuArg.omap_val_up, NuArg.map_val_up, List.map_cons,
        nuAppsE, NuArg.toE]
      refine (nuAppsE_steps (ℍ := ℍ) ps (PureSteps.beta _ v)).trans ?_
      rw [NuTree.toE_subst u _ _ _ (NuArg.val_closed hf) (oval_closed hs)
        (vals_app_closed hos (NuArg.var_closed 0)) 0 hv]
      simp [NuArg.sub, List.map_append]
      exact .refl
  | _, _, _, .dead (u := u) (ps := ps) h, os, hos, hps => by
      have ih := nuEta_reach hf hs h (os ++ [Val.unit]) (app_closed hos rfl)
        (fun w hw => hps w (List.mem_cons_of_mem _ hw))
      simp only [List.append_assoc, List.singleton_append] at ih
      refine PureSteps.trans ?_ ih
      simp only [NuTree.toE, NuArg.up_val, NuArg.omap_val_up, NuArg.map_val_up, List.map_cons,
        nuAppsE, NuArg.toE]
      refine (nuAppsE_steps (ℍ := ℍ) ps (PureSteps.beta _ .unit)).trans ?_
      rw [NuTree.toE_subst u _ _ _ (NuArg.val_closed hf) (oval_closed hs)
        (vals_app_closed hos (NuArg.val_closed rfl)) 0 rfl]
      simp [NuArg.sub_val, List.map_append]
      exact .refl

/-- A leaf of the η-tree is the observation of `f s` made so far, by at most one β. -/
theorem nuEta_leaf {ℍ : Host} [HostIs ℍ] {fv : Val} {sv : Option Val}
    (hs : ∀ v ∈ sv, closedAt 0 v.1 = true) (rb : Bool) (os : List Val)
    (hos : ∀ v ∈ os, closedAt 0 v.1 = true) :
    PureSteps (ℍ := ℍ) ((NuTree.leaf rb).toE (.val fv) (sv.map .val) (os.map .val))
      (nuAppsE (nuHeadE (.val fv) (sv.map .val)) (os.map .val)) := by
  cases rb with
  | false => exact .refl
  | true =>
    simp only [NuTree.toE, NuArg.omap_val_up, NuArg.map_val_up, NuArg.toE]
    refine (PureSteps.beta _ fv).trans ?_
    rw [nuAppsE_subst _ _ (vals_closed hos), nuHeadE_subst (NuArg.var_closed 0) (oval_closed hs),
      NuArg.map_val_sub, NuArg.omap_val_sub]
    exact .refl

/-- **The η-thunk's observations are `f s`'s**: an observation `ps` of the thunk that reaches a
leaf of its η-tree reaches, by pure steps, the same observation of `f s` (of `f`, with no
state).  `[spec §45, §65]` -/
theorem nuEta_obs {ℍ : Host} [HostIs ℍ] {fv : Val} {sv : Option Val} {t : NuTree} {ps : List Val}
    {rb : Bool} (hf : closedAt 0 fv.1 = true) (hs : ∀ v ∈ sv, closedAt 0 v.1 = true)
    (hps : ∀ v ∈ ps, closedAt 0 v.1 = true) (h : t.Reach ps (.leaf rb)) :
    PureSteps (ℍ := ℍ) (nuAppsE (t.toE (.val fv) (sv.map .val) []) (ps.map .val))
      (nuAppsE (nuHeadE (.val fv) (sv.map .val)) (ps.map .val)) := by
  have := nuEta_reach (ℍ := ℍ) hf hs h [] (by simp) hps
  simp only [List.map_nil, List.nil_append] at this
  exact this.trans (nuEta_leaf hs rb ps hps)

/-- **With no state, the η-thunk is its variable**: its observations are `f`'s. -/
theorem nuEta_var {ℍ : Host} [HostIs ℍ] {fv : Val} {t : NuTree} {ps : List Val} {rb : Bool}
    (hf : closedAt 0 fv.1 = true) (hps : ∀ v ∈ ps, closedAt 0 v.1 = true)
    (h : t.Reach ps (.leaf rb)) :
    PureSteps (ℍ := ℍ) (nuAppsE (t.toE (.val fv) none []) (ps.map .val))
      (nuAppsE (.val fv) (ps.map .val)) :=
  nuEta_obs (sv := none) hf (by simp) hps h

/-- **At `f = unfold step`, the η-thunk is the codata `f s` computes**: its every observation
that reaches a leaf reaches by pure steps the same observation of `etaN C g s`, which `f s` steps
to by one β at every memory (`hN_steps`).  `[spec §45, §65]` -/
theorem nuEta_unfold {ℍ : Host} [HostIs ℍ] (C : CTy) (g sv : Val) {t : NuTree} {ps : List Val}
    {rb : Bool} (hf : closedAt 0 (hN C g).1 = true) (hs : closedAt 0 sv.1 = true)
    (hps : ∀ v ∈ ps, closedAt 0 v.1 = true) (h : t.Reach ps (.leaf rb)) :
    PureSteps (ℍ := ℍ) (nuAppsE (t.toE (.val (hN C g)) (some (.val sv)) []) (ps.map .val))
      (nuAppsE (.val (etaN C g sv)) (ps.map .val)) ∧
    PureSteps (ℍ := ℍ) (.app (.val (hN C g)) (.val sv)) (.val (etaN C g sv)) := by
  refine ⟨?_, hN_steps C g sv⟩
  have := nuEta_obs (ℍ := ℍ) (sv := some sv) hf (by simpa using hs) hps h
  exact this.trans (nuAppsE_steps ps (hN_steps C g sv))

/-! ### A walk's read  `[spec §46]`

A walk node with `read` (`walkReadB`) is, at a shared view, `let (v, c) = array_copy v₀;
count (λq. S, (len c, (i, s)))` with `s`'s first component `v`, and its step `S` takes its argument
apart, copies the view and reads the copy at the counter, each tail handing the view on
(`walkStepB`, `walkTailsB`). The bound is the view's length (`walk_copy_len`); the step runs only
below the bound (`walk_index_lt`, `walk_fold_index_lt`); below it, the view's read answers its
leaf (`walk_get_leaf`). At a unique view the step splits one element off the view and reads it at
`0`: the head of a split by one is one element long, so that read answers its leaf whatever the
view (`walk_get_split`). -/

/-- **A shared walk's bound is its view's length**: `array_copy` of the view answers the view
twice, and `array_len` of it its length, by pure steps. -/
theorem walk_copy_len {ℍ : Host} [HostIs ℍ] (ℓ : Loc) (n : UInt32) :
    PureSteps (ℍ := ℍ) (.app (.val copyV) (.val (Val.arr ℓ n)))
        (.val (Val.pair (Val.arr ℓ n) (Val.arr ℓ n))) ∧
      PureSteps (ℍ := ℍ) (.app (.val arrLenV) (.val (Val.arr ℓ n))) (.val (Val.i32 n)) := by
  constructor
  · have := PureSteps.beta (ℍ := ℍ) (.pair (.var 0) (.var 0)) (Val.arr ℓ n)
    simpa [copyV, Expr.subst] using this
  · refine (PureSteps.beta (ℍ := ℍ) (.letpair (.var 0) (.var 0)) (Val.arr ℓ n)).trans ?_
    simp only [Expr.subst]
    have := PureSteps.head (ℍ := ℍ) (fun μ => BoCa.BoLo.Head.letpair μ (Val.loc ℓ) (Val.i32 n) (.var 0)) rfl
    simpa [Val.arr, Expr.subst, Expr.shift, Val.i32] using this

/-- **The head of a split by one is read in range**: when `split ((ℓ, n), 1)` answers its two
parts, the first is `(ℓ, 1)`, whose element `0` is its leaf. -/
theorem walk_get_split (ℓ : Loc) (n : UInt32) {h t : Val}
    (hs : splitAns ℓ n 1 = .inj₁ (.pair h t)) : h = Val.arr ℓ 1 ∧ idxAns ℓ 1 0 = .inj₁ (.loc ℓ) := by
  unfold splitAns at hs
  split at hs
  · simp only [Val.inj₁, Val.pair, Subtype.mk.injEq, Expr.inj₁.injEq, Expr.pair.injEq] at hs
    refine ⟨Subtype.ext hs.1.symm, ?_⟩
    have := idxAns_lt ℓ (n := 1) (i := 0) (by decide)
    simpa using this
  · simp [Val.inj₂, Val.inj₁] at hs

end BoCa.Fig16.LogRel.Core.Check
