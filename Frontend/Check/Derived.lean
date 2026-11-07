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

/-! ### Codata's η-thunk  `[spec §45]`

A loop's codata is written as the η-thunk of an observation of `f s`
(`thunkv nu_in < (nu_out (force f s)).1, (nu_out (force f s)).2 >`, `nuEtaE`), since `thunkv`
takes only a λ. Its two observations are the observations of `f s`: each is a β, a `case` and a
`;` away (`nuEta_obs`). When `f` is `unfold step` (`hN`, the value `unfold step` steps to),
`f s` is itself one β at every memory to the codata `etaN C g s` (`hN_steps`), so the thunk's every
observation reaches the same observation of that value by pure steps (`nuEta_unfold`): the value
may be computed where the thunk is built. With no state, the thunk's observations are those of
`f` (`nuEta_var`). -/

/-- An arm of the closed η-thunk at the observation `o`: `fv sv o`, `fv o` with no state; with
`rb`, through a binding of `fv` first. -/
def nuArmV (fv : Val) (sv : Option Val) (rb : Bool) (o : Val) : Expr :=
  let body : Option Val → Expr
    | some sv => .app (.app (.var 0) (.val sv)) (.val o)
    | none => .app (.var 0) (.val o)
  if rb then .app (.val (.lam (body sv))) (.val fv) else (body sv).subst 0 fv

/-- `nuEtaE` at closed values: the `&` of the two arms. -/
def nuEtaV (fv : Val) (sv : Option Val) (rb : Bool) : Expr :=
  withPair (nuArmV fv sv rb (.inj₁ .unit)) (nuArmV fv sv rb (.inj₂ .unit))

/-- The observation `fv sv o` (`fv o` with no state). -/
def nuObsV (fv : Val) (sv : Option Val) (o : Val) : Expr :=
  match sv with
  | some sv => .app (.app (.val fv) (.val sv)) (.val o)
  | none => .app (.val fv) (.val o)

theorem nuArmV_closed {ℍ : Host} [HostIs ℍ] {fv : Val} {sv : Option Val} {rb : Bool} {o : Val}
    (hf : closedAt 0 fv.1 = true) (hs : ∀ v ∈ sv, closedAt 0 v.1 = true)
    (ho : closedAt 0 o.1 = true) :
    closedAt 0 (nuArmV fv sv rb o) = true ∧ PureSteps (ℍ := ℍ) (nuArmV fv sv rb o) (nuObsV fv sv o) := by
  cases sv with
  | none =>
    cases rb
    · simp [nuArmV, nuObsV, Expr.subst, closed_subst ho, closedAt, hf, ho]; exact .refl
    · refine ⟨by simp [nuArmV, closedAt, hf, closedAt_mono _ ho (Nat.zero_le _)], ?_⟩
      have := PureSteps.beta (ℍ := ℍ) (.app (.var 0) (.val o)) fv
      simpa [nuArmV, nuObsV, Expr.subst, closed_subst ho] using this
  | some sv =>
    have hs' := hs sv rfl
    cases rb
    · simp [nuArmV, nuObsV, Expr.subst, closed_subst ho, closed_subst hs', closedAt, hf, ho, hs']
      exact .refl
    · refine ⟨by simp [nuArmV, closedAt, hf, closedAt_mono _ ho (Nat.zero_le _),
        closedAt_mono _ hs' (Nat.zero_le _)], ?_⟩
      have := PureSteps.beta (ℍ := ℍ) (.app (.app (.var 0) (.val sv)) (.val o)) fv
      simpa [nuArmV, nuObsV, Expr.subst, closed_subst ho, closed_subst hs'] using this

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

/-- **The η-thunk's observations are `f s`'s**: at `inj₁ ()` and `inj₂ ()`, by pure steps. -/
theorem nuEta_obs {ℍ : Host} [HostIs ℍ] {fv : Val} {sv : Option Val} (rb k : Bool)
    (hf : closedAt 0 fv.1 = true) (hs : ∀ v ∈ sv, closedAt 0 v.1 = true) :
    PureSteps (ℍ := ℍ) (.app (nuEtaV fv sv rb) (.val (if k then .inj₂ .unit else .inj₁ .unit)))
      (nuObsV fv sv (if k then .inj₂ .unit else .inj₁ .unit)) := by
  have h₁ := nuArmV_closed (ℍ := ℍ) (rb := rb) (o := .inj₁ .unit) hf hs rfl
  have h₂ := nuArmV_closed (ℍ := ℍ) (rb := rb) (o := .inj₂ .unit) hf hs rfl
  refine (withPair_obs h₁.1 h₂.1 k).trans ?_
  cases k
  · exact h₁.2
  · exact h₂.2

/-- **With no state, the η-thunk is its variable**: its observations are `f`'s. -/
theorem nuEta_var {ℍ : Host} [HostIs ℍ] {fv : Val} (rb k : Bool) (hf : closedAt 0 fv.1 = true) :
    PureSteps (ℍ := ℍ) (.app (nuEtaV fv none rb) (.val (if k then .inj₂ .unit else .inj₁ .unit)))
      (.app (.val fv) (.val (if k then .inj₂ .unit else .inj₁ .unit))) :=
  nuEta_obs rb k hf (by simp)

/-- **At `f = unfold step`, the η-thunk is the codata `f s` computes**: its every observation
reaches by pure steps the same observation of `etaN C g s`, which `f s` steps to by one β at
every memory (`hN_steps`). -/
theorem nuEta_unfold {ℍ : Host} [HostIs ℍ] (C : CTy) (g sv : Val) (rb k : Bool)
    (hf : closedAt 0 (hN C g).1 = true) (hs : closedAt 0 sv.1 = true) :
    PureSteps (ℍ := ℍ) (.app (nuEtaV (hN C g) (some sv) rb) (.val (if k then .inj₂ .unit else .inj₁ .unit)))
      (.app (.val (etaN C g sv)) (.val (if k then .inj₂ .unit else .inj₁ .unit))) ∧
    PureSteps (ℍ := ℍ) (.app (.val (hN C g)) (.val sv)) (.val (etaN C g sv)) := by
  refine ⟨(nuEta_obs rb k hf (by simpa using hs)).trans ?_, hN_steps C g sv⟩
  exact PureSteps.plug (.appL .hole _) (hN_steps C g sv)

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
