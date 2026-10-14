import Law2.Rules

/-!
# Law2 — the fundamental lemma for the piece judgment

`pj_fundamental`: every derivation of Core's typing, at the stack `σ` and the lenders' row `S₀`, is
the piece judgment — a value judgment `V : A` re-lendable (`PV`), a computation judgment `M : C`
in `RC C` (`PJ`) — by one induction on `CDerives`, one case per rule. Each case is a lemma of
`Law2/Rules.lean`, or, where a rule is not derived, its own lemma below, stated at the rule's
premises and closed by `sorry`. Some rules are proved at part of their instances and not derived
at the rest; the case splits on the rule's own types and rows, never on the stack.

`piece_of_typed_R` is (S1) at a context given slot by slot (`RCtx`), from `pj_fundamental` and
`openS_of_pj`.

**The rules not derived** (each `sorry` below; no obstruction verified for any):

* `∀`: `fl_allI_ctx` (`[∀I]` at a context holding `U`), `fl_allE`, `fl_allEV`;
* `[@a]`: `fl_boxI_ctx` (`[]I` at a type that does not itself outlive `@a`);
* `μ`, `ν`: `fl_roll_thunk` (`roll` at an unrolling holding `U`), `fl_unroll`, `fl_nuIn`,
  `fl_nuOut`, `fl_unfoldN`, `fl_foldImm`, `fl_foldOwn`, `fl_foldReuse`;
* loops over a callback: `fl_countFold`, `fl_countTry`, `fl_arrNew`, `fl_arrFree`;
* a leaf or part taken out of a family: `fl_arrGet`, `fl_arrReplace`, `fl_arrCopy`,
  `fl_sliceGetM`, `fl_sliceSplitI`, `fl_sliceSplitM`, `fl_sliceReplaceM`, `fl_sliceSwapM`;
* families otherwise: `fl_arrSize`, `fl_arrLen`, `fl_arrForget`, `fl_sliceLenM`, `fl_sliceEmptyI`,
  `fl_sliceEmptyM`;
* an inner lend: `fl_withbor1`, `fl_withbor2`, `fl_withbor3`, `fl_withload`, `fl_withswap`,
  `fl_withbor1U`, `fl_withbor2U`, `fl_withbor3U`, `fl_withloadU`, `fl_sliceBorrowM`,
  `fl_sliceBorrowI`, `fl_sliceBorrowMU`, `fl_sliceBorrowIU`;
* the effect rules: `fl_effPerform_open` (a lenders' name at an operation that is not resuming
  data), `fl_effRaise`, `fl_effLet_open` (a row whose lenders' operations are not all linear
  resuming), `fl_effThen`, `fl_effHandleV_open` (a handler of a lenders' name, or at an operation
  that is not linear).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Law2
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Kont Head Step1N performE opPayload)
open BoCa.Lifetime (LifeVar LifeCtx LSub)
open GhostEnd

/-- **The piece judgment at a judgment form**: `PV` at `V : A`, `PJ` at `M : C`. -/
def PJudg (δ : LSub) (σ : LStack) (S₀ : Row) (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) :
    Jdg → Prop
  | .val A => PV (ℍ := ℍ) δ σ S₀ Δ Γ e A
  | .comp C => PJ (ℍ := ℍ) δ σ S₀ Δ Γ e C

section open_rules
variable {δ : LSub} {σ : LStack} {S₀ : Row}

/-! ### The rules not derived -/

/-- **`[∀I]` at a context holding a `U` — not derived; no obstruction verified.** `∀` is read at
the kernel's relation at the current lifetimes; its body's context then has to be read at the
kernel's relation, which a re-lendable closure in it is not (`rslot_vC` reads types free of `U`). -/
theorem fl_allI_ctx {Δ : LifeCtx} {Γ : Ctx VTy} {x : LifeVar} {b : Lifetime.Life} {M : Expr}
    {S : VTy} {C : CTy} (_hbx : b.mentions x = false)
    (_hΔx : ∀ y u, Δ.find? y = some u → u.mentions x = false)
    (_hΓx : ∀ s ∈ Γ, s.live = true → ¬ VFree x s.ty)
    (_hd : CDerives (Δ.extend x b) (⟨S, false⟩ :: Γ) M (.comp C))
    (_ih : PJ (ℍ := ℍ) δ σ S₀ (Δ.extend x b) (⟨S, false⟩ :: Γ) M C) (_hΓ : ¬ CtxNoThunk Γ) :
    PJ (ℍ := ℍ) δ σ S₀ Δ Γ (.val (.lam M)) (.all x b C) := by
  sorry

/-- **`[∀E]` — not derived; no obstruction verified.** The instance is read at the kernel's
relation at `C[@a/'x]`, which does not give the re-lendable reading there: at a row, a run's
`ewpTS` at one reading is not the piece (§15's route 1); at `F A`, the answer is not
re-lendable. A `∀` instantiated inside the borrower and held across a stop fixes its lifetime
while the stack's re-lends move the bound. -/
theorem fl_allE {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {x : LifeVar} {b a : Lifetime.Life}
    {C : CTy} (_ih : PJ (ℍ := ℍ) δ σ S₀ Δ Γ M (.all x b C)) (_hlt : Δ.EntailsLt a b) :
    PJ (ℍ := ℍ) δ σ S₀ Δ Γ (.app M (.val .unit)) (C.instLife x a) := by
  sorry

/-- **`[∀E]` called by value — not derived; no obstruction verified.** As `fl_allE`. -/
theorem fl_allEV {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {x : LifeVar} {b a : Lifetime.Life}
    {A : VTy} (_ih : PV (ℍ := ℍ) δ σ S₀ Δ Γ e (.all x b A)) (_hlt : Δ.EntailsLt a b) :
    PV (ℍ := ℍ) δ σ S₀ Δ Γ (.app e (.val .unit)) (A.instLife x a) := by
  sorry

/-- **`[]I` at a type that does not outlive `@a` — not derived; no obstruction verified.** A
boxed value held across a stop is re-lent at shorter lifetimes; that its views stay in `Res_{@a}`
follows from its type outliving `@a` (`rslot_outlives`, `pv_boxI_outlives`), and the rule's
premise is that its context does. Which views the value holds is not recorded against the
context's. -/
theorem fl_boxI_ctx {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {A : VTy} {a : Lifetime.Life}
    (_ih : PV (ℍ := ℍ) δ σ S₀ Δ Γ e A) (_hΓ : CtxOutlives Δ Γ a) (_hA : ¬ VOutlives Δ a A) :
    PV (ℍ := ℍ) δ σ S₀ Δ Γ e (.box a A) := by
  sorry

/-- **`roll` at an unrolling holding `U` — not derived; no obstruction verified.** `μ` is read at
the kernel's relation; a re-lendable closure under the unrolling is not in it. -/
theorem fl_roll_thunk {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {A : VTy} (_hA : A.NoMut 0)
    (_hc : (VTy.mu A).Cl 0) (_ih : PV (ℍ := ℍ) δ σ S₀ Δ Γ e (VTy.inst (.mu A) A))
    (_hN : ¬ NoThunkT (VTy.inst (.mu A) A)) : PV (ℍ := ℍ) δ σ S₀ Δ Γ e (.mu A) := by
  sorry

/-- **`unroll` — not derived; no obstruction verified.** A `μ` value is re-lendable as one value
at the kernel's relation; its unrolling is read componentwise, and the value's split into views
and a frozen part is not split along the components. -/
theorem fl_unroll {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {A : VTy}
    (_ih : PV (ℍ := ℍ) δ σ S₀ Δ Γ e (.mu A)) :
    PV (ℍ := ℍ) δ σ S₀ Δ Γ e (VTy.inst (.mu A) A) := by
  sorry

/-- **`ν` in — not derived; no obstruction verified.** `ν` is read at the kernel's relation; the
unrolling's re-lendable reading does not give it. -/
theorem fl_nuIn {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {C : CTy} (_hC : C.NuOk)
    (_ih : PJ (ℍ := ℍ) δ σ S₀ Δ Γ e C.unroll) : PJ (ℍ := ℍ) δ σ S₀ Δ Γ e (.nu C) := by
  sorry

/-- **`ν` out — not derived; no obstruction verified.** The kernel's relation at the unrolling
does not give the re-lendable reading. -/
theorem fl_nuOut {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {C : CTy} (_hC : C.NuOk)
    (_ih : PJ (ℍ := ℍ) δ σ S₀ Δ Γ e (.nu C)) : PJ (ℍ := ℍ) δ σ S₀ Δ Γ e C.unroll := by
  sorry

/-- **Coiteration — not derived; no obstruction verified.** Its step is a re-lendable closure;
the kernel's coiteration reads it at the kernel's relation. -/
theorem fl_unfoldN {Δ : LifeCtx} {Γ : Ctx VTy} (C : CTy) (S : VTy) (_hC : C.NuOk)
    (_hΓ : Ctx.DeadP Γ) : PV (ℍ := ℍ) δ σ S₀ Δ Γ (.val (unfoldV C)) (unfoldTy C S) := by
  sorry

/-- **The borrowed fold — not derived; no obstruction verified.** Its algebra is a re-lendable
closure, and the fold's run over a `μ` value read at the kernel's relation is the kernel's
proof at the kernel's relation. -/
theorem fl_foldImm {Δ : LifeCtx} {Γ : Ctx VTy} (F : FShape) (y : LifeVar) (c : Lifetime.Life)
    (R : VTy) (_hΓ : Ctx.DeadP Γ) (_hF : F.WF) (_hG : F.Guarded) (_hyM : ¬ VFree y (.mu F.ty))
    (_hyR : ¬ VFree y R) (_hR : ∀ Δ' a, VOutlives Δ' a R) :
    PV (ℍ := ℍ) δ σ S₀ Δ Γ (.val (foldImmV F)) (.lolli (algTy F y R) (foldTy F y c R)) := by
  sorry

/-- **The owned fold — not derived; no obstruction verified.** As `fl_foldImm`. -/
theorem fl_foldOwn {Δ : LifeCtx} {Γ : Ctx VTy} (F : FShape) (R : VTy) (_hΓ : Ctx.DeadP Γ)
    (_hF : F.WF) (_hG : F.Guarded) :
    PV (ℍ := ℍ) δ σ S₀ Δ Γ (.val (foldOwnV F)) (.lolli (algOTy F R) (foldOTy F R)) := by
  sorry

/-- **The owned fold with reuse — not derived; no obstruction verified.** As `fl_foldImm`. -/
theorem fl_foldReuse {Δ : LifeCtx} {Γ : Ctx VTy} (F : FShape) (R : VTy) (_hΓ : Ctx.DeadP Γ)
    (_hF : F.WF) (_hG : F.Guarded) :
    PV (ℍ := ℍ) δ σ S₀ Δ Γ (.val (foldReuseV F)) (.lolli (algRTy F R) (foldOTy F R)) := by
  sorry

/-- **`count_fold` — not derived; no obstruction verified.** Its step is a re-lendable closure;
the counted loop's induction at the re-lendable reading (as `rslot_boundedFix`'s) is not
written. -/
theorem fl_countFold {Δ : LifeCtx} {Γ : Ctx VTy} (S : VTy) (_hΓ : Ctx.DeadP Γ) :
    PV (ℍ := ℍ) δ σ S₀ Δ Γ (.val (.prim .count)) (countFoldTy S) := by
  sorry

/-- **`count_try` — not derived; no obstruction verified.** As `fl_countFold`. -/
theorem fl_countTry {Δ : LifeCtx} {Γ : Ctx VTy} (S E : VTy) (_hΓ : Ctx.DeadP Γ) :
    PV (ℍ := ℍ) δ σ S₀ Δ Γ (.val (.prim .countTry)) (countTryTy S E) := by
  sorry

/-- **`array_new` — not derived; no obstruction verified.** Its element function is a
re-lendable closure, called once per element; the loop at the re-lendable reading is not
written, and the family it builds is read at the kernel's relation. -/
theorem fl_arrNew {Δ : LifeCtx} {Γ : Ctx VTy} (A : VTy) (_hΓ : Ctx.DeadP Γ) :
    PV (ℍ := ℍ) δ σ S₀ Δ Γ (.val (.prim .tab)) (arrNewTy A) := by
  sorry

/-- **`array_free` — not derived; no obstruction verified.** As `fl_arrNew`, its finaliser a
re-lendable closure called once per element of a family read at the kernel's relation. -/
theorem fl_arrFree {Δ : LifeCtx} {Γ : Ctx VTy} (A : VTy) (_hΓ : Ctx.DeadP Γ) :
    PV (ℍ := ℍ) δ σ S₀ Δ Γ (.val (.prim .drop)) (arrFreeTy A) := by
  sorry

/-- **`array_size` — not derived; no obstruction verified.** A family is read at the kernel's
relation; the lemma that its re-lendable reading passes through the size step unchanged is not
written. -/
theorem fl_arrSize {Δ : LifeCtx} {Γ : Ctx VTy} (A : VTy) (_hΓ : Ctx.DeadP Γ) :
    PV (ℍ := ℍ) δ σ S₀ Δ Γ (.val sizeV) (arrSizeTy A) := by
  sorry

/-- **`array_replace` — not derived; no obstruction verified.** A family is read at the kernel's
relation; the element taken out is not re-lendable on its own (the family's split into views and a
frozen part is not split by location), and the one stored in has to be at the kernel's
relation. -/
theorem fl_arrReplace {Δ : LifeCtx} {Γ : Ctx VTy} (A : VTy) (_hΓ : Ctx.DeadP Γ) :
    PV (ℍ := ℍ) δ σ S₀ Δ Γ (.val replaceV) (arrReplaceTy A) := by
  sorry

/-- **`array_len` — not derived; no obstruction verified.** As `fl_arrSize`. -/
theorem fl_arrLen {Δ : LifeCtx} {Γ : Ctx VTy} (a : Lifetime.Life) (A : VTy)
    (_hΓ : Ctx.DeadP Γ) : PV (ℍ := ℍ) δ σ S₀ Δ Γ (.val arrLenV) (arrLenTy a A) := by
  sorry

/-- **`array_get` — not derived; no obstruction verified.** As `fl_arrReplace`: a leaf taken
out of a family read at the kernel's relation. -/
theorem fl_arrGet {Δ : LifeCtx} {Γ : Ctx VTy} (a : Lifetime.Life) (A : VTy)
    (_hΓ : Ctx.DeadP Γ) : PV (ℍ := ℍ) δ σ S₀ Δ Γ (.val (.prim .idx)) (arrGetTy a A) := by
  sorry

/-- **`array_copy` — not derived; no obstruction verified.** A family of `imm` leaves duplicated:
the lemma that the duplicate shares the original's re-lendable reading is not written. -/
theorem fl_arrCopy {Δ : LifeCtx} {Γ : Ctx VTy} (a : Lifetime.Life) (A : VTy)
    (_hΓ : Ctx.DeadP Γ) : PV (ℍ := ℍ) δ σ S₀ Δ Γ (.val copyV) (arrCopyTy a A) := by
  sorry

/-- **`array_forget` — not derived; no obstruction verified.** As `fl_arrSize`. -/
theorem fl_arrForget {Δ : LifeCtx} {Γ : Ctx VTy} (a : Lifetime.Life) (A : VTy)
    (_hΓ : Ctx.DeadP Γ) : PV (ℍ := ℍ) δ σ S₀ Δ Γ (.val forgetV) (arrForgetTy a A) := by
  sorry

/-- **`slice_borrow_mut` — not derived; no obstruction verified.** An inner lend: its callback,
read at the kernel's relation (`∀`), runs with the inner lend open; the kernel's lend (6.65) reads
the lent array at the kernel's relation, and the result comes back at the kernel's relation, which
is not re-lendable. -/
theorem fl_sliceBorrowM {Δ : LifeCtx} {Γ : Ctx VTy} {A B : VTy} (x : LifeVar) (_hΓ : Ctx.DeadP Γ)
    (_hsideA : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A)
    (_hsideB : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b B) (_hfree₁ : ¬ VFree x A)
    (_hfree₂ : ¬ VFree x B) :
    PV (ℍ := ℍ) δ σ S₀ Δ Γ withbor (sliceBorrowMTy x Δ.meetOfDom A B) := by
  sorry

/-- **`slice_borrow_imm` — not derived; no obstruction verified.** As `fl_sliceBorrowM`. -/
theorem fl_sliceBorrowI {Δ : LifeCtx} {Γ : Ctx VTy} {A B : VTy} (x : LifeVar) (_hΓ : Ctx.DeadP Γ)
    (_hsc : VScoped Δ A) (_hsideA : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A)
    (_hsideB : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b B) (_hfree₁ : ¬ VFree x A)
    (_hfree₂ : ¬ VFree x B) :
    PV (ℍ := ℍ) δ σ S₀ Δ Γ withbor (sliceBorrowITy x Δ.meetOfDom A B) := by
  sorry

/-- **`slice_get_mut` — not derived; no obstruction verified.** As `fl_arrGet`. -/
theorem fl_sliceGetM {Δ : LifeCtx} {Γ : Ctx VTy} (a : Lifetime.Life) (A : VTy)
    (_hΓ : Ctx.DeadP Γ) : PV (ℍ := ℍ) δ σ S₀ Δ Γ (.val (.prim .idx)) (sliceGetMTy a A) := by
  sorry

/-- **`slice_len_mut` — not derived; no obstruction verified.** As `fl_arrSize`. -/
theorem fl_sliceLenM {Δ : LifeCtx} {Γ : Ctx VTy} (a : Lifetime.Life) (A : VTy)
    (_hΓ : Ctx.DeadP Γ) : PV (ℍ := ℍ) δ σ S₀ Δ Γ (.val sizeV) (sliceLenMTy a A) := by
  sorry

/-- **`slice_split_imm` — not derived; no obstruction verified.** A family read at the kernel's
relation split by location: its re-lendable split does not split along the parts. -/
theorem fl_sliceSplitI {Δ : LifeCtx} {Γ : Ctx VTy} (a : Lifetime.Life) (A : VTy)
    (_hΓ : Ctx.DeadP Γ) : PV (ℍ := ℍ) δ σ S₀ Δ Γ (.val (.prim .split)) (sliceSplitITy a A) := by
  sorry

/-- **`slice_split_mut` — not derived; no obstruction verified.** As `fl_sliceSplitI`. -/
theorem fl_sliceSplitM {Δ : LifeCtx} {Γ : Ctx VTy} (a : Lifetime.Life) (A : VTy)
    (_hΓ : Ctx.DeadP Γ) : PV (ℍ := ℍ) δ σ S₀ Δ Γ (.val (.prim .split)) (sliceSplitMTy a A) := by
  sorry

/-- **`slice_empty_imm` — not derived; no obstruction verified.** As `fl_arrSize`. -/
theorem fl_sliceEmptyI {Δ : LifeCtx} {Γ : Ctx VTy} (a : Lifetime.Life) (A : VTy)
    (_hΓ : Ctx.DeadP Γ) : PV (ℍ := ℍ) δ σ S₀ Δ Γ (.val emptyFamV) (.arrayImm a A) := by
  sorry

/-- **`slice_empty_mut` — not derived; no obstruction verified.** As `fl_arrSize`. -/
theorem fl_sliceEmptyM {Δ : LifeCtx} {Γ : Ctx VTy} (a : Lifetime.Life) (A : VTy)
    (_hΓ : Ctx.DeadP Γ) : PV (ℍ := ℍ) δ σ S₀ Δ Γ (.val emptyFamV) (.sliceMut a A) := by
  sorry

/-- **`slice_replace_mut` — not derived; no obstruction verified.** As `fl_arrReplace`. -/
theorem fl_sliceReplaceM {Δ : LifeCtx} {Γ : Ctx VTy} (a : Lifetime.Life) (A : VTy)
    (_hΓ : Ctx.DeadP Γ) : PV (ℍ := ℍ) δ σ S₀ Δ Γ (.val replaceV) (sliceReplaceMTy a A) := by
  sorry

/-- **`slice_swap_mut` — not derived; no obstruction verified.** As `fl_arrReplace`. -/
theorem fl_sliceSwapM {Δ : LifeCtx} {Γ : Ctx VTy} (a : Lifetime.Life) (A : VTy)
    (_hΓ : Ctx.DeadP Γ) : PV (ℍ := ℍ) δ σ S₀ Δ Γ (.val swapV) (sliceSwapMTy a A) := by
  sorry

/-- **`withbor` (1) — not derived; no obstruction verified.** As `fl_sliceBorrowM`: an inner lend,
the lent reference and the result read at the kernel's relation. -/
theorem fl_withbor1 {Δ : LifeCtx} {Γ : Ctx VTy} {A B : VTy} (x : LifeVar) (_hΓ : Ctx.DeadP Γ)
    (_hx : Δ.find? x = none) (_hsc₁ : VScoped Δ A) (_hfree₁ : ¬ VFree x A)
    (_hfree₂ : ¬ VFree x B) :
    PV (ℍ := ℍ) δ σ S₀ Δ Γ withbor (axWithbor1Ty x Δ.meetOfDom A B) := by
  sorry

/-- **`withbor` (2) — not derived; no obstruction verified.** As `fl_withbor1`. -/
theorem fl_withbor2 {Δ : LifeCtx} {Γ : Ctx VTy} {A B : VTy} (x : LifeVar) (_hΓ : Ctx.DeadP Γ)
    (_hx : Δ.find? x = none) (_hside : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A)
    (_hfree₁ : ¬ VFree x A) (_hfree₂ : ¬ VFree x B) :
    PV (ℍ := ℍ) δ σ S₀ Δ Γ withbor (axWithbor2Ty x Δ.meetOfDom A B) := by
  sorry

/-- **`withbor` (3), the reborrow — not derived; no obstruction verified.** As `fl_withbor1`; the
reborrowed view comes back from the kernel's 6.66/6.65 at the kernel's relation. -/
theorem fl_withbor3 {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {A B : VTy} (x : LifeVar)
    (_hΓ : Ctx.DeadP Γ) (_hx : Δ.find? x = none) (_hfree₁ : ¬ VFree x A)
    (_hfree₂ : ¬ VFree x B) :
    PV (ℍ := ℍ) δ σ S₀ Δ Γ withbor (axWithbor3Ty a x Δ.meetOfDom A B) := by
  sorry

/-- **`withload` — not derived; no obstruction verified.** As `fl_withbor3`. -/
theorem fl_withload {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {A B : VTy} (x : LifeVar)
    (_hΓ : Ctx.DeadP Γ) (_hx : Δ.find? x = none) (_hfree₁ : ¬ VFree x A)
    (_hfree₂ : ¬ VFree x B) :
    PV (ℍ := ℍ) δ σ S₀ Δ Γ withload (axWithloadTy a x Δ.meetOfDom A B) := by
  sorry

/-- **`withswap` — not derived; no obstruction verified.** Its callback is a re-lendable closure
run inside the kernel's anti-frame (6.66), which reads it at the kernel's relation. -/
theorem fl_withswap {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {A B : VTy}
    (_hΓ : Ctx.DeadP Γ) : PV (ℍ := ℍ) δ σ S₀ Δ Γ withswap (axWithswapTy a A B) := by
  sorry

/-- **The unwinding `withbor` (1) — not derived; no obstruction verified.** An inner lend whose
callback unwinds to an inner handler: the lend ends at the unwind, which the piece does not read
(it has no unwind outcome). -/
theorem fl_withbor1U {Δ : LifeCtx} {Γ : Ctx VTy} {A B : VTy} {d : Expr} {S : Row} (x : LifeVar)
    (_hΓ : Ctx.DeadP Γ) (_hx : Δ.find? x = none) (_hsc₁ : VScoped Δ A) (_hfree₁ : ¬ VFree x A)
    (_hfree₂ : ¬ VFree x B) (_hS : S.Unwind x) (_hdc : closedAt 0 d = true)
    (_ihd : PV (ℍ := ℍ) δ σ S₀ Δ Γ d (.lolli (.ref A) .unit)) :
    PV (ℍ := ℍ) δ σ S₀ Δ Γ (withborUE d) (withbor1UTy x Δ.meetOfDom A B S) := by
  sorry

/-- **The unwinding `withbor` (2) — not derived; no obstruction verified.** As `fl_withbor1U`. -/
theorem fl_withbor2U {Δ : LifeCtx} {Γ : Ctx VTy} {A B : VTy} {d : Expr} {S : Row} (x : LifeVar)
    (_hΓ : Ctx.DeadP Γ) (_hx : Δ.find? x = none) (_hside : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A)
    (_hfree₁ : ¬ VFree x A) (_hfree₂ : ¬ VFree x B) (_hS : S.Unwind x)
    (_hdc : closedAt 0 d = true) (_ihd : PV (ℍ := ℍ) δ σ S₀ Δ Γ d (.lolli (.ref A) .unit)) :
    PV (ℍ := ℍ) δ σ S₀ Δ Γ (withborUE d) (withbor2UTy x Δ.meetOfDom A B S) := by
  sorry

/-- **The unwinding `withbor` (3) — not derived; no obstruction verified.** As `fl_withbor1U`. -/
theorem fl_withbor3U {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {A B : VTy} {d : Expr}
    {S : Row} (x : LifeVar) (_hΓ : Ctx.DeadP Γ) (_hx : Δ.find? x = none) (_hfree₁ : ¬ VFree x A)
    (_hfree₂ : ¬ VFree x B) (_hS : S.Unwind x) (_hdc : closedAt 0 d = true)
    (_ihd : PV (ℍ := ℍ) δ σ S₀ Δ Γ d (.lolli (.mut a A) .unit)) :
    PV (ℍ := ℍ) δ σ S₀ Δ Γ (withborUE d) (withbor3UTy a x Δ.meetOfDom A B S) := by
  sorry

/-- **The unwinding `withload` — not derived; no obstruction verified.** As `fl_withbor1U`. -/
theorem fl_withloadU {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {A B : VTy} {S : Row}
    (x : LifeVar) (_hΓ : Ctx.DeadP Γ) (_hx : Δ.find? x = none) (_hfree₁ : ¬ VFree x A)
    (_hfree₂ : ¬ VFree x B) (_hS : S.Unwind x) :
    PV (ℍ := ℍ) δ σ S₀ Δ Γ withload (withloadUTy a x Δ.meetOfDom A B S) := by
  sorry

/-- **The unwinding `slice_borrow_mut` — not derived; no obstruction verified.** As
`fl_withbor1U`. -/
theorem fl_sliceBorrowMU {Δ : LifeCtx} {Γ : Ctx VTy} {A B : VTy} {d : Expr} {S : Row}
    (x : LifeVar) (_hΓ : Ctx.DeadP Γ) (_hsideA : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A)
    (_hsideB : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b B) (_hfree₁ : ¬ VFree x A)
    (_hfree₂ : ¬ VFree x B) (_hS : S.Unwind x) (_hdc : closedAt 0 d = true)
    (_ihd : PV (ℍ := ℍ) δ σ S₀ Δ Γ d (.lolli (.array A) .unit)) :
    PV (ℍ := ℍ) δ σ S₀ Δ Γ (withborUE d) (sliceBorrowMUTy x Δ.meetOfDom A B S) := by
  sorry

/-- **The unwinding `slice_borrow_imm` — not derived; no obstruction verified.** As
`fl_withbor1U`. -/
theorem fl_sliceBorrowIU {Δ : LifeCtx} {Γ : Ctx VTy} {A B : VTy} {d : Expr} {S : Row}
    (x : LifeVar) (_hΓ : Ctx.DeadP Γ) (_hsc : VScoped Δ A)
    (_hsideA : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A)
    (_hsideB : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b B) (_hfree₁ : ¬ VFree x A)
    (_hfree₂ : ¬ VFree x B) (_hS : S.Unwind x) (_hdc : closedAt 0 d = true)
    (_ihd : PV (ℍ := ℍ) δ σ S₀ Δ Γ d (.lolli (.array A) .unit)) :
    PV (ℍ := ℍ) δ σ S₀ Δ Γ (withborUE d) (sliceBorrowIUTy x Δ.meetOfDom A B S) := by
  sorry

/-- **`[perform]` at a lenders' name, not at resuming data — not derived; no obstruction
verified.** The stop crosses the lends; the lenders' table and `fold_mixed` are stated at
operations that resume linearly, answered at `1`, whose argument is data free of the stack's
variables and outliving every lifetime (`ResumeOp`). -/
theorem fl_effPerform_open {Δ : LifeCtx} {Γ : Ctx VTy} {V : Expr} {S : Row} {o : OpSig}
    (_hf : Row.find S o.n o.i = some o) (_hna : o.abort = false)
    (_ih : PV (ℍ := ℍ) δ σ S₀ Δ Γ V o.A) (_hout : outN S₀ o.n = true) (_hR : ¬ ResumeOp σ o) :
    PJ (ℍ := ℍ) δ σ S₀ Δ Γ (performE (opArgE o.n o.i V)) (CTy.effOf S o.B) := by
  sorry

/-- **`[raise]` — not derived; no obstruction verified.** An abortive operation caught inside the
borrower unwinds to its handler; the piece has no unwind outcome. At a lenders' name the
operation is abortive, which `fold_mixed`'s linear resuming table does not admit. -/
theorem fl_effRaise {Δ : LifeCtx} {Γ : Ctx VTy} {V : Expr} {S : Row} {o : OpSig} {B : VTy}
    (_hf : Row.find S o.n o.i = some o) (_ha : o.abort = true) (_hd : o.A.Drop)
    (_ih : PV (ℍ := ℍ) δ σ S₀ Δ Γ V o.A) :
    PJ (ℍ := ℍ) δ σ S₀ Δ Γ (BoCa.BoLo.raiseE (opArgE o.n o.i V)) (CTy.effOf S B) := by
  sorry

/-- **`[let]` at a row whose lenders' operations do not all resume linearly — not derived; no
obstruction verified.** The stacked bind (`bodyH_bind`, `openH_bind`) carries its frame across
stops that resume once; a stop that may cancel would have to unwind the frozen frame. -/
theorem fl_effLet_open {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {M N : Expr} {A B : VTy} {S : Row}
    (_hs : Ctx.SplitP Γ Γ₁ Γ₂) (_hW : S.Weak → Γ₂.Drops) (_hU : S.Unr → Persistent Γ₂)
    (_ihM : PJ (ℍ := ℍ) δ σ S₀ Δ Γ₁ M (CTy.effOf S A))
    (_ihN : PJ (ℍ := ℍ) δ σ S₀ Δ (⟨A, true⟩ :: Γ₂) N (CTy.effOf S B)) (_hL : ¬ RowLin S₀ S) :
    PJ (ℍ := ℍ) δ σ S₀ Δ Γ (.app (.val (.lam N)) M) (CTy.effOf S B) := by
  sorry

/-- **`[then]` — not derived; no obstruction verified.** Its finaliser runs when a continuation
captured in `M` is cancelled; the piece's continuations are resumed, never cancelled, and its
frames do not unwind. -/
theorem fl_effThen {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {M N D : Expr} {A B : VTy} {S SM SD : Row}
    (_hs : Ctx.SplitP Γ Γ₁ Γ₂) (_hNZ : S.NZ) (_hUq : S.Uniq) (_hU : S.UnrD → Persistent Γ₂)
    (_hMS : RowLe SM S) (_hDS : RowLe SD S)
    (_hfin : ∀ n i o o', Row.find SM n i = some o → Row.find S n i = some o' →
      capB o.q o.B = true → ThenLe o.fin SD o'.fin)
    (_hP : SD.UnrD → SM.PendPers)
    (_ihM : PJ (ℍ := ℍ) δ σ S₀ Δ Γ₁ M (CTy.effOf SM A))
    (_ihN : PJ (ℍ := ℍ) δ σ S₀ Δ (⟨A, true⟩ :: Γ₂) N (CTy.effOf S B))
    (_ihD : PJ (ℍ := ℍ) δ σ S₀ Δ (⟨.unit, false⟩ :: Γ₂) D (CTy.effOf SD .unit)) :
    PJ (ℍ := ℍ) δ σ S₀ Δ Γ (thenE N D M) (CTy.effOf S B) := by
  sorry

/-- **`[handle]` of a lenders' name, or at an operation that is not linear — not derived; no
obstruction verified.** The piece classifies a stop by its name (`outN`): a handler inside the
borrower of a lenders' name catches stops the piece reads as crossing the lends. At an affine or
unrestricted operation the continuation a clause is handed may be dropped or copied, and an
abortive one unwinds, none of which `InStop` reads. -/
theorem fl_effHandleV_open {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {H e : Expr} {S : Row}
    {E : List (Qual × VTy × VTy)} {fs : Nat → CTy} {n : UInt32} {A R : VTy}
    (_hs : Ctx.SplitP Γ Γ₁ Γ₂) (_hd : Ctx.DeadP Γ₁) (_hH : H.ValFormIn Γ₁)
    (_ihc : PV (ℍ := ℍ) δ σ S₀ Δ Γ₁ H (.tensor (retTy S A R) (clausesTy S R E fs)))
    (_hn0 : n ≠ 0) (_hnS : ∀ o ∈ S, o.n ≠ n) (_hlen : E.length ≤ 2 ^ 32)
    (_ihe : PJ (ℍ := ℍ) δ σ S₀ Δ Γ₂ e (CTy.effOf (Row.ofEff n E 0 fs ++ S) A))
    (_hopen : ¬ (outN S₀ n = false ∧ ∀ q ∈ E, q.1 = .lin)) :
    PJ (ℍ := ℍ) δ σ S₀ Δ Γ (hndExpr n (E.map Prod.fst) H e) (CTy.effOf S R) := by
  sorry

end open_rules

/-! ### The fundamental lemma -/

section fund
variable {δ : LSub} {σ : LStack} {S₀ : Row}

/-- **The fundamental lemma for the piece judgment.** Every derivation of Core's typing is the
piece judgment at its judgment form, by one induction on the derivation; each rule is its lemma of
`Law2/Rules.lean`, the rules and instances not derived their `fl_` lemma above. -/
theorem pj_fundamental : ∀ {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg},
    CDerives Δ Γ e j → PJudg (ℍ := ℍ) δ σ S₀ Δ Γ e j := by
  intro Δ Γ e j hd
  induction hd with
  | var h => exact pv_var h
  | unitI h => exact pv_unit h
  | tensorI hs _ _ ih₁ ih₂ => exact pv_pair hs ih₁ ih₂
  | sumI₁ _ ih => exact pv_inj₁ ih
  | sumI₂ _ ih => exact pv_inj₂ ih
  | thunkF _ ih => exact pv_thunkF ih
  | thunkV hC _ ih => exact pv_thunkV hC ih
  | ret _ ih => exact pj_ret ih
  | bind hs _ _ ihM ihN => exact pj_bind hs ihM ihN
  | force h => exact pj_force h
  | lam _ ih => exact pj_lam ih
  | lamDead _ ih => exact pj_lamDead ih
  | app hs _ hx ih => exact pj_app hs ih hx
  | withI _ _ ihM ihN => exact pj_withI ihM ihN
  | proj₁ _ ih => exact pj_proj₁ ih
  | proj₂ _ ih => exact pj_proj₂ ih
  | topI => exact pj_topI
  | unitE hs _ _ ihV ihM => exact pj_seq hs ihV ihM
  | tensorE hs _ _ ihV ihM => exact pj_letpair hs ihV ihM
  | sumE hs _ _ _ ihV ih₁ ih₂ => exact pj_case hs ihV ih₁ ih₂
  | zeroE hs _ ihV => exact pj_zeroE hs ihV
  | @allI Δ' Γ' x b M S C hbx hΔx hΓx h ih =>
      by_cases hΓ : CtxNoThunk Γ'
      · exact pj_allI_kernel hbx hΔx hΓx h hΓ
      · exact fl_allI_ctx hbx hΔx hΓx h ih hΓ
  | allE _ hlt ih => exact fl_allE ih hlt
  | bangThunkF hp _ ih => exact pv_bangThunkF hp ih
  | bangThunkV hp hC _ ih => exact pv_bangThunkV hp hC ih
  | bangE _ ih => exact pv_bangE ih
  | copyBang hΓ => exact pv_copyBang hΓ
  | forgetBang hΓ => exact pv_forgetBang hΓ
  | @boxI Δ' Γ' e' a A _ hΓ ih =>
      by_cases hA : VOutlives Δ' a A
      · exact pv_boxI_outlives ih hΓ.1 hA
      · exact fl_boxI_ctx ih hΓ hA
  | boxE _ ih => exact pv_boxE ih
  | immSub _ hle ih => exact pv_immSub ih hle
  | mutSub _ hle ih => exact pv_mutSub ih hle
  | alloc hΓ => exact pv_alloc hΓ
  | free hΓ => exact pv_free hΓ
  | swap hΓ => exact pv_swap hΓ
  | copy hΓ => exact pv_copy hΓ
  | forgetImm hΓ => exact pv_forgetImm hΓ
  | forgetMut hΓ => exact pv_forgetMut hΓ
  | forgetUnk hΓ => exact pv_forgetUnk hΓ
  | lit c hΓ => exact pv_lit c hΓ
  | hostOp op hΓ => exact pv_hostOp op hΓ
  | arrNew A hΓ => exact fl_arrNew A hΓ
  | arrFree A hΓ => exact fl_arrFree A hΓ
  | arrSize A hΓ => exact fl_arrSize A hΓ
  | arrReplace A hΓ => exact fl_arrReplace A hΓ
  | arrLen a A hΓ => exact fl_arrLen a A hΓ
  | arrGet a A hΓ => exact fl_arrGet a A hΓ
  | arrCopy a A hΓ => exact fl_arrCopy a A hΓ
  | arrForget a A hΓ => exact fl_arrForget a A hΓ
  | countFold S hΓ => exact fl_countFold S hΓ
  | countTry S E hΓ => exact fl_countTry S E hΓ
  | boundedFix A C hΓ => exact pv_boundedFix hΓ
  | sliceBorrowM x hΓ hA hB hf₁ hf₂ => exact fl_sliceBorrowM x hΓ hA hB hf₁ hf₂
  | sliceBorrowI x hΓ hsc hA hB hf₁ hf₂ => exact fl_sliceBorrowI x hΓ hsc hA hB hf₁ hf₂
  | sliceGetM a A hΓ => exact fl_sliceGetM a A hΓ
  | sliceLenM a A hΓ => exact fl_sliceLenM a A hΓ
  | sliceSplitI a A hΓ => exact fl_sliceSplitI a A hΓ
  | sliceSplitM a A hΓ => exact fl_sliceSplitM a A hΓ
  | sliceEmptyI a A hΓ => exact fl_sliceEmptyI a A hΓ
  | sliceEmptyM a A hΓ => exact fl_sliceEmptyM a A hΓ
  | sliceReplaceM a A hΓ => exact fl_sliceReplaceM a A hΓ
  | sliceSwapM a A hΓ => exact fl_sliceSwapM a A hΓ
  | withbor1 x hΓ hx hsc₁ hf₁ hf₂ => exact fl_withbor1 x hΓ hx hsc₁ hf₁ hf₂
  | withbor2 x hΓ hx hside hf₁ hf₂ => exact fl_withbor2 x hΓ hx hside hf₁ hf₂
  | withbor3 x hΓ hx hf₁ hf₂ => exact fl_withbor3 x hΓ hx hf₁ hf₂
  | withload x hΓ hx hf₁ hf₂ => exact fl_withload x hΓ hx hf₁ hf₂
  | withswap hΓ => exact fl_withswap hΓ
  | withbor1U x hΓ hx hsc₁ hf₁ hf₂ hS hdc _ ihd =>
      exact fl_withbor1U x hΓ hx hsc₁ hf₁ hf₂ hS hdc ihd
  | withbor2U x hΓ hx hside hf₁ hf₂ hS hdc _ ihd =>
      exact fl_withbor2U x hΓ hx hside hf₁ hf₂ hS hdc ihd
  | withbor3U x hΓ hx hf₁ hf₂ hS hdc _ ihd => exact fl_withbor3U x hΓ hx hf₁ hf₂ hS hdc ihd
  | withloadU x hΓ hx hf₁ hf₂ hS => exact fl_withloadU x hΓ hx hf₁ hf₂ hS
  | sliceBorrowMU x hΓ hA hB hf₁ hf₂ hS hdc _ ihd =>
      exact fl_sliceBorrowMU x hΓ hA hB hf₁ hf₂ hS hdc ihd
  | sliceBorrowIU x hΓ hsc hA hB hf₁ hf₂ hS hdc _ ihd =>
      exact fl_sliceBorrowIU x hΓ hsc hA hB hf₁ hf₂ hS hdc ihd
  | lolliE hs _ _ iha ihf => exact pv_lolliE hs iha ihf
  | allEV _ hlt ih => exact fl_allEV ih hlt
  | ofRet _ ih => exact pv_ofRet ih
  | @roll Δ' Γ' e' A' hA hc _ ih =>
      by_cases hN : NoThunkT (VTy.inst (.mu A') A')
      · exact pv_roll hA hc hN ih
      · exact fl_roll_thunk hA hc ih hN
  | unroll _ ih => exact fl_unroll ih
  | foldImm F y c R hΓ hF hG hyM hyR hR => exact fl_foldImm F y c R hΓ hF hG hyM hyR hR
  | foldOwn F R hΓ hF hG => exact fl_foldOwn F R hΓ hF hG
  | foldReuse F R hΓ hF hG => exact fl_foldReuse F R hΓ hF hG
  | nuIn hC _ ih => exact fl_nuIn hC ih
  | nuOut hC _ ih => exact fl_nuOut hC ih
  | unfoldN C S hC hΓ => exact fl_unfoldN C S hC hΓ
  | effSub hle _ ih => exact pj_effSub hle ih
  | @effPerform Δ' Γ' V S o hf hna _ ih =>
      cases hout : outN S₀ o.n
      · exact pj_performIn hf hout ih
      · by_cases hR : ResumeOp σ o
        · exact pj_effPerform_resume hf hout hR ih
        · exact fl_effPerform_open hf hna ih hout hR
  | effRaise hf ha hd _ ih => exact fl_effRaise hf ha hd ih
  | @effLet Δ' Γ' Γ₁ Γ₂ M N A B S hs hW hU _ _ ihM ihN =>
      by_cases hL : RowLin S₀ S
      · exact pj_let hL hs ihM ihN
      · exact fl_effLet_open hs hW hU ihM ihN hL
  | effThen hs hNZ hUq hU hMS hDS hfin hP _ _ _ ihM ihN ihD =>
      exact fl_effThen hs hNZ hUq hU hMS hDS hfin hP ihM ihN ihD
  | @effHandleV Δ' Γ' Γ₁ Γ₂ H e' S E fs n A R hs hd hH _ hn0 hnS hlen _ ihc ihe =>
      by_cases ho : outN S₀ n = false ∧ ∀ q ∈ E, q.1 = .lin
      · exact pj_handle hs hd hH ihc ho.1 hnS hlen ho.2 ihe
      · exact fl_effHandleV_open hs hd hH ihc hn0 hnS hlen ihe ho
  | letPoly b hcl _ _ _ ihN => exact pj_letPoly (Val.lam b) hcl ihN

end fund

end Law2

end
