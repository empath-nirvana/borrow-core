import Affine.Elab

/-!
# Affine — programs with implicit drops

Each program is a source term with no destructor call for the values it discards, an
`ADerives` derivation that places the discards, and the elaborated term that derivation
produces. Adequacy (`runsA`) runs the elaborated term to a value with no cell left, at every
host; the interpreter (`eval`, Wasm's host) computes the answer by `decide`.

**`sumAff`**: `IntPrograms`' `sumListProg` (build `[100, 20, 3]` as blocks, lend it to
`foldImm`'s sum, get it back) with both explicit frees removed. The source ends
`let (r′, n) = p in return n`; the owner `r′ : Ref L` comes back from the loan and is dropped
at the end of its scope. Its destructor is `free`, then `foldOwn` with the algebra that frees
each node's value cell (`HasDtor.ref (.mu …)`). Answer `123`, no cell left, as
`sumListProg_eval`.

**`blockAff b`**: a block `{a : I32, b : I32}` (one allocation, two leaves), then a branch. The
first arm moves `a` out of its cell and returns it; the unused field `b` is dropped at the end
of the arm. The second arm uses nothing and drops the whole block. Answers `7` and `0`, no cell
left on either path.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Affine
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### The list's destructor -/

theorem hasDtor_ilistL : HasDtor ilistL :=
  .mu (A := ilistF.ty) ilistF_WF trivial
    (.sum .unit (.tensor (.ref .int) .unit))

/-! ### The borrowed sum at the empty context -/

theorem d_sumIAlg0 : CDerives LifeCtx.empty [] (.val sumIAlgV) (.val (algTy ilistF 0 .i32)) := by
  refine d_algI .nil (.ret ?_)
  refine caseP (A := .unit) (B := .tensor (.imm (.var 0) .i32) .i32) (.var (by csoloP))
    (d_i32 0 (by cdeadP)) ?_
  refine letP (A := .imm (.var 0) .i32) (B := .i32) (.var (by csoloP)) ?_
  refine d_hop (.bin .w32 .add) (pairP ?_ (.var (by csoloP))) (by cdeadP)
  exact appW
    (callbackW ΔA_ok (x := 1) rfl (by cdead)
      (.boxI (.var (by csoloP))
        (CtxOutlives.solo (LifeCtx.defines_of_wf (wf_var_self _ _ _)) (outlives_of_dataB rfl)
          (by cdead))))
    (appW (.var (by csoloP))
      (.withload (a := .var 0) (A := .i32) (B := .i32) 1 (by cdeadP) rfl (by simp [VFree])
        (by simp [VFree])))

theorem d_sumI0 : CDerives LifeCtx.empty [] sumIE (.val (fTy ilistL .i32)) :=
  .lolliE .nil d_sumIAlg0
    (.foldImm ilistF 0 LifeCtx.empty.meetOfDom .i32 .nil ilistF_WF trivial
      (by simp [VFree, FShape.ty]) (by simp [VFree]) (fun _ _ => .int))

/-! ### `sumAff`: the list dropped after the loan -/

/-- `build to s. alloc s to r. return g to g′. withbor r borrower to p. let (r′, n) = p in K`,
with the fold `g` at index `0`. -/
def openWith (build K : Expr) : Expr :=
  bindE build (bindE (.app (.val (.prim .alloc)) (.var 0))
    (bindE (.var 2)
      (bindE (.app (.app withbor (.var 1)) borrowerE)
        (.letpair (.var 0) K))))

/-- The source: `… let (r′, n) = p in return n`, no free. -/
def sumAff : Expr := bindE sumIE (openWith (buildI [100, 20, 3]) (.var 0))

/-- The elaboration: `r′` (index `1`) dropped before `return n`. -/
def sumAffE : Expr := bindE sumIE (openWith (buildI [100, 20, 3]) (dropE (.ref ilistL) 1 (.var 0)))

theorem ilistL_closed : ∀ z, ¬ VFree z ilistL := fun _ => by simp [VFree, FShape.ty]

theorem sumAff_derives : ADerives LifeCtx.empty [] sumAff sumAffE (.comp (.ret .i32)) := by
  refine .bind .nil (.core (.ret d_sumI0)) ?_
  -- `build to s`
  refine .bind (.right .nil) (.core (.ret (d_buildI (.cons .nil) _))) ?_
  -- `alloc s to r`
  refine .bind (.left (.right .nil))
    (.core (.ret (.lolliE (.left (.dead .nil)) (.var (.here (.cons .nil)))
      (.alloc (A := ilistL) (.cons (.cons .nil)))))) ?_
  -- `return g to g′`
  refine .bind (.right (.dead (.left .nil)))
    (.core (.ret (.var (.there (.there (.here .nil)))))) ?_
  -- `withbor r borrower to p`
  refine .bind (.left (.left (.dead (.dead .nil))))
    (.core (.ret (.lolliE (.left (.right (.dead (.dead .nil))))
      (d_borrowerG (by repeat constructor) (fun _ _ => .int) rfl)
      (.lolliE (.dead (.left (.dead (.dead .nil))))
        (.var (.there (.here (by repeat constructor))))
        (.withbor1 (A := ilistL) (B := .i32) 0 (by repeat constructor) rfl
          (fun y h => absurd h (ilistL_closed y)) (ilistL_closed 0) (by simp [VFree])))))) ?_
  -- `let (r′, n) = p in`
  refine .tensorE (A := .ref ilistL) (B := .i32) (.left (.dead (.dead (.dead (.dead .nil)))))
    (.core (.var (.here (by repeat constructor)))) ?_
  -- drop `r′`; `return n`
  exact .drop (.right (.left (.dead (.dead (.dead (.dead (.dead .nil)))))))
    (.there (.here (by repeat constructor))) (.ref hasDtor_ilistL)
    (.core (.ret (.var (.here (by repeat constructor)))))

/-- **The elaborated sum runs at every host**, from the empty memory to a 32-bit literal and the
empty memory. -/
theorem sumAffE_runs :
    ∃ v, BoCa.BoLo.Steps Adequacy.emptyMem sumAffE Adequacy.emptyMem (.val v) ∧
      ∃ n, v = Val.i32 n :=
  runsA (fun _ _ _ hv => by obtain ⟨rfl, n, rfl⟩ := hv; exact ⟨rfl, n, rfl⟩) sumAff_derives

set_option maxRecDepth 100000 in
/-- The interpreter: `123`, no cell left, as the explicit-free program. -/
theorem sumAffE_eval : i32NoLeak (eval sumAffE) = some 123 := by decide

/-! ### `blockAff`: a field and a block dropped in the arms that do not use them -/

abbrev σB : Shape := .node (.leaf .i32) (.leaf .i32)

/-- `allocS σB (7, 5) to s. case b {inj₁ u. u; let (a, b) = s in free a to m. return m
| inj₂ u. u; return 0}`. -/
def blockWith (b : Bool) (K₁ K₂ : Expr) : Expr :=
  bindE (.app (allocS σB) (.pair (i32E 7) (i32E 5)))
    (.case (bval b).1
      (.seq (.var 0) (.letpair (.var 1) (bindE (.app (.val (.prim .free)) (.var 1)) K₁)))
      (.seq (.var 0) K₂))

/-- The source: neither `b` in the first arm nor `s` in the second is freed. -/
def blockAff (b : Bool) : Expr := blockWith b (.var 0) (i32E 0)

/-- The elaboration: the field `b` (index `1`) dropped before `return m`; the block (index `1`)
dropped before `return 0`. -/
def blockAffE (b : Bool) : Expr :=
  blockWith b (dropE (.ref .i32) 1 (.var 0)) (dropE σB.refTy 1 (i32E 0))

theorem blockAff_derives (b : Bool) :
    ADerives LifeCtx.empty [] (blockAff b) (blockAffE b) (.comp (.ret .i32)) := by
  -- `allocS σB (7, 5) to s`
  refine .bind .nil (.core (.ret (.lolliE .nil (.tensorI .nil (d_i32 7 .nil) (d_i32 5 .nil))
    (d_allocS σB .nil)))) ?_
  refine .sumE (.right .nil) (.core (d_bval (.cons .nil) b)) ?_ ?_
  · -- `u; let (a, b) = s in free a to m.` drop `b`; `return m`
    refine .unitE (.left (.right .nil)) (.core (.var (.here (by repeat constructor)))) ?_
    refine .tensorE (A := .ref .i32) (B := .ref .i32) (.dead (.left .nil))
      (.core (.var (.there (.here .nil)))) ?_
    refine .bind (.right (.left (.dead (.dead .nil))))
      (.core (.ret (.lolliE (.dead (.left (.dead (.dead .nil))))
        (.var (.there (.here (by repeat constructor)))) (.free (by repeat constructor))))) ?_
    exact .drop (.right (.left (.dead (.dead (.dead .nil))))) (.there (.here (by repeat constructor)))
      (.ref .int) (.core (.ret (.var (.here (by repeat constructor)))))
  · -- `u;` drop `s`; `return 0`
    refine .unitE (.left (.right .nil)) (.core (.var (.here (by repeat constructor)))) ?_
    exact .drop (.dead (.left .nil)) (.there (.here .nil)) (.tensor (.ref .int) (.ref .int))
      (.core (.ret (d_i32 0 (by repeat constructor))))

theorem blockAffE_runs (b : Bool) :
    ∃ v, BoCa.BoLo.Steps Adequacy.emptyMem (blockAffE b) Adequacy.emptyMem (.val v) ∧
      ∃ n, v = Val.i32 n :=
  runsA (fun _ _ _ hv => by obtain ⟨rfl, n, rfl⟩ := hv; exact ⟨rfl, n, rfl⟩) (blockAff_derives b)

/-- The interpreter: the first arm returns `7`, no cell left. -/
theorem blockAffE_eval₁ : i32NoLeak (eval (blockAffE false)) = some 7 := by decide

/-- The interpreter: the second arm returns `0`, no cell left. -/
theorem blockAffE_eval₂ : i32NoLeak (eval (blockAffE true)) = some 0 := by decide

/-! ### Without the inserted drops the programs leak -/

/-- The source run as is: the value comes back, and the interpreter reports a cell left. -/
theorem sumAff_leaks :
    (match eval sumAff with | .value _ true => true | _ => false) = true := by decide

theorem blockAff_leaks (b : Bool) :
    (match eval (blockAff b) with | .value _ true => true | _ => false) = true := by
  cases b <;> decide

end BoCa.Fig16.LogRel.Core.Affine

end
