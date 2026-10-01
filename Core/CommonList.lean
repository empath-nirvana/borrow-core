import Core.Blocks

/-!
# Core — the common list shape through the block view  `[spec §5, §6]`

Rust's `Box<Node { val, next }>` list is `μX. 1 ⊕ Ref (N ⊗ X)`: each node is one allocation of
a product.  Read through `Blocks.lean`, the owned handle of a block of `N ⊗ X` is the leaf
family, so the list is

    μX. 1 ⊕ Ref (N ⊗ X)   =   μX. 1 ⊕ (Ref N ⊗ Ref X)      (`clistF_ty`, by `refTy_pair`)

and the right-hand side is in `FShape`.  A node is allocated by `allocS nodeC` as one block
(`consC`), so the value leaf and the next leaf are adjacent cells.

Every function below is `foldImm alg` or `foldOwn alg` with `alg` a `CDerives` derivation; each
program is one closed `CDerives` derivation, run by adequacy and by the interpreter.  No
per-program proof.

* `sumCE = foldImm sumAlg : !U(∀'a. Imm 'a L ⊸ F N)`: the algebra sees `1 ⊕ (Imm 'y N ⊗ N)`,
  copies the borrowed payload (`natCopy`, itself `foldImm`) and adds (`addE`, `foldOwn` at `N`).
* `mapIncCE = foldOwn mapAlg : U(L ⊸ F L)`: frees each node's value leaf and allocates a fresh
  block for the incremented node.
* `toPureCE = foldOwn tpAlg : U(L ⊸ F P)`, `freeCE = foldOwn freeAlg : U(L ⊸ F 1)`.
* `sumProg` sums `[1, 2, 3]` inside an immutable borrow (`6`, no cell left); `mapProgC` maps
  `[0, 0, 0]` inside a mutable borrow and returns `[1, 1, 1]`, no cell left.
* `consC_block`: at every frame, on some run, a node is allocated as one block `(ℓ, ℓ + 1)`;
  `buildC_blocks`, `mapIncC_blocks`: the interpreter's list after `buildC` and after `mapIncCE`
  has every node at adjacent cells.

`foldOwn` frees each `Ref X` cell before the algebra runs, so `mapIncCE` rebuilds the list in
fresh blocks.  The in-place map over this shape is `foldReuse` (`ReuseList.lean`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### The shape -/

/-- `1 ⊕ (Ref N ⊗ Ref X)`. -/
abbrev clistF : FShape := .sum (.leaf .unit) (.tensor (.leaf (.ref natN)) .refX)

/-- `Node { val : N, next : X }`, one block. -/
abbrev nodeS : Shape := .node (.leaf natN) (.leaf (.tvar 0))

/-- **The common list shape is in `FShape`**: `1 ⊕ Ref (N ⊗ X)`, with `Ref (N ⊗ X)` the block
handle of a node, is `clistF`'s body. -/
theorem clistF_ty : clistF.ty = .sum .unit nodeS.refTy := rfl

/-- `L = μX. 1 ⊕ Ref (N ⊗ X)`, the node a block. -/
abbrev clistL : VTy := .mu clistF.ty

theorem clistF_WF : clistF.WF := by simp [FShape.WF, VTy.Cl, natN, natBody]

/-- The node at the closed list type: `N ⊗ L`. -/
abbrev nodeC : Shape := .node (.leaf natN) (.leaf clistL)

theorem clistL_unroll : VTy.inst clistL clistF.ty = .sum .unit nodeC.refTy := rfl

theorem clistL_outlives (Δ : LifeCtx) (a : Lifetime.Life) : VOutlives Δ a clistL :=
  .mu (.sum .unit (.tensor (.ref (natN_outlives _ _)) (.ref .tvar)))

/-! ### Building -/

/-- `inj₂ (allocS nodeC (n, t))`: a node, allocated as one block. -/
def consC (n t : Expr) : Expr := .inj₂ (.app (allocS nodeC) (.pair n t))

theorem d_consC {Δ : LifeCtx} {Γ Γ₁ Γ₂ ΓD : Ctx VTy} {n t : Expr} (hs : Ctx.SplitP Γ Γ₁ Γ₂)
    (hA : Ctx.SplitP Γ Γ ΓD) (hD : Ctx.Dead ΓD)
    (hn : CDerives Δ Γ₁ n (.val natN)) (ht : CDerives Δ Γ₂ t (.val clistL)) :
    CDerives Δ Γ (consC n t) (.val clistL) :=
  .roll (FShape.noMut_ty clistF_WF) (FShape.Cl_ty clistF_WF)
    (.sumI₂ (.lolliE hA (.tensorI hs hn ht) (d_allocS nodeC hD)))

/-- `[]`. -/
def nilC : Expr := .inj₁ (.val .unit)

theorem d_nilC {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ nilC (.val clistL) :=
  .roll (FShape.noMut_ty clistF_WF) (FShape.Cl_ty clistF_WF) (.sumI₁ (.unitI hΓ))

/-- A list of literals. -/
def buildList : List Nat → Expr
  | [] => nilC
  | k :: ks => consC (.val (num k)) (buildList ks)

theorem d_buildList {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    ∀ ks, CDerives Δ Γ (buildList ks) (.val clistL)
  | [] => d_nilC hΓ
  | k :: ks => d_consC (deadSplit hΓ) (deadSplit hΓ) hΓ (d_num hΓ k) (d_buildList hΓ ks)

/-- `[1, 2, 3]`. -/
def buildC : Expr := buildList [1, 2, 3]

/-- `[0, 0, 0]`. -/
def buildC0 : Expr := buildList [0, 0, 0]

/-! ### Adding numerals -/

/-- `λm. m`. -/
def idV : Val := .lam (.var 0)

/-- `case r {inj₁ u. u; λm. m | inj₂ f. λm. f (m + 1)}`: `add k = λm. k + m`. -/
def addAlgB : Expr :=
  .case (.var 0) (.seq (.var 0) (.val idV)) (.val (.lam (.app (.var 1) (.inj₂ (.var 0)))))

def addAlgV : Val := .lam addAlgB

theorem d_addAlg {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ (.val addAlgV) (.val (algOTy natF (.lolli natN natN))) := by
  refine d_algO hΓ (.sumE (A := .unit) (B := .lolli natN natN) (.left (deadSplit hΓ))
    (.var (.here hΓ)) ?_ ?_)
  · exact .unitE (.left (.dead (deadSplit hΓ))) (.var (.here (.cons hΓ)))
      (.ret (.thunkV rfl (.lam (.ret (.var (.here (.cons (.cons hΓ))))))))
  · exact .ret (.thunkV rfl (.lam (.ret (.lolliE (.left (.right (.dead (deadSplit hΓ))))
      (.roll natBody_noMut natN_closed (.sumI₂ (.var (.here (.cons (.cons hΓ))))))
      (.var (.there (.here (.cons hΓ))))))))

/-- `foldOwn addAlg : N ⊸ F (U(N ⊸ F N))`. -/
def addE : Expr := .app (.val (foldOwnV natF)) (.val addAlgV)

theorem d_add {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ addE (.val (.lolli natN (.lolli natN natN))) :=
  .bangE (.lolliE (deadSplit hΓ) (d_addAlg hΓ)
    (.foldOwn natF (.lolli natN natN) hΓ ⟨trivial, trivial⟩ trivial))

/-! ### Copying a borrowed numeral inside an algebra -/

/-- The context of a `foldImm` algebra's body: `'y ⊏ ⊤` at lifetime variable `0`. -/
abbrev ΔA : LifeCtx := LifeCtx.empty.extend 0 LifeCtx.empty.meetOfDom

/-- The count algebra at `ΔA`, bound at lifetime variable `1`. -/
theorem d_countAlg1 {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives ΔA Γ (.val countAlgV) (.val (algTy natF 1 natN)) :=
  .bangThunkV (persistent_dead hΓ) rfl
    (.allI (S := .unit) rfl (fun y u hy => by
        simp only [LifeCtx.extend, LifeCtx.find?, LifeCtx.empty] at hy
        simp only [Lifetime.assocFind] at hy
        split at hy
        · cases hy; rfl
        · simp at hy)
      (dead_noLive hΓ) (.ret (.thunkV rfl (.lam (d_countAlgB (.cons hΓ))))))

/-- `natCopy` at `ΔA`, its binder at lifetime variable `1`. -/
theorem d_natCopy1 {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives ΔA Γ natCopyE (.val (foldTy natF 1 LifeCtx.empty.meetOfDom natN)) :=
  .lolliE (deadSplit hΓ) (d_countAlg1 hΓ)
    (.foldImm natF 1 LifeCtx.empty.meetOfDom natN hΓ ⟨trivial, trivial⟩ trivial
      (by simp [VFree, FShape.ty]) (by simp [VFree, natN, natBody]) natN_outlives)

/-- `natCopy [] : Imm 'y N ⊸ F N`, at the algebra's lifetime `'y`. -/
theorem d_natCopyAt {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives ΔA Γ (.app natCopyE (.val .unit)) (.val (.lolli (.imm (.var 0) natN) natN)) :=
  .allEV (x := 1) (b := LifeCtx.empty.meetOfDom) (a := .var 0)
    (A := VTy.lolli (.imm (.var 1) natN) natN) (.bangE (d_natCopy1 hΓ)) (fun _ hδ => hδ 0 _ rfl)

/-! ### The algebras -/

/-- `case r {inj₁ u. u; 0 | inj₂ p. let (b, s) = p in natCopy [] b to n. add n s}`. -/
def sumAlgB : Expr :=
  .case (.var 0) (.seq (.var 0) (.inj₁ (.val .unit)))
    (.letpair (.var 0)
      (bindE (.app (.app natCopyE (.val .unit)) (.var 1)) (.app (.app addE (.var 0)) (.var 1))))

/-- The sum algebra, `!U(∀'y. 1 ⊕ (Imm 'y N ⊗ N) ⊸ F N)`. -/
def sumAlgV : Val := .lam (.val (.lam sumAlgB))

theorem d_sumAlgB {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives ΔA (⟨clistF.res 0 natN, true⟩ :: Γ) sumAlgB (.comp (.ret natN)) := by
  refine .sumE (A := .unit) (B := .tensor (.imm (.var 0) natN) natN) (.left (deadSplit hΓ))
    (.var (.here hΓ)) ?_ ?_
  · exact .unitE (.left (.dead (deadSplit hΓ))) (.var (.here (.cons hΓ)))
      (.ret (.roll natBody_noMut natN_closed (.sumI₁ (.unitI (.cons (.cons hΓ))))))
  have G2 : Ctx.Dead (⟨VTy.tensor (.imm (.var 0) natN) natN, false⟩ ::
      ⟨clistF.res 0 natN, false⟩ :: Γ) := .cons (.cons hΓ)
  refine .tensorE (A := .imm (.var 0) natN) (B := natN) (.left (.dead (deadSplit hΓ)))
    (.var (.here (.cons hΓ))) ?_
  refine .bind (A := natN) (.right (.left (deadSplit G2)))
    (.ret (.lolliE (.dead (.left (deadSplit G2))) (.var (.there (.here G2)))
      (d_natCopyAt (.cons (.cons G2))))) ?_
  exact .ret (.lolliE (.right (.left (.dead (deadSplit G2))))
    (.var (.there (.here (.cons G2))))
    (.lolliE (.left (.dead (.dead (deadSplit G2)))) (.var (.here (.cons (.cons G2))))
      (d_add (.cons (.cons (.cons G2))))))

theorem d_sumAlg {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives LifeCtx.empty Γ (.val sumAlgV) (.val (algTy clistF 0 natN)) :=
  d_algI hΓ (d_sumAlgB (.cons hΓ))

/-- `case r {inj₁ u. u | inj₂ p. let (rn, u) = p in u; free rn to n. freeNat n}`. -/
def freeCAlgB : Expr :=
  .case (.var 0) (.var 0) (.letpair (.var 0) (.seq (.var 0)
    (bindE (.app (.val (.prim .free)) (.var 1)) (.app freeNatE (.var 0)))))

def freeCAlgV : Val := .lam freeCAlgB

theorem d_freeCAlg {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ (.val freeCAlgV) (.val (algOTy clistF .unit)) := by
  refine d_algO hΓ (.sumE (A := .unit) (B := .tensor (.ref natN) .unit) (.left (deadSplit hΓ))
    (.var (.here hΓ)) (.ret (.var (.here (.cons hΓ)))) ?_)
  have G2 : Ctx.Dead (⟨VTy.tensor (.ref natN) .unit, false⟩ ::
      ⟨clistF.resO .unit, false⟩ :: Γ) := .cons (.cons hΓ)
  refine .tensorE (A := .ref natN) (B := .unit) (.left (.dead (deadSplit hΓ)))
    (.var (.here (.cons hΓ))) ?_
  refine .unitE (.left (.right (deadSplit G2))) (.var (.here (.cons G2))) ?_
  exact .bind (A := natN) (.dead (.left (deadSplit G2)))
    (.ret (.lolliE (.dead (.left (deadSplit G2))) (.var (.there (.here G2)))
      (.free (.cons (.cons G2)))))
    (.ret (.lolliE (.left (.dead (.dead (deadSplit G2)))) (.var (.here (.cons (.cons G2))))
      (d_freeNat (.cons (.cons (.cons G2))))))

/-- `case r {inj₁ u. inj₁ u | inj₂ p. let (rn, t) = p in free rn to n. inj₂ (n, t)}`. -/
def tpCAlgB : Expr :=
  .case (.var 0) (.inj₁ (.var 0)) (.letpair (.var 0)
    (bindE (.app (.val (.prim .free)) (.var 1)) (.inj₂ (.pair (.var 0) (.var 1)))))

def tpCAlgV : Val := .lam tpCAlgB

theorem d_tpCAlg {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ (.val tpCAlgV) (.val (algOTy clistF pureL)) := by
  refine d_algO hΓ (.sumE (A := .unit) (B := .tensor (.ref natN) pureL) (.left (deadSplit hΓ))
    (.var (.here hΓ))
    (.ret (.roll pureBody_noMut pureL_closed (.sumI₁ (.var (.here (.cons hΓ)))))) ?_)
  have G2 : Ctx.Dead (⟨VTy.tensor (.ref natN) pureL, false⟩ ::
      ⟨clistF.resO pureL, false⟩ :: Γ) := .cons (.cons hΓ)
  refine .tensorE (A := .ref natN) (B := pureL) (.left (.dead (deadSplit hΓ)))
    (.var (.here (.cons hΓ))) ?_
  exact .bind (A := natN) (.right (.left (deadSplit G2)))
    (.ret (.lolliE (.dead (.left (deadSplit G2))) (.var (.there (.here G2)))
      (.free (.cons (.cons G2)))))
    (.ret (.roll pureBody_noMut pureL_closed (.sumI₂ (.tensorI (.left (.right (.dead (deadSplit G2))))
      (.var (.here (.cons (.cons G2)))) (.var (.there (.here (.cons G2))))))))

/-- `case r {inj₁ u. inj₁ u | inj₂ p. let (rn, t) = p in free rn to n. consC (n + 1) t}`: the
incremented node in a fresh block. -/
def mapCAlgB : Expr :=
  .case (.var 0) (.inj₁ (.var 0)) (.letpair (.var 0)
    (bindE (.app (.val (.prim .free)) (.var 1)) (consC (.inj₂ (.var 0)) (.var 1))))

def mapCAlgV : Val := .lam mapCAlgB

theorem d_mapCAlg {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ (.val mapCAlgV) (.val (algOTy clistF clistL)) := by
  refine d_algO hΓ (.sumE (A := .unit) (B := .tensor (.ref natN) clistL) (.left (deadSplit hΓ))
    (.var (.here hΓ))
    (.ret (.roll (FShape.noMut_ty clistF_WF) (FShape.Cl_ty clistF_WF)
      (.sumI₁ (.var (.here (.cons hΓ)))))) ?_)
  have G2 : Ctx.Dead (⟨VTy.tensor (.ref natN) clistL, false⟩ ::
      ⟨clistF.resO clistL, false⟩ :: Γ) := .cons (.cons hΓ)
  refine .tensorE (A := .ref natN) (B := clistL) (.left (.dead (deadSplit hΓ)))
    (.var (.here (.cons hΓ))) ?_
  exact .bind (A := natN) (.right (.left (deadSplit G2)))
    (.ret (.lolliE (.dead (.left (deadSplit G2))) (.var (.there (.here G2)))
      (.free (.cons (.cons G2)))))
    (.ret (d_consC (.left (.right (.dead (deadSplit G2)))) (.left (.left (.dead (deadSplit G2))))
      (.cons (.cons (.cons G2)))
      (.roll natBody_noMut natN_closed (.sumI₂ (.var (.here (.cons (.cons G2.toP))))))
      (.var (.there (.here (.cons G2.toP))))))

/-! ### The folds, by the rules -/

/-- `foldImm sumAlg`, the borrowed sum. -/
def sumCE : Expr := .app (.val (foldImmV clistF)) (.val sumAlgV)

theorem d_sumC {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives LifeCtx.empty Γ sumCE (.val (fTy clistL natN)) :=
  .lolliE (deadSplit hΓ) (d_sumAlg hΓ)
    (.foldImm clistF 0 LifeCtx.empty.meetOfDom natN hΓ clistF_WF trivial
      (by simp [VFree, FShape.ty, natN, natBody]) (by simp [VFree, natN, natBody]) natN_outlives)

/-- **The borrowed sum's semantic type, from the Fundamental Property.** -/
theorem sumC_semV : SemV LifeCtx.empty [] sumCE (fTy clistL natN) := fundamentalC (d_sumC .nil)

/-- `foldOwn freeCAlg`. -/
def freeCE : Expr := .app (.val (foldOwnV clistF)) (.val freeCAlgV)

theorem d_freeC {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ freeCE (.val (.lolli clistL .unit)) :=
  .bangE (.lolliE (deadSplit hΓ) (d_freeCAlg hΓ) (.foldOwn clistF .unit hΓ clistF_WF trivial))

/-- `foldOwn tpCAlg`. -/
def toPureCE : Expr := .app (.val (foldOwnV clistF)) (.val tpCAlgV)

theorem d_toPureC {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ toPureCE (.val (.lolli clistL pureL)) :=
  .bangE (.lolliE (deadSplit hΓ) (d_tpCAlg hΓ) (.foldOwn clistF pureL hΓ clistF_WF trivial))

/-- **`toPure`'s semantic type, from the Fundamental Property.** -/
theorem toPureC_semV : SemV LifeCtx.empty [] toPureCE (.lolli clistL pureL) :=
  fundamentalC (d_toPureC .nil)

/-- `foldOwn mapCAlg`. -/
def mapIncCE : Expr := .app (.val (foldOwnV clistF)) (.val mapCAlgV)

theorem d_mapIncC {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ mapIncCE (.val (.lolli clistL clistL)) :=
  .bangE (.lolliE (deadSplit hΓ) (d_mapCAlg hΓ) (.foldOwn clistF clistL hΓ clistF_WF trivial))

/-- **`mapInc`'s semantic type, from the Fundamental Property.** -/
theorem mapIncC_semV : SemV LifeCtx.empty [] mapIncCE (.lolli clistL clistL) :=
  fundamentalC (d_mapIncC .nil)

/-! ### The sum, inside an immutable borrow -/

/-- Build `[1, 2, 3]` node by node as blocks, borrow it, sum it with `foldImm sumAlg`, end the
borrow, free it with `foldOwn freeCAlg`. -/
def sumProg : Expr := foldProg freeCE sumCE buildC

theorem sumProg_derives : CDerives LifeCtx.empty [] sumProg (.comp (.ret natN)) :=
  d_foldProg (d_freeC .nil) (d_sumC (.cons .nil)) (fun hΓ => d_buildList hΓ _)
    (fun _ => by simp [VFree, FShape.ty, natN, natBody]) (fun _ => by simp [VFree, natN, natBody])
    natN_outlives rfl

/-- **Adequacy at the derived sum**: from the empty memory to a numeral and the empty memory. -/
theorem sumProg_runs :
    ∃ k, BoCa.BoLo.Steps Adequacy.emptyMem sumProg Adequacy.emptyMem (.val (num k)) := by
  have hwp : wpTS [] sumProg (fun _ v => Fig16.BoLo.pure (∃ k, v = num k))
      (PMap.empty : WRes) := by
    refine wpTS_mono (fun _ v ρ hv => ?_) PMap.empty (wp_of_derives sumProg_derives)
    obtain ⟨rfl, k, rfl⟩ := vC_natN hv
    exact ⟨rfl, k, rfl⟩
  obtain ⟨v, hsteps, k, rfl⟩ := theorem32 sumProg (fun v => ∃ k, v = num k) hwp
  exact ⟨k, hsteps⟩

set_option maxRecDepth 100000 in
theorem sumProg_eval : numNoLeak (eval sumProg) = some 6 := by decide

/-! ### The map, inside a mutable borrow -/

theorem d_borrowerMC :
    CDerives LifeCtx.empty [⟨.ref clistL, false⟩, ⟨clistL, false⟩, ⟨.lolli clistL clistL, true⟩,
      ⟨.lolli clistL pureL, false⟩] borrowerM
      (.val (VTy.all 0 LifeCtx.empty.meetOfDom (.lolli (.mut (.var 0) clistL) (.box (.var 0) .unit)))) := by
  refine .thunkV rfl (.allI (S := .unit) rfl
    (fun _ _ hy => LifeCtx.Ok.bound_mentions_false ok_empty rfl hy) ?_
    (.ret (.thunkV rfl (.lam ?_))))
  · intro s hs hl
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · exact absurd hl (by simp)
    · exact absurd hl (by simp)
    · simp [VFree, CFree, FShape.ty, natN, natBody]
    · exact absurd hl (by simp)
  refine .bind (A := .tensor (.mut (.var 0) clistL) .unit)
    (.left (.dead (.dead (.dead (.left (.dead .nil)))))) ?_ ?_
  · refine .ret (.lolliE (.right (.dead (.dead (.dead (.left (.dead .nil)))))) ?_
      (.lolliE (.left (.dead (.dead (.dead (.dead (.dead .nil))))))
        (.var (.here (by repeat constructor)))
        (.withswap (a := .var 0) (A := clistL) (B := .unit) (by repeat constructor))))
    refine .thunkV rfl (.lam (.bind (A := clistL) (.left (.dead (.dead (.dead (.dead (.left (.dead .nil))))))) ?_ ?_))
    · exact .ret (.lolliE (.left (.dead (.dead (.dead (.dead (.right (.dead .nil)))))))
        (.var (.here (by repeat constructor)))
        (.var (.there (.there (.there (.there (.there (.here (by repeat constructor)))))))))
    · exact .ret (.tensorI (.left (.dead (.dead (.dead (.dead (.dead (.dead (.dead .nil))))))))
        (.var (.here (by repeat constructor))) (.unitI (by repeat constructor)))
  · refine .tensorE (A := .mut (.var 0) clistL) (B := .unit)
      (.left (.dead (.dead (.dead (.dead (.dead (.dead .nil))))))) (.var (.here (by repeat constructor))) ?_
    refine .unitE (.left (.right (.dead (.dead (.dead (.dead (.dead (.dead (.dead .nil)))))))))
      (.var (.here (by repeat constructor))) ?_
    refine .unitE (.dead (.left (.dead (.dead (.dead (.dead (.dead (.dead (.dead .nil)))))))))
      (.lolliE (.dead (.left (.dead (.dead (.dead (.dead (.dead (.dead (.dead .nil)))))))))
        (.var (.there (.here (by repeat constructor))))
        (.forgetMut (a := .var 0) (A := clistL) (by repeat constructor))) ?_
    exact .ret (.boxI (.unitI (by repeat constructor))
      ⟨LifeCtx.defines_of_wf rfl, dead_noLive (by repeat constructor)⟩)

/-- The program, open in `mapInc` (index `0`) and `toPure` (index `1`): `MapMut.lean`'s
`mapProgOpen` at the list of blocks.

    buildC0 to lst. alloc lst to r.
    withbor r (Λ. λb. withswap b (λl. mapInc l to l′. (l′, ())) to q.
                     let (b′, u) = q in u; forget b′; ()) to p.
    let (r′, u) = p in u; free r′ to lst′. toPure lst′                                   -/
def mapProgOpenC : Expr :=
  bindE buildC0 (bindE (.app (.val (.prim .alloc)) (.var 0))
    (bindE (.app (.app withbor (.var 0)) borrowerM)
      (.letpair (.var 0) (.seq (.var 0)
        (bindE (.app (.val (.prim .free)) (.var 1)) (.app (.var 7) (.var 0)))))))

/-- The context of `mapInc` and `toPure`. -/
abbrev ΓMC : Ctx VTy := [⟨.lolli clistL clistL, true⟩, ⟨.lolli clistL pureL, true⟩]

theorem mapProgOpenC_derives : CDerives LifeCtx.empty ΓMC mapProgOpenC (.comp (.ret pureL)) := by
  refine .bind (.right (.right .nil)) (.ret (d_buildList (by repeat constructor) _)) ?_
  refine .bind (.left (.right (.right .nil)))
    (.ret (.lolliE (.left (.dead (.dead .nil))) (.var (.here (by repeat constructor)))
      (.alloc (A := clistL) (by repeat constructor)))) ?_
  refine .bind (.left (.dead (.left (.right .nil))))
    (.ret (.lolliE (.right (.dead (.left (.dead .nil)))) d_borrowerMC
      (.lolliE (.left (.dead (.dead (.dead .nil)))) (.var (.here (by repeat constructor)))
        (.withbor2 (A := clistL) (B := .unit) 0 (by repeat constructor) rfl
          ⟨LifeCtx.empty.meetOfDom, LifeCtx.defines_of_wf rfl, clistL_outlives _ _⟩
          (by simp [VFree, FShape.ty, natN, natBody]) (by simp [VFree]))))) ?_
  refine .tensorE (A := .ref clistL) (B := .unit) (.left (.dead (.dead (.dead (.right .nil)))))
    (.var (.here (by repeat constructor))) ?_
  refine .unitE (.left (.right (.dead (.dead (.dead (.dead (.right .nil)))))))
    (.var (.here (by repeat constructor))) ?_
  refine .bind (.dead (.left (.dead (.dead (.dead (.dead (.right .nil)))))))
    (.ret (.lolliE (.dead (.left (.dead (.dead (.dead (.dead (.dead .nil)))))))
      (.var (.there (.here (by repeat constructor)))) (.free (A := clistL) (by repeat constructor)))) ?_
  exact .ret (.lolliE (.left (.dead (.dead (.dead (.dead (.dead (.dead (.right .nil))))))))
    (.var (.here (by repeat constructor)))
    (.var (.there (.there (.there (.there (.there (.there (.there (.here .nil))))))))))

/-- The closed program: `toPure to t. mapInc to m. mapProgOpenC`. -/
def mapProgC : Expr := bindE toPureCE (bindE mapIncCE mapProgOpenC)

theorem mapProgC_derives : CDerives LifeCtx.empty [] mapProgC (.comp (.ret pureL)) :=
  .bind .nil (.ret (d_toPureC .nil))
    (.bind (.right .nil) (.ret (d_mapIncC (.cons .nil))) mapProgOpenC_derives)

/-- **Adequacy at the derived map**: from the empty memory to a pure list and the empty
memory. -/
theorem mapProgC_runs :
    ∃ v, PureOut v ∧ BoCa.BoLo.Steps Adequacy.emptyMem mapProgC Adequacy.emptyMem (.val v) := by
  have hwp : wpTS [] mapProgC (fun _ v => Fig16.BoLo.pure (PureOut v)) (PMap.empty : WRes) := by
    refine wpTS_mono (fun ls v ρ hv => ?_) PMap.empty (wp_of_derives mapProgC_derives)
    have e := vC_pureL_empty (sizeOf v.1 + 1) (Nat.lt_succ_self _) hv
    subst e
    exact ⟨rfl, true, ls, LSub.empty, hv⟩
  obtain ⟨v, hsteps, hv⟩ := theorem32 mapProgC PureOut hwp
  exact ⟨v, hv, hsteps⟩

set_option maxRecDepth 100000 in
theorem mapProgC_eval : pureNoLeak (eval mapProgC) = some [1, 1, 1] := by decide

/-! ### Each node is one block -/

/-- **A node is allocated as one block, on some run**: at every frame the typed world admits, on
the run that places the node's cells consecutively, `allocS nodeC` returns the handle
`(ℓ, ℓ + 1)` of two adjacent cells, of type `Ref N ⊗ Ref L`.  `[spec §13]` -/
theorem consC_block {ls : List SRec} {δ : LSub} {v : Val} {ρ : WRes}
    (hv : vP nodeC.valTy ls δ v ρ) :
    wpTSAngelic ls (.app (allocS nodeC) v.1)
      (fun ls' w => fun ρ' => ∃ b, w = .pair (.loc b) (.loc (b + 1)) ∧
        vP (.tensor (.ref natN) (.ref clistL)) ls' δ w ρ') ρ :=
  wpTSAngelic_mono (fun _ _ _ ⟨b, hw, h⟩ => ⟨b, hw, h⟩) ρ (wpTSAngelic_allocS nodeC hv)

/-- The interpreter's run, returning the value and the memory. -/
def runMem : Nat → BoCa.Mem → Expr → Option (Val × BoCa.Mem)
  | 0, _, _ => none
  | n + 1, μ, e =>
    match BoCa.step wasmHost μ e with
    | .value v => some (v, μ)
    | .next μ' e' => runMem n μ' e'
    | .stuck _ => none
    | .op _ _ _ => none

/-- The payloads of the list `e` in `μ`, when every node is at two adjacent cells `(ℓ, ℓ + 1)`
holding the payload and the tail. -/
def blockNodes : Nat → BoCa.Mem → Expr → Option (List Nat)
  | 0, _, _ => none
  | _ + 1, _, .inj₁ .unit => some []
  | n + 1, μ, .inj₂ (.pair (.loc a) (.loc b)) =>
      if b = a + 1 then do
        let x ← μ.get? a
        let k ← numOf x.1
        let t ← μ.get? b
        let ks ← blockNodes n μ t.1
        pure (k :: ks)
      else none
  | _, _, _ => none

/-- Run `e` and read the list it returns node by node, as blocks. -/
def blocksOf (e : Expr) : Option (List Nat) := do
  let (v, μ) ← runMem 2000 BoCa.Mem.empty e
  blockNodes 100 μ v.1

set_option maxRecDepth 100000 in
/-- The interpreter builds `[1, 2, 3]` with every node one block. -/
theorem buildC_blocks : blocksOf buildC = some [1, 2, 3] := by decide

set_option maxRecDepth 100000 in
/-- After `mapInc`, every node is again one block. -/
theorem mapIncC_blocks : blocksOf (bindE buildC0 (.app mapIncCE (.var 0))) = some [1, 1, 1] := by
  decide

end BoCa.Fig16.LogRel.Core

end
