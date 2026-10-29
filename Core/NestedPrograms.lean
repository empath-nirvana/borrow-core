import Core.ArrayPrograms

/-!
# Core — a value nested three deep, walked by the general owned fold and dropped  `[spec §6, §12]`

The type `T = μX. I32 ⊗ Array (μY. 1 ⊕ (Ref X ⊗ Ref Y))`: a node holds an integer and an array
of chains of children, each chain a `μ` inside the array inside the outer `μ`. It is outside
`FShape` (`nodeB_not_FShape`) and in `P` (`nodeB_P`); its keys are the root, the array and the
inner `μ` (`keys_nodeB`), one algebra each.

    t₁ ← build;  t₂ ← build;      -- 1 with the children 10, 11, 12, each in a chain of one
    s ← foldOwnG (add, sum, sum) t₁;
    dtor T t₂;                    -- the derived destructor (SPEC §12): `foldOwnG` at results 1
    s

One closed `CDerives` derivation (`nestProg_derives`); it runs by adequacy at every host
(`nestProg_runs`), and by the interpreter at `wasmHost` to `34`, the sum of the four integers,
with no cell left (`nestProg_eval`, kernel-checked by `decide`). It is the kernel program
`nested-fold` of `Backend/Kernel.lean`. A node with no children has an empty array (`tab` of length `0`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Nested
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### The type -/

/-- The inner body `1 ⊕ (Ref X ⊗ Ref Y)`: `Y` is variable `0`, `X` variable `1`. -/
abbrev chainB : VTy := .sum .unit (.tensor (.ref (.tvar 1)) (.ref (.tvar 0)))

/-- The body `I32 ⊗ Array (μY. 1 ⊕ (Ref X ⊗ Ref Y))`. -/
abbrev nodeB : VTy := .tensor .i32 (.fam (.ref (.mu chainB)))

/-- `T = μX. I32 ⊗ Array (μY. 1 ⊕ (Ref X ⊗ Ref Y))`. -/
abbrev nodeT : VTy := .mu nodeB

/-- The chain body at `X = T`. -/
abbrev chainTB : VTy := .sum .unit (.tensor (.ref nodeT) (.ref (.tvar 0)))

/-- A chain of children, closed: `μY. 1 ⊕ (Ref T ⊗ Ref Y)`. -/
abbrev chainT : VTy := .mu chainTB

theorem nodeT_unroll : VTy.inst nodeT nodeB = .tensor .i32 (.fam (.ref chainT)) := rfl

theorem chainT_unroll : VTy.inst chainT chainTB = .sum .unit (.tensor (.ref nodeT) (.ref chainT)) :=
  rfl

theorem nodeB_P : FoldP.PBody nodeB := by decide

theorem nodeB_not_FShape : ¬ (toFShape nodeB).WF := by
  simp [toFShape, FShape.WF, VTy.Cl]

theorem nodeB_fshape : fshapeB nodeB = false := by decide

/-- The keys: the root, the array of chains, the inner `μ`. -/
theorem keys_nodeB : FoldP.keys nodeB =
    [.mu [nodeB], .arr [nodeB] (.mu chainB), .mu [chainB, nodeB]] := by decide

theorem nodeB_noMut : nodeB.NoMut 0 := by simp [VTy.NoMut]
theorem nodeT_closed : nodeT.Cl 0 := by simp [VTy.Cl]
theorem chainTB_noMut : chainTB.NoMut 0 := by simp [VTy.NoMut]
theorem chainT_closed : chainT.Cl 0 := by simp [VTy.Cl]

/-! ### Building -/

/-- `inj₁ ()`, the empty chain. -/
def emptyChainE : Expr := .inj₁ (.val .unit)

/-- `λi. inj₁ ()`: the tabulator of an array of empty chains. -/
def emptyGenV : Val := .lam emptyChainE

/-- `(n, tab (0, λi. inj₁ ()))`: a node with no children. -/
def leafE (n : Expr) : Expr :=
  .pair n (.app (.val (.prim .tab)) (.pair (i32E 0) (.val emptyGenV)))

/-- `inj₂ (alloc t, alloc (inj₁ ()))`: a chain of the one child `t`. -/
def oneChainE (t : Expr) : Expr :=
  .inj₂ (.pair (.app (.val (.prim .alloc)) t) (.app (.val (.prim .alloc)) emptyChainE))

/-- `λi. inj₂ (alloc (i + 10, []), alloc (inj₁ ()))`: the tabulator of the root's children. -/
def childGenV : Val := .lam (oneChainE (leafE (hop (.bin .w32 .add) (.pair (.var 0) (i32E 10)))))

/-- The root `(1, tab (3, childGenV))`. -/
def buildE : Expr := .pair (i32E 1) (.app (.val (.prim .tab)) (.pair (i32E 3) (.val childGenV)))

section
variable {Γ : Ctx VTy}

theorem d_emptyChain (hΓ : Ctx.DeadP Γ) : CDerives LifeCtx.empty Γ emptyChainE (.val chainT) :=
  .roll chainTB_noMut chainT_closed (.sumI₁ (.unitI hΓ))

theorem d_emptyGen (hΓ : Ctx.Dead Γ) :
    CDerives LifeCtx.empty Γ (.val emptyGenV) (.val (.bang (.lolli .i32 chainT))) :=
  .bangThunkV (persistent_dead hΓ) rfl (.lam (.ret (d_emptyChain (.drop rfl hΓ.toP))))

/-- `tab (0, λi. inj₁ ())`, at a dead context. -/
theorem d_emptyKids (hΓ : Ctx.Dead Γ) :
    CDerives LifeCtx.empty Γ (.app (.val (.prim .tab)) (.pair (i32E 0) (.val emptyGenV)))
      (.val (.fam (.ref chainT))) :=
  .lolliE (deadSplit hΓ) (.tensorI (deadSplit hΓ) (d_i32 0 hΓ.toP) (d_emptyGen hΓ))
    (.bangE (.arrNew chainT hΓ.toP))

/-- A node with no children, its integer typed at the one live slot. -/
theorem d_leaf {A : VTy} {n : Expr} (hΓ : Ctx.Dead Γ)
    (hn : CDerives LifeCtx.empty (⟨A, true⟩ :: Γ) n (.val .i32)) :
    CDerives LifeCtx.empty (⟨A, true⟩ :: Γ) (leafE n) (.val nodeT) := by
  refine .roll nodeB_noMut nodeT_closed ?_
  rw [nodeT_unroll]
  exact .tensorI (.left (deadSplit hΓ)) hn (d_emptyKids (.cons hΓ))

/-- A chain of one child, the child typed at the one live slot. -/
theorem d_oneChain {A : VTy} {t : Expr} (hΓ : Ctx.Dead Γ)
    (ht : CDerives LifeCtx.empty (⟨A, true⟩ :: Γ) t (.val nodeT)) :
    CDerives LifeCtx.empty (⟨A, true⟩ :: Γ) (oneChainE t) (.val chainT) := by
  refine .roll chainTB_noMut chainT_closed ?_
  rw [chainT_unroll]
  refine .sumI₂ (.tensorI (.left (deadSplit hΓ)) ?_ ?_)
  · exact .lolliE (.left (deadSplit hΓ)) ht (.alloc (Ctx.Dead.cons hΓ).toP)
  · exact .lolliE (deadSplit (.cons hΓ)) (d_emptyChain (Ctx.Dead.cons hΓ).toP)
      (.alloc (Ctx.Dead.cons hΓ).toP)

theorem d_childGen (hΓ : Ctx.Dead Γ) :
    CDerives LifeCtx.empty Γ (.val childGenV) (.val (.bang (.lolli .i32 chainT))) := by
  refine .bangThunkV (persistent_dead hΓ) rfl (.lam (.ret ?_))
  refine d_oneChain hΓ (d_leaf hΓ ?_)
  exact .lolliE (.left (deadSplit hΓ))
    (.tensorI (.left (deadSplit hΓ)) (.var (.here hΓ.toP)) (d_i32 10 (Ctx.Dead.cons hΓ).toP))
    (.bangE (.hostOp _ (Ctx.Dead.cons hΓ).toP))

theorem d_build (hΓ : Ctx.Dead Γ) : CDerives LifeCtx.empty Γ buildE (.val nodeT) := by
  refine .roll nodeB_noMut nodeT_closed ?_
  rw [nodeT_unroll]
  exact .tensorI (deadSplit hΓ) (d_i32 1 hΓ.toP)
    (.lolliE (deadSplit hΓ) (.tensorI (deadSplit hΓ) (d_i32 3 hΓ.toP) (d_childGen hΓ))
      (.bangE (.arrNew chainT hΓ.toP)))

end

/-! ### The fold -/

/-- `λp. let (a, b) = p in a + b`: the root's algebra, `I32 ⊗ I32 ⊸ I32`. -/
def addAlgV : Val := .lam (.letpair (.var 0) (hop (.bin .w32 .add) (.pair (.var 1) (.var 0))))

/-- `λx. case x {inj₁ u. 0 | inj₂ p. let (a, b) = p in a + b}`: the algebra of the array and of
the inner `μ`, `1 ⊕ (I32 ⊗ I32) ⊸ I32`. -/
def sumAlgV : Val := .lam (.case (.var 0) (i32E 0)
  (.letpair (.var 0) (hop (.bin .w32 .add) (.pair (.var 1) (.var 0)))))

/-- The three results, in the order of the keys. -/
abbrev nestRs : List VTy := [.i32, .i32, .i32]

theorem nest_algsTy : FoldP.algsTy nodeB nestRs =
    .tensor (.bang (.lolli (.tensor .i32 .i32) .i32))
      (.tensor (.bang (.lolli (.sum .unit (.tensor .i32 .i32)) .i32))
        (.bang (.lolli (.sum .unit (.tensor .i32 .i32)) .i32))) := by decide

theorem nest_res : (FoldP.algsOf (FoldP.keys nodeB) nestRs).Res [nodeB] = .i32 := by decide

section
variable {Γ : Ctx VTy}

/-- `a + b` at the two live slots `b, a` above a dead one. -/
theorem d_addBody {T : VTy} (hΓ : Ctx.Dead Γ) :
    CDerives LifeCtx.empty (⟨.i32, true⟩ :: ⟨.i32, true⟩ :: ⟨T, false⟩ :: Γ)
      (hop (.bin .w32 .add) (.pair (.var 1) (.var 0))) (.val .i32) :=
  .lolliE (.left (.left (.dead (deadSplit hΓ))))
    (.tensorI (.right (.left (.dead (deadSplit hΓ))))
      (.var (.there (.here (Ctx.Dead.cons hΓ).toP))) (.var (.here (.cons (Ctx.Dead.cons hΓ).toP))))
    (.bangE (.hostOp _ (Ctx.Dead.cons (Ctx.Dead.cons (Ctx.Dead.cons hΓ))).toP))

theorem d_addAlg (hΓ : Ctx.Dead Γ) :
    CDerives LifeCtx.empty Γ (.val addAlgV) (.val (.bang (.lolli (.tensor .i32 .i32) .i32))) :=
  d_algO hΓ (.ret (.letpairV (.left (deadSplit hΓ)) (.var (.here hΓ.toP)) (d_addBody hΓ)))

theorem d_sumAlg (hΓ : Ctx.Dead Γ) :
    CDerives LifeCtx.empty Γ (.val sumAlgV)
      (.val (.bang (.lolli (.sum .unit (.tensor .i32 .i32)) .i32))) :=
  d_algO hΓ (.ret (.caseV (.left (deadSplit hΓ)) (.var (.here hΓ.toP))
    (d_i32 0 (.drop rfl (Ctx.Dead.cons hΓ).toP))
    (.letpairV (.left (deadSplit (.cons hΓ))) (.var (.here (Ctx.Dead.cons hΓ).toP))
      (d_addBody (.cons hΓ)))))

/-- `foldOwnG (add, (sum, sum))`: the sum of a tree's integers. -/
def nestSumE : Expr :=
  .app (.val (FoldP.foldOwnGV nodeB)) (.pair (.val addAlgV) (.pair (.val sumAlgV) (.val sumAlgV)))

theorem d_nestSum (hΓ : Ctx.Dead Γ) :
    CDerives LifeCtx.empty Γ nestSumE (.val (.lolli nodeT .i32)) := by
  have h := CDerives.lolliE (deadSplit hΓ)
    (.tensorI (deadSplit hΓ) (d_addAlg hΓ) (.tensorI (deadSplit hΓ) (d_sumAlg hΓ) (d_sumAlg hΓ)))
    (.foldOwnG (Δ := LifeCtx.empty) nodeB nestRs hΓ.toP nodeB_P)
  simp only [nest_res] at h
  exact .bangE h

end

/-! ### The program -/

theorem keysIn_nodeB : FoldP.keysIn [nodeB] nodeB = [.arr [nodeB] (.mu chainB), .mu [chainB, nodeB]] := by
  decide

/-- `T` has a destructor: `foldOwnG` at results `1`. -/
theorem nodeT_hasDtor : HasDtor nodeT := by
  refine .mu nodeB_P ?_ (fun B Bs hm => ?_) (fun Bs S hm => ?_)
  · have e : FoldP.resO dtorAlgs [nodeB] nodeB = .tensor .i32 .unit := by decide
    rw [e]; exact .tensor .int .unit
  · rw [keysIn_nodeB] at hm
    simp only [List.mem_cons, reduceCtorEq, FoldP.Bnd.mu.injEq, List.cons.injEq, List.not_mem_nil,
      false_or, or_false] at hm
    obtain ⟨rfl, rfl⟩ := hm
    have e : FoldP.resO dtorAlgs [chainB, nodeB] chainB = .sum .unit (.tensor .unit .unit) := by
      decide
    rw [e]; exact .sum .unit (.tensor .unit .unit)
  · rw [keysIn_nodeB] at hm
    simp only [List.mem_cons, reduceCtorEq, FoldP.Bnd.arr.injEq, List.not_mem_nil, or_false] at hm
    obtain ⟨rfl, rfl⟩ := hm
    have e : FoldP.resO dtorAlgs [nodeB] (.mu chainB) = .unit := by decide
    rw [e]; exact .unit

/-- The program. -/
def nestProg : Expr :=
  bindE buildE (bindE buildE
    (bindE (.app nestSumE (.var 1)) (.seq (.app (dtorE nodeT) (.var 1)) (.var 0))))

theorem nestProg_derives : CDerives LifeCtx.empty [] nestProg (.comp (.ret .i32)) := by
  refine .ret (bindP (A := nodeT) (d_build (by cdead)) ?_)
  refine bindP (A := nodeT) (d_build (by cdead)) ?_
  refine bindP (A := .i32) (appP (.var (by csoloP)) (d_nestSum (by cdead))) ?_
  refine .seqV (partP_split (.app (dtorE nodeT) (.var 1)) 0 _) ?_ (.var (by csoloP))
  exact .lolliE (split_kill' _).toP (.var (by csoloP)) (dtor_wf nodeT_hasDtor (kill_dead _))

/-- **The program runs at every host**: from the empty memory to a 32-bit literal and the
empty memory: every cell the two trees hold is freed, by the fold and by the destructor. -/
theorem nestProg_runs :
    ∃ n, BoCa.BoLo.Steps Adequacy.emptyMem nestProg Adequacy.emptyMem (.val (Val.i32 n)) := by
  have hwp : wpTS [] nestProg (fun _ v => Fig16.BoLo.pure (∃ n, v = Val.i32 n))
      (PMap.empty : WRes) := by
    refine wpTS_mono (fun _ v ρ hv => ?_) PMap.empty (wp_of_derives nestProg_derives)
    obtain ⟨rfl, n, rfl⟩ := hv
    exact ⟨rfl, n, rfl⟩
  obtain ⟨v, hsteps, n, rfl⟩ := theorem32 nestProg (fun v => ∃ n, v = Val.i32 n) hwp
  exact ⟨n, hsteps⟩

set_option maxRecDepth 100000 in
/-- The interpreter at Wasm's host: `34`, the sum of the four integers, and no cell left. -/
theorem nestProg_eval : i32NoLeak (run wasmHost 1500 Mem.empty nestProg) = some 34 := by decide

end BoCa.Fig16.LogRel.Core.Nested

end
