import Core.CommonList

/-!
# Core — the in-place map over the common list shape, by the fold with reuse  `[spec §6]`

Over the common list `μX. 1 ⊕ (Ref E ⊗ Ref X)` (`CommonList.lean`, each node one block),
`foldReuse` hands the algebra, at a cons node, the value leaf `Ref E`, the emptied next leaf
`Ref 1` and the mapped tail.  Two closed derived functions do the reuse:

* `take : Ref A ⊸ F (Ref 1 ⊗ A)`, `λr. swap r ()`: empties a cell;
* `fill : Ref 1 ⊗ A ⊸ F (Ref A)`, `λp. let (c, x) = p in swap c x to q. let (c′, u) = q in u; c′`:
  refills an emptied cell at any type.

`mapRAlg f` takes the value leaf, applies `f : E ⊸ F E′` to its content and fills the same leaf,
and fills the emptied next leaf with the mapped tail.  So `foldReuse (mapRAlg f)` is a map
`L_E ⊸ F L_E′` that allocates nothing and frees nothing.

* `mapIncRE = foldReuse (mapRAlg inc) : U(L ⊸ F L)` (`mapIncR_semV`, by `fundamentalC`).
* `mapProgR`: `MapMut.lean`'s program (build `[0, 0, 0]`, borrow mutably, `withswap` and the
  map, end, free the cell, `toPure`) with `mapIncRE`, one closed derivation; it runs to a pure
  list and the empty memory (`mapProgR_runs`), and the interpreter returns `[1, 1, 1]` with no
  cell left (`mapProgR_eval`).
* **In place**: `mapIncR_inPlace`: the interpreter's list after `mapIncRE` has its nodes at the
  addresses the built list had; `mapIncC_moves`: after `foldOwn`'s `mapIncCE` it does not.
* **Changing the element type**: `isZeroRE = foldReuse (mapRAlg isZero) : U(L_N ⊸ F L_B)`
  (`isZeroR_semV`), and `isZeroR_inPlace`: the booleans are in the numerals' cells.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- Close a context-split, `Solo` or `Dead` goal whose contexts are fixed, over a dead tail. -/
local macro "ctx" : tactic =>
  `(tactic| repeat (first | assumption | exact deadSplit (by assumption) | constructor))

/-! ### The shape at any element type -/

/-- `1 ⊕ (Ref E ⊗ Ref X)`. -/
abbrev clistFE (E : VTy) : FShape := .sum (.leaf .unit) (.tensor (.leaf (.ref E)) .refX)

/-- `L_E = μX. 1 ⊕ Ref (E ⊗ X)`, each node a block. -/
abbrev clistLE (E : VTy) : VTy := .mu (clistFE E).ty

theorem clistFE_WF {E : VTy} (hE : E.Cl 0) : (clistFE E).WF := by
  simp [FShape.WF, VTy.Cl, hE]

theorem clistLE_nat : clistLE natN = clistL := rfl

/-- The algebra's domain at a cons node: the value leaf, the emptied next leaf, the mapped
tail. -/
theorem clistFE_resR (E R : VTy) :
    (clistFE E).resR R = .sum .unit (.tensor (.ref E) (.tensor (.ref .unit) R)) := rfl

/-! ### `take` and `fill` -/

/-- `take = λr. swap r ()`. -/
def takeV : Val := .lam (.app (.app swap (.var 0)) (.val .unit))

theorem d_take {Δ : LifeCtx} {Γ : Ctx VTy} {A : VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ (.val takeV) (.val (.lolli (.ref A) (.tensor (.ref .unit) A))) :=
  .thunkV rfl (.lam (.ret (.lolliE (Γ₁ := ⟨.ref A, false⟩ :: Γ) (Γ₂ := ⟨.ref A, true⟩ :: Γ)
    (by ctx) (.unitI (.cons hΓ))
    (.lolliE (Γ₁ := ⟨.ref A, true⟩ :: Γ) (Γ₂ := ⟨.ref A, false⟩ :: Γ) (by ctx)
      (.var (.here hΓ)) (.swap (.cons hΓ))))))

/-- `fill = λp. let (c, x) = p in swap c x to q. let (c′, u) = q in u; c′`. -/
def fillB : Expr :=
  .letpair (.var 0) (bindE (.app (.app swap (.var 1)) (.var 0))
    (.letpair (.var 0) (.seq (.var 0) (.var 1))))

def fillV : Val := .lam fillB

theorem d_fill {Δ : LifeCtx} {Γ : Ctx VTy} {A : VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ (.val fillV) (.val (.lolli (.tensor (.ref .unit) A) (.ref A))) := by
  refine .thunkV rfl (.lam ?_)
  refine .tensorE (A := .ref .unit) (B := A) (Γp := ⟨_, true⟩ :: Γ) (Γb := ⟨_, false⟩ :: Γ)
    (by ctx) (.var (.here hΓ)) ?_
  refine .bind (A := .tensor (.ref A) .unit)
    (Γ₁ := ⟨A, true⟩ :: ⟨.ref .unit, true⟩ :: ⟨_, false⟩ :: Γ)
    (Γ₂ := ⟨A, false⟩ :: ⟨.ref .unit, false⟩ :: ⟨_, false⟩ :: Γ) (by ctx) ?_ ?_
  · exact .ret (.lolliE (Γ₁ := ⟨A, true⟩ :: ⟨.ref .unit, false⟩ :: ⟨_, false⟩ :: Γ)
      (Γ₂ := ⟨A, false⟩ :: ⟨.ref .unit, true⟩ :: ⟨_, false⟩ :: Γ) (by ctx)
      (.var (.here (.cons (.cons hΓ))))
      (.lolliE (Γ₁ := ⟨A, false⟩ :: ⟨.ref .unit, true⟩ :: ⟨_, false⟩ :: Γ)
        (Γ₂ := ⟨A, false⟩ :: ⟨.ref .unit, false⟩ :: ⟨_, false⟩ :: Γ) (by ctx)
        (.var (.there (.here (.cons hΓ)))) (.swap (.cons (.cons (.cons hΓ))))))
  · refine .tensorE (A := .ref A) (B := .unit)
      (Γp := ⟨_, true⟩ :: ⟨A, false⟩ :: ⟨.ref .unit, false⟩ :: ⟨_, false⟩ :: Γ)
      (Γb := ⟨_, false⟩ :: ⟨A, false⟩ :: ⟨.ref .unit, false⟩ :: ⟨_, false⟩ :: Γ)
      (by ctx) (.var (.here (.cons (.cons (.cons hΓ))))) ?_
    exact .unitE
      (Γ₁ := ⟨.unit, true⟩ :: ⟨.ref A, false⟩ :: ⟨_, false⟩ :: ⟨A, false⟩ :: ⟨.ref .unit, false⟩ ::
        ⟨_, false⟩ :: Γ)
      (Γ₂ := ⟨.unit, false⟩ :: ⟨.ref A, true⟩ :: ⟨_, false⟩ :: ⟨A, false⟩ :: ⟨.ref .unit, false⟩ ::
        ⟨_, false⟩ :: Γ)
      (by ctx) (.var (.here (.cons (.cons (.cons (.cons (.cons hΓ)))))))
      (.ret (.var (.there (.here (.cons (.cons (.cons (.cons hΓ))))))))

/-! ### The reuse algebra -/

/-- `case r {inj₁ u. inj₁ u | inj₂ p. let (rn, q) = p in let (c, x) = take rn in
inj₂ (fill (c, f x), fill q)}`: the value leaf refilled with `f` of its content, the next leaf
refilled with the mapped tail. -/
def mapRAlgB (f : Val) : Expr :=
  .case (.var 0) (.inj₁ (.var 0))
    (.letpair (.var 0)
      (.letpair (.app (.val takeV) (.var 1))
        (.inj₂ (.pair (.app (.val fillV) (.pair (.var 1) (.app (.val f) (.var 0))))
          (.app (.val fillV) (.var 2))))))

def mapRAlgV (f : Val) : Val := .lam (mapRAlgB f)

theorem d_mapRAlg {Δ : LifeCtx} {Γ : Ctx VTy} {E E' : VTy} {f : Val} (hΓ : Ctx.Dead Γ)
    (hE' : E'.Cl 0)
    (hf : ∀ {Γ : Ctx VTy}, Ctx.Dead Γ → CDerives Δ Γ (.val f) (.val (.lolli E E'))) :
    CDerives Δ Γ (.val (mapRAlgV f)) (.val (algRTy (clistFE E) (clistLE E'))) := by
  have hW := clistFE_WF hE'
  refine d_algO hΓ (.sumE (A := .unit) (B := .tensor (.ref E) (.tensor (.ref .unit) (clistLE E')))
    (Γs := ⟨_, true⟩ :: Γ) (Γb := ⟨_, false⟩ :: Γ) (by ctx) (.var (.here hΓ))
    (.ret (.roll (FShape.noMut_ty hW) (FShape.Cl_ty hW) (.sumI₁ (.var (.here (.cons hΓ))))))
    ?_)
  -- `p` live, `r` dead
  refine .tensorE (A := .ref E) (B := .tensor (.ref .unit) (clistLE E'))
    (Γp := ⟨_, true⟩ :: ⟨_, false⟩ :: Γ) (Γb := ⟨_, false⟩ :: ⟨_, false⟩ :: Γ) (by ctx)
    (.var (.here (.cons hΓ))) ?_
  -- `q` (0), `rn` (1)
  refine .tensorE (A := .ref .unit) (B := E)
    (Γp := ⟨_, false⟩ :: ⟨.ref E, true⟩ :: ⟨_, false⟩ :: ⟨_, false⟩ :: Γ)
    (Γb := ⟨_, true⟩ :: ⟨.ref E, false⟩ :: ⟨_, false⟩ :: ⟨_, false⟩ :: Γ) (by ctx)
    (.lolliE (Γ₁ := ⟨_, false⟩ :: ⟨.ref E, true⟩ :: ⟨_, false⟩ :: ⟨_, false⟩ :: Γ)
      (Γ₂ := ⟨_, false⟩ :: ⟨.ref E, false⟩ :: ⟨_, false⟩ :: ⟨_, false⟩ :: Γ) (by ctx)
      (.var (.there (.here (.cons (.cons hΓ))))) (d_take (.cons (.cons (.cons (.cons hΓ))))))
    ?_
  -- `x` (0), `c` (1), `q` (2)
  have hD : Ctx.Dead (⟨E, false⟩ :: ⟨VTy.ref .unit, false⟩ ::
      ⟨VTy.tensor (.ref .unit) (clistLE E'), false⟩ :: ⟨VTy.ref E, false⟩ ::
      ⟨VTy.tensor (.ref E) (.tensor (.ref .unit) (clistLE E')), false⟩ ::
      ⟨(clistFE E).resR (clistLE E'), false⟩ :: Γ) :=
    .cons (.cons (.cons (.cons (.cons (.cons hΓ)))))
  have e : VTy.inst (clistLE E') (clistFE E').ty
      = .sum .unit (.tensor (.ref E') (.ref (clistLE E'))) := by
    show VTy.sum .unit (.tensor (.ref (VTy.inst (clistLE E') E')) (.ref (clistLE E'))) = _
    rw [show VTy.inst (clistLE E') E' = E' from VTy.subst_closed0 hE' _]
  refine .ret (.roll (FShape.noMut_ty hW) (FShape.Cl_ty hW) ?_)
  rw [e]
  refine .sumI₂ ?_
  refine .tensorI (A := .ref E') (B := .ref (clistLE E'))
    (Γ₁ := ⟨E, true⟩ :: ⟨_, true⟩ :: ⟨_, false⟩ :: ⟨_, false⟩ :: ⟨_, false⟩ :: ⟨_, false⟩ :: Γ)
    (Γ₂ := ⟨E, false⟩ :: ⟨_, false⟩ :: ⟨_, true⟩ :: ⟨_, false⟩ :: ⟨_, false⟩ :: ⟨_, false⟩ :: Γ)
    (by ctx) ?_ ?_
  · refine .lolliE (A := .tensor (.ref .unit) E')
      (Γ₁ := ⟨E, true⟩ :: ⟨_, true⟩ :: ⟨_, false⟩ :: ⟨_, false⟩ :: ⟨_, false⟩ :: ⟨_, false⟩ :: Γ)
      (Γ₂ := ⟨E, false⟩ :: ⟨_, false⟩ :: ⟨_, false⟩ :: ⟨_, false⟩ :: ⟨_, false⟩ :: ⟨_, false⟩ :: Γ)
      (by ctx) ?_ (d_fill hD)
    refine .tensorI
      (Γ₁ := ⟨E, false⟩ :: ⟨_, true⟩ :: ⟨_, false⟩ :: ⟨_, false⟩ :: ⟨_, false⟩ :: ⟨_, false⟩ :: Γ)
      (Γ₂ := ⟨E, true⟩ :: ⟨_, false⟩ :: ⟨_, false⟩ :: ⟨_, false⟩ :: ⟨_, false⟩ :: ⟨_, false⟩ :: Γ)
      (by ctx) (.var (.there (.here (.cons (.cons (.cons (.cons hΓ))))))) ?_
    exact .lolliE
      (Γ₁ := ⟨E, true⟩ :: ⟨_, false⟩ :: ⟨_, false⟩ :: ⟨_, false⟩ :: ⟨_, false⟩ :: ⟨_, false⟩ :: Γ)
      (Γ₂ := ⟨E, false⟩ :: ⟨_, false⟩ :: ⟨_, false⟩ :: ⟨_, false⟩ :: ⟨_, false⟩ :: ⟨_, false⟩ :: Γ)
      (by ctx) (.var (.here (.cons (.cons (.cons (.cons (.cons hΓ))))))) (hf hD)
  · exact .lolliE (A := .tensor (.ref .unit) (clistLE E'))
      (Γ₁ := ⟨E, false⟩ :: ⟨_, false⟩ :: ⟨_, true⟩ :: ⟨_, false⟩ :: ⟨_, false⟩ :: ⟨_, false⟩ :: Γ)
      (Γ₂ := ⟨E, false⟩ :: ⟨_, false⟩ :: ⟨_, false⟩ :: ⟨_, false⟩ :: ⟨_, false⟩ :: ⟨_, false⟩ :: Γ)
      (by ctx) (.var (.there (.there (.here (.cons (.cons (.cons hΓ))))))) (d_fill hD)

/-- `foldReuse (mapRAlg f) : U(L_E ⊸ F L_E′)`. -/
def mapRE (f : Val) (E : VTy) : Expr := .app (.val (foldReuseV (clistFE E))) (.val (mapRAlgV f))

theorem d_mapR {Δ : LifeCtx} {Γ : Ctx VTy} {E E' : VTy} {f : Val} (hΓ : Ctx.Dead Γ)
    (hE : E.Cl 0) (hE' : E'.Cl 0)
    (hf : ∀ {Γ : Ctx VTy}, Ctx.Dead Γ → CDerives Δ Γ (.val f) (.val (.lolli E E'))) :
    CDerives Δ Γ (mapRE f E) (.val (.lolli (clistLE E) (clistLE E'))) :=
  .bangE (.lolliE (deadSplit hΓ) (d_mapRAlg hΓ hE' hf)
    (.foldReuse (clistFE E) (clistLE E') hΓ (clistFE_WF hE) trivial))

/-! ### The in-place increment -/

/-- `λn. n + 1`. -/
def incV : Val := .lam (.inj₂ (.var 0))

theorem d_inc {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ (.val incV) (.val (.lolli natN natN)) :=
  .thunkV rfl (.lam (.ret (.roll natBody_noMut natN_closed (.sumI₂ (.var (.here hΓ))))))

/-- `foldReuse (mapRAlg inc)`. -/
def mapIncRE : Expr := mapRE incV natN

theorem d_mapIncR {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ mapIncRE (.val (.lolli clistL clistL)) :=
  d_mapR hΓ natN_closed natN_closed d_inc

/-- **The in-place map's semantic type, from the Fundamental Property.** -/
theorem mapIncR_semV : SemV LifeCtx.empty [] mapIncRE (.lolli clistL clistL) :=
  fundamentalC (d_mapIncR .nil)

/-! ### `MapMut.lean`'s program with the in-place map -/

/-- The closed program: `toPure to t. mapIncR to m. mapProgOpenC`. -/
def mapProgR : Expr := bindE toPureCE (bindE mapIncRE mapProgOpenC)

theorem mapProgR_derives : CDerives LifeCtx.empty [] mapProgR (.comp (.ret pureL)) :=
  .bind .nil (.ret (d_toPureC .nil))
    (.bind (.right .nil) (.ret (d_mapIncR (.cons .nil))) mapProgOpenC_derives)

/-- **Adequacy at the in-place map**: from the empty memory to a pure list and the empty
memory. -/
theorem mapProgR_runs :
    ∃ v, PureOut v ∧ BoCa.BoLo.Steps Adequacy.emptyMem mapProgR Adequacy.emptyMem (.val v) := by
  have hwp : wpTS [] mapProgR (fun _ v => Fig16.BoLo.pure (PureOut v)) (PMap.empty : WRes) := by
    refine wpTS_mono (fun ls v ρ hv => ?_) PMap.empty (wp_of_derives mapProgR_derives)
    have e := vC_pureL_empty (sizeOf v.1 + 1) (Nat.lt_succ_self _) hv
    subst e
    exact ⟨rfl, true, ls, LSub.empty, hv⟩
  obtain ⟨v, hsteps, hv⟩ := theorem32 mapProgR PureOut hwp
  exact ⟨v, hv, hsteps⟩

set_option maxRecDepth 100000 in
theorem mapProgR_eval : pureNoLeak (eval mapProgR) = some [1, 1, 1] := by decide

/-! ### Changing the element type: `N → B` -/

/-- `λn. case n {inj₁ u. inj₂ u | inj₂ m. freeNat m; inj₁ ()}`: whether `n` is zero. -/
def isZeroV : Val :=
  .lam (.case (.var 0) (.inj₂ (.var 0)) (.seq (.app freeNatE (.var 0)) (.inj₁ (.val .unit))))

theorem d_isZero {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ (.val isZeroV) (.val (.lolli natN boolT)) := by
  refine .thunkV rfl (.lam (.sumE (A := .unit) (B := natN)
    (Γs := ⟨_, true⟩ :: Γ) (Γb := ⟨_, false⟩ :: Γ) (by ctx) (.unroll (.var (.here hΓ)))
    (.ret (.sumI₂ (.var (.here (.cons hΓ))))) ?_))
  exact .unitE (Γ₁ := ⟨natN, true⟩ :: ⟨_, false⟩ :: Γ)
    (Γ₂ := ⟨natN, false⟩ :: ⟨_, false⟩ :: Γ) (by ctx)
    (.lolliE (Γ₁ := ⟨natN, true⟩ :: ⟨_, false⟩ :: Γ) (Γ₂ := ⟨natN, false⟩ :: ⟨_, false⟩ :: Γ)
      (by ctx) (.var (.here (.cons hΓ))) (d_freeNat (.cons (.cons hΓ))))
    (.ret (.sumI₁ (.unitI (.cons (.cons hΓ)))))

/-- `foldReuse (mapRAlg isZero) : U(L_N ⊸ F L_B)`, a map that changes the element type. -/
def isZeroRE : Expr := mapRE isZeroV natN

theorem d_isZeroR {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ isZeroRE (.val (.lolli clistL (clistLE boolT))) :=
  d_mapR hΓ natN_closed (by simp [VTy.Cl]) d_isZero

theorem isZeroR_semV : SemV LifeCtx.empty [] isZeroRE (.lolli clistL (clistLE boolT)) :=
  fundamentalC (d_isZeroR .nil)

/-! ### In place: the interpreter's node addresses -/

/-- The nodes of the list `e` in `μ` as `(address, payload)`, when every node is at two
adjacent cells `(ℓ, ℓ + 1)`. -/
def nodesAt {α : Type} (rd : Expr → Option α) : Nat → BoCa.Mem → Expr → Option (List (Nat × α))
  | 0, _, _ => none
  | _ + 1, _, .inj₁ .unit => some []
  | n + 1, μ, .inj₂ (.pair (.loc a) (.loc b)) =>
      if b = a + 1 then do
        let x ← μ.get? a
        let k ← rd x.1
        let t ← μ.get? b
        let ks ← nodesAt rd n μ t.1
        pure ((a, k) :: ks)
      else none
  | _, _, _ => none

/-- Run `e` and read the list it returns as `(address, payload)` pairs. -/
def nodesOf {α : Type} (rd : Expr → Option α) (e : Expr) : Option (List (Nat × α)) := do
  let (v, μ) ← runMem 4000 BoCa.Mem.empty e
  nodesAt rd 100 μ v.1

/-- Build `[k₁, k₂, …]` and apply `f` to it. -/
def afterBuild (ks : List Nat) (f : Expr) : Expr := bindE (buildList ks) (.app f (.var 0))

set_option maxRecDepth 100000 in
/-- The built list `[0, 0, 0]`: nodes at `4`, `2`, `0` (the last node is allocated first). -/
theorem buildC0_nodes : nodesOf numOf buildC0 = some [(4, 0), (2, 0), (0, 0)] := by decide

set_option maxRecDepth 100000 in
/-- **`mapIncRE` is in place**: after the map the nodes are at the same addresses. -/
theorem mapIncR_inPlace :
    nodesOf numOf (afterBuild [0, 0, 0] mapIncRE) = some [(4, 1), (2, 1), (0, 1)] := by decide

set_option maxRecDepth 100000 in
/-- `foldOwn`'s `mapIncCE` rebuilds the list in fresh blocks, at `10`, `8`, `6`. -/
theorem mapIncC_moves :
    (nodesOf numOf (afterBuild [0, 0, 0] mapIncCE)).map (List.map Prod.fst)
      = some [10, 8, 6] := by decide

set_option maxRecDepth 100000 in
/-- **`isZeroRE` is in place**: `[0, 1, 0]` becomes `[true, false, true]` in the numerals'
cells. -/
theorem isZeroR_inPlace :
    nodesOf numOf (buildList [0, 1, 0]) = some [(4, 0), (2, 1), (0, 0)] ∧
    nodesOf boolOf (afterBuild [0, 1, 0] isZeroRE)
      = some [(4, true), (2, false), (0, true)] := by decide

end BoCa.Fig16.LogRel.Core

end
