import Optics.Prism
import Core.ReuseList

/-!
# Optics — the decisive test (b): a list traversal  (stage 3)

Over the common list `L_E = μX. 1 ⊕ (Ref E ⊗ Ref X)` (each node one block), two traversals,
each a closed `CDerives` derivation from `foldReuse`, `withbor` and `withswap`:

* **Copy-in/copy-out** (`mapOverV`, the accessor form):
  `Mut @a L_E ⊸ Mut @a L_E ⊗ 1`, `withswap m (λl. (foldReuse (mapRAlg f) l, ()))`, the in-place
  map of `ReuseList.lean` run through a mutable borrow of the list's cell.
* **Borrow form, one element at a time** (`iterMutV`, IterMut):
  `L_E ⊸ !(∀'x ⊏ ⊓Δ. Mut 'x E ⊸ ['x] 1) ⊸ L_E ⊗ 1`.  `foldReuse`'s algebra lends each value
  cell to the callback by `withbor`, at its own fresh lifetime, and refills the emptied next
  cell with the traversed tail.  The algebra is built at run time around the callback, promoted
  under `!` over the callback's slot.

`iterProg` builds `[0, 0, 0]`, increments each element through its `Mut 'x N`, frees the list;
`adequacyC` runs it with no cell left, and the interpreter returns `[1, 1, 1]` with the nodes at
their addresses (`iterObs_eval`, `iter_inPlace`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Optics
open BoCa
open BoCa.Fig16
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Kont)
open BoCa.Programs (app2 alloc' free' unitNoLeak)

/-- Close a context-split, `Solo` or `Dead` goal whose contexts are fixed, over a dead tail. -/
local macro "ctx" : tactic =>
  `(tactic| repeat (first | assumption | exact deadSplit (by assumption) | constructor))

/-! ### IterMut -/

/-- The algebra's body, under `r` (0) with the callback at `g` (index 1):
`case r {inj₁ u ⇒ inj₁ u | inj₂ p ⇒ let (rx, q) = p; let (rx′, u) = withbor rx g; u;
inj₂ (rx′, fill q)}`. -/
def itAlgB : Expr :=
  .case (.var 0) (.inj₁ (.var 0))
    (.letpair (.var 0)
      (.letpair (app2 (.val withborV) (.var 1) (.var 4))
        (.seq (.var 0) (.inj₂ (.pair (.var 1) (.app (.val fillV) (.var 2)))))))

/-- `λs. λg. (foldReuse (λr. itAlgB) s, ())`. -/
def iterMutV (E : VTy) : Val :=
  .lam (.val (.lam (.pair (.app (.app (.val (foldReuseV (clistFE E))) (.val (.lam itAlgB))) (.var 1))
    unit')))

/-- The callback's type, `∀'x ⊏ @b. Mut 'x E ⊸ ['x] 1`. -/
abbrev elemCb (E : VTy) (x : LifeVar) (b : Lifetime.Life) : VTy :=
  cbTy (fun c => .mut c E) x b .unit

theorem d_itAlgB {Δ : LifeCtx} {Γ : Ctx VTy} {x : LifeVar} {E : VTy} (hE : plainV E = true)
    (hEc : E.Cl 0) (hx : Δ.find? x = none) (hΓ : Ctx.Dead Γ) :
    CDerives Δ (⟨(clistFE E).resR (clistLE E), true⟩ ::
        ⟨.bang (elemCb E x Δ.meetOfDom), true⟩ :: Γ) itAlgB (.comp (.ret (clistLE E))) := by
  have hW := clistFE_WF hEc
  have hD := hΓ.toP
  have e : VTy.inst (clistLE E) (clistFE E).ty
      = .sum .unit (.tensor (.ref E) (.ref (clistLE E))) := by
    show VTy.sum .unit (.tensor (.ref (VTy.inst (clistLE E) E)) (.ref (clistLE E))) = _
    rw [show VTy.inst (clistLE E) E = E from VTy.subst_closed0 hEc _]
  refine .sumE (A := .unit) (B := .tensor (.ref E) (.tensor (.ref .unit) (clistLE E)))
    (Γs := ⟨_, true⟩ :: ⟨_, false⟩ :: Γ) (Γb := ⟨_, false⟩ :: ⟨_, true⟩ :: Γ)
    (.left (.right (deadSplit hΓ))) (.var (.here (.cons hD))) ?_ ?_
  · refine .ret (.roll (FShape.noMut_ty hW) (FShape.Cl_ty hW) ?_)
    rw [e]
    exact .sumI₁ (.var (.here (.cons (.drop rfl hD))))
  refine .tensorE (A := .ref E) (B := .tensor (.ref .unit) (clistLE E))
    (Γp := ⟨_, true⟩ :: ⟨_, false⟩ :: ⟨_, false⟩ :: Γ)
    (Γb := ⟨_, false⟩ :: ⟨_, false⟩ :: ⟨_, true⟩ :: Γ)
    (.left (.dead (.right (deadSplit hΓ)))) (.var (.here (.cons (.cons hD)))) ?_
  -- `q` (0), `rx` (1), `p` (2), `r` (3), `g` (4)
  refine .tensorE (A := .ref E) (B := .unit)
    (Γp := ⟨_, false⟩ :: ⟨_, true⟩ :: ⟨_, false⟩ :: ⟨_, false⟩ :: ⟨_, true⟩ :: Γ)
    (Γb := ⟨_, true⟩ :: ⟨_, false⟩ :: ⟨_, false⟩ :: ⟨_, false⟩ :: ⟨_, false⟩ :: Γ)
    (.right (.left (.dead (.dead (.left (deadSplit hΓ)))))) ?_ ?_
  · refine .lolliE (.dead (.right (.dead (.dead (.left (deadSplit hΓ))))))
      (.bangE (.var (.there (.there (.there (.there (.here hD))))))) ?_
    exact .lolliE (.dead (.left (.dead (.dead (.dead (deadSplit hΓ))))))
      (.var (.there (.here (.cons (.cons (.cons hD))))))
      (.withbor2 x (.cons (.cons (.cons (.cons (.cons hD))))) hx
        ⟨.top, Lifetime.LifeCtx.defines_of_wf rfl, plain_outlives hE⟩ (plain_noFree hE)
        (by simp [VFree]))
  -- `u` (0), `rx′` (1), `q` (2)
  refine .unitE (.left (.right (.right (.dead (.dead (.dead (.dead (deadSplit hΓ))))))))
    (.var (.here (.cons (.cons (.cons (.cons (.cons (.cons hD)))))))) ?_
  refine .ret (.roll (FShape.noMut_ty hW) (FShape.Cl_ty hW) ?_)
  rw [e]
  refine .sumI₂ (.tensorI (.dead (.left (.right (.dead (.dead (.dead (.dead (deadSplit hΓ))))))))
    (.var (.there (.here (.cons (.cons (.cons (.cons (.cons hD)))))))) ?_)
  exact .lolliE (.dead (.dead (.left (.dead (.dead (.dead (.dead (deadSplit hΓ))))))))
    (.var (.there (.there (.here (.cons (.cons (.cons (.cons hD))))))))
    (d_fill (.cons (.cons (.cons (.cons (.cons (.cons (.cons hΓ))))))))

/-- **IterMut**: `iterMut : L_E ⊸ !(∀'x ⊏ ⊓Δ. Mut 'x E ⊸ ['x] 1) ⊸ L_E ⊗ 1`. -/
theorem d_iterMut {Δ : LifeCtx} {Γ : Ctx VTy} {x : LifeVar} {E : VTy} (hE : plainV E = true)
    (hEc : E.Cl 0) (hx : Δ.find? x = none) (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ (.val (iterMutV E))
      (.val (.lolli (clistLE E) (.lolli (.bang (elemCb E x Δ.meetOfDom))
        (.tensor (clistLE E) .unit)))) := by
  have hD := hΓ.toP
  refine .lamV (.lamV ?_)
  refine .tensorI (.left (.left (deadSplit hΓ))) ?_ (.unitI (.cons (.cons hD)))
  refine .lolliE (.right (.left (deadSplit hΓ))) (.var (.there (.here hD))) ?_
  refine .bangE (.lolliE (.left (.dead (deadSplit hΓ))) ?_
    (.foldReuse (clistFE E) (clistLE E) (.cons (.cons hD)) (clistFE_WF hEc) trivial))
  exact .bangThunkV (fun s hs hl => by
      simp only [List.mem_cons] at hs
      rcases hs with rfl | rfl | hs
      · exact ⟨_, rfl⟩
      · simp at hl
      · exact absurd hl (by have := dead_noLive hΓ (P := fun _ => False) s hs; simpa using this))
    rfl (.lam (d_itAlgB hE hEc hx (.cons hΓ)))

/-! ### Copy-in/copy-out: the accessor form through `withswap` -/

/-- `λm. withswap m (λl. (mapRE f E l, ()))`. -/
def mapOverV (f : Val) (E : VTy) : Val :=
  .lam (app2 withswap (.var 0) (.val (.lam (.pair (.app (mapRE f E) (.var 0)) unit'))))

/-- `Mut @a L_E ⊸ Mut @a L_E ⊗ 1`, for `f : E ⊸ E`. -/
theorem d_mapOver {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {E : VTy} {f : Val}
    (hEc : E.Cl 0) (hf : ∀ {Γ : Ctx VTy}, Ctx.Dead Γ → CDerives Δ Γ (.val f) (.val (.lolli E E)))
    (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ (.val (mapOverV f E)) (.val (.lolli (.mut a (clistLE E)) (.tensor (.mut a (clistLE E)) .unit))) := by
  have hD := hΓ.toP
  refine .lamV (.lolliE (.right (deadSplit hΓ)) ?_
    (.lolliE (.left (deadSplit hΓ)) (.var (.here hD)) (.withswap (.cons hD))))
  refine .lamV (.tensorI (.left (.dead (deadSplit hΓ))) ?_ (.unitI (.cons (.cons hD))))
  exact .lolliE (.left (.dead (deadSplit hΓ))) (.var (.here (.cons hD)))
    (d_mapR (.cons (.cons hΓ)) hEc hEc hf)

/-! ### A program: IterMut over `[0, 0, 0]`

    let (l, u) = iterMut [0, 0, 0] (! Λ. λm. let (m′, u) = withswap m incG; u; forget m′; ());
    u; free l -/

/-- `λn. (n + 1, ())`. -/
def incG : Expr := .val (.lam (.pair (.inj₂ (.var 0)) unit'))

/-- `Λ. λm. let (m′, u) = withswap m incG; u; forget m′; ()`. -/
def incCb : Expr :=
  .val (.lam (.val (.lam (.letpair (app2 withswap (.var 0) incG)
    (.seq (.var 0) (.seq (.app forget (.var 1)) unit'))))))

theorem d_incCb {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives LifeCtx.empty Γ incCb (.val (.bang (elemCb natN 0 LifeCtx.empty.meetOfDom))) := by
  refine .bangThunkV (persistent_dead hΓ) rfl (allI_fresh (S := .unit) ok_empty rfl hΓ (.ret (.lamV ?_)))
  exact letW (A := .mut (.var 0) natN) (B := .unit)
      (appW (.lamV (pairW (.roll natBody_noMut natN_closed (.sumI₂ (.var (by csolo))))
          (.unitI (by cdead))))
        (appW (.var (by csolo)) (.withswap (by cdead)))) <|
    seqW (.var (by csolo)) <|
    seqW (appW (.var (by csolo)) (.forgetMut (by cdead)))
      (.boxI (.unitI (by cdead)) ⟨Lifetime.LifeCtx.defines_of_wf rfl, dead_noLive (by cdead)⟩)

theorem natN_plain : plainV natN = true := rfl

/-- The program, ending with `k` applied to the traversed list. -/
def iterProgK (k : Expr) : Expr :=
  .letpair (app2 (.val (iterMutV natN)) (buildList [0, 0, 0]) incCb) (.seq (.var 0) (.app k (.var 1)))

def iterProg : Expr := iterProgK freeCE

theorem d_iterProg : CDerives LifeCtx.empty [] iterProg (.val .unit) := by
  refine letW (A := clistL) (B := .unit)
    (appW (d_incCb (by cdead)) (appW (d_buildList (by cdead) _)
      (d_iterMut natN_plain natN_closed rfl (by cdead)))) ?_
  exact seqW (.var (by csolo)) (appW (.var (by csolo)) (d_freeC (by cdead)))

theorem iterProg_runs :
    BoCa.BoLo.Steps Adequacy.emptyMem iterProg Adequacy.emptyMem (.val .unit) :=
  adequacyC (.ret d_iterProg)

set_option maxRecDepth 100000 in
theorem iterProg_eval : unitNoLeak (eval iterProg) = true := by decide

set_option maxRecDepth 100000 in
/-- Every element incremented: `[1, 1, 1]`, with no cell left. -/
theorem iterObs_eval : pureNoLeak (eval (iterProgK toPureCE)) = some [1, 1, 1] := by decide

/-- The traversed list, not freed. -/
def iterKeep : Expr :=
  .letpair (app2 (.val (iterMutV natN)) (buildList [0, 0, 0]) incCb) (.seq (.var 0) (.var 1))

set_option maxRecDepth 100000 in
/-- **In place**: after IterMut the nodes are where `buildList` put them. -/
theorem iter_inPlace : nodesOf numOf iterKeep = some [(4, 1), (2, 1), (0, 1)] := by decide

end BoCa.Fig16.LogRel.Core.Optics

end
