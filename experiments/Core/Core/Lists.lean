import Core.Fix
import Core.Examples
import Paper.Examples.Programs

/-!
# Core — the boxed list through the real former

`L = μX. 1 ⊕ Ref X` is a `VTy`.  A list is built by a `CDerives` derivation (`roll`, `alloc`),
and `freeAll = Z (λself. λl. case l {inj₁ u. u | inj₂ r. self (free r)})` frees it.

* `freeAll_wp`: at a list `v`, `freeAll v` has a `wpTS` to `()` at every record list, by
  induction on the least fixed point (`vC_mu_ind`).
* `freeAll_semV`: `SemV [] freeAll (U (L ⊸ F 1))`, the semantic judgment at the real type.
* `build3Free_runs`: a 3-cell list built by `CDerives` and freed runs from the empty memory to
  `()` and the empty memory; `build3Free_eval`: the interpreter agrees.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### The type -/

/-- `1 ⊕ Ref X`. -/
def listBody : VTy := .sum .unit (.ref (.tvar 0))

/-- `L = μX. 1 ⊕ Ref X`. -/
def listL : VTy := .mu listBody

theorem listBody_noMut : listBody.NoMut 0 := ⟨trivial, trivial⟩

theorem listL_closed : listL.Cl 0 := ⟨trivial, Nat.zero_lt_one⟩

/-- `L` unrolls to `1 ⊕ Ref L`. -/
theorem listL_unroll : VTy.inst listL listBody = .sum .unit (.ref listL) := rfl

/-- `L` holds `own` cells only: it outlives every lifetime. -/
theorem listL_outlives (Δ : LifeCtx) (a : Lifetime.Life) : VOutlives Δ a listL :=
  .mu (.sum .unit (.ref .tvar))

/-! ### Building a list -/

/-- The empty list, `roll (inj₁ ())`. -/
theorem d_nil {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ (.inj₁ (.val .unit)) (.val listL) :=
  .roll listBody_noMut listL_closed (.sumI₁ (.unitI hΓ))

/-- `roll (inj₂ (alloc e))` for a list `e`. -/
theorem d_cons {Δ : LifeCtx} {e : Expr} (h : CDerives Δ [] e (.val listL)) :
    CDerives Δ [] (.inj₂ (.app (.val (.prim .alloc)) e)) (.val listL) :=
  .roll listBody_noMut listL_closed (.sumI₂ (.lolliE .nil h (.alloc .nil)))

/-- `inj₂ (alloc (inj₂ (alloc (inj₂ (alloc (inj₁ ()))))))`. -/
def build3 : Expr :=
  .inj₂ (.app (.val (.prim .alloc)) (.inj₂ (.app (.val (.prim .alloc))
    (.inj₂ (.app (.val (.prim .alloc)) (.inj₁ (.val .unit)))))))

theorem build3_derives : CDerives LifeCtx.empty [] build3 (.val listL) :=
  d_cons (d_cons (d_cons (d_nil .nil)))

/-! ### `freeAll` -/

/-- The body of `freeAll = Z (λself. λl. case l {inj₁ u. u | inj₂ r. self (free r)})`. -/
def faB : Expr := .case (.var 0) (.var 0) (.app (.var 2) (.app (.val (.prim .free)) (.var 0)))

theorem faB_closed : closedAt 2 faB = true := rfl

/-- `faB[S/self][w/l]` for a closed handle `S`. -/
theorem faB_subst {S : Val} (hS : closedAt 0 S.1 = true) (w : Val) :
    (faB.subst 1 S).subst 0 w
      = .case (.val w) (.var 0) (.app (.val S) (.app (.val (.prim .free)) (.var 0))) := by
  have h₁ : ∀ d c, Expr.shift d c S.1 = S.1 := fun d c => shift_closedAt S.1 d hS (Nat.zero_le c)
  have h₂ : ∀ j s, Expr.subst j s S.1 = S.1 := fun j s => subst_closedAt S.1 s hS (Nat.zero_le j)
  simp [faB, Expr.subst, h₁, h₂]

/-- `freeAll`, a closed λ-value. -/
def freeAll : Val := fixV faB

theorem freeAll_closed : closedAt 0 freeAll.1 = true := by
  simp [freeAll, fixV, closedAt]
  rfl

/-- The postcondition of `F 1`. -/
abbrev unitQ : List SRec → Val → WProp := fun _ w => ⌜w = .unit⌝

/-- `freeAll v` frees every cell of a list `v` and returns `()`, at every record list: induction
on the least fixed point at `L`. -/
theorem freeAll_wp {b : Bool} {ls : List SRec} {δ : LSub} {v : Val} {ρ : WRes}
    (h : vC b listL ls δ v ρ) (ls' : List SRec) :
    wpTS ls' (.app (.val freeAll) (.val v)) unitQ ρ := by
  have hS := selfV_closed faB_closed
  refine vC_mu_ind (A := listBody) (δ := δ)
    (fun _ _ v ρ => ∀ ls', wpTS ls' (.app (.val freeAll) (.val v)) unitQ ρ) ?_ b ls v ρ h ls'
  rintro b ls v ρ - - (⟨v₁, hs⟩ | ⟨v₂, hs⟩) ls'
  · obtain ⟨rfl, rfl, rfl⟩ := pure_sep_iff.mp hs
    rw [freeAll, fixV_eq faB_closed]
    refine wpTS_lolli _ _ _ _ _ ?_
    rw [faB_subst hS]
    refine wpTS_sum₁ _ _ _ _ _ _ ?_
    exact wpTS_val _ _ _ _ ⟨rfl, rfl⟩
  · obtain ⟨rfl, ℓ, v', hs'⟩ := pure_sep_iff.mp hs
    obtain ⟨rfl, ρ₁, ρ₂, hc, hρ₁, hP⟩ := pure_sep_iff.mp hs'
    rw [freeAll, fixV_eq faB_closed]
    refine wpTS_lolli _ _ _ _ _ ?_
    rw [faB_subst hS]
    refine wpTS_sum₂ _ _ _ _ _ _ ?_
    have e₂ : (Expr.app (.val (selfV faB)) (.app (.val (.prim .free)) (.var 0))).subst 0
        (Val.loc ℓ) = (Kont.appR (.val (selfV faB)) .hole).plug
          (.app (.val (.prim .free)) (.val (.loc ℓ))) := by
      simp [Expr.subst, val_subst_closed hS, Kont.plug]
    rw [e₂]
    refine wpTS_bind _ _ _ _ _ ?_
    refine wpTS_free _ _ _ _ _ ⟨ρ₁, ρ₂, hc, hρ₁, ?_⟩
    have := hP.2 ls'
    rw [freeAll] at this
    exact wpTS_selfV faB_closed v' ls' unitQ ρ₂ this

/-- A closed value at the empty context: its semantic judgment is the relation at `∅`. -/
theorem semV_closed {Δ : LifeCtx} {v : Val} {A : VTy} (hv : closedAt 0 v.1 = true)
    (h : ∀ δ ls, vC true A ls δ v PMap.empty) : SemV Δ [] (.val v) A := by
  intro δ γ ls ρ _ hg
  obtain ⟨ρ₁, ρ₂, hc, ⟨rfl, -⟩, hsep⟩ := hg
  have e : ρ₂ = PMap.empty := hsep.1
  subst e
  rw [eq_of_compS_empty_left hc, substAll_closed hv]
  exact wpTS_val ls v _ _ (h δ ls)

/-- `freeAll` is a value of `U (L ⊸ F 1)` at `∅`. -/
theorem freeAll_vC (δ : LSub) (ls : List SRec) :
    vC true (.lolli listL .unit) ls δ freeAll PMap.empty := by
  intro ls' _ v ρ₁ ρ₂ hv hc
  rw [eq_of_compS_empty_left hc]
  exact freeAll_wp hv ls'

/-- **`freeAll : U (L ⊸ F 1)`**, the semantic judgment at the real type. -/
theorem freeAll_semV {Δ : LifeCtx} : SemV Δ [] (.val freeAll) (.lolli listL .unit) :=
  semV_closed freeAll_closed freeAll_vC

/-! ### Build a 3-cell list and free it -/

/-- `freeAll build3`. -/
def build3Free : Expr := .app (.val freeAll) build3

theorem build3Free_sem : SemV LifeCtx.empty [] build3Free .unit :=
  lolliE_compatX .nil (fundamentalC build3_derives) freeAll_semV

/-- **Adequacy at the list**: build a 3-cell list and free it; the run goes from the empty
memory to `()` and the empty memory. -/
theorem build3Free_runs :
    BoCa.BoLo.Steps Adequacy.emptyMem build3Free Adequacy.emptyMem (.val .unit) :=
  corollary33 build3Free build3Free_sem

/-- The executable interpreter agrees: `()` and no cell left. -/
theorem build3Free_eval : Programs.unitNoLeak (eval build3Free) = true := by decide

/-! ### `Imm̲` at the list and at a boxed tree -/

/-- `Imm̲ 'b L = μY. 1 ⊕ Imm 'b L`: the tail borrow's payload is `L` itself. -/
theorem listL_immReborrow (b : Lifetime.Life) :
    listL.immReborrow b = .mu (.sum .unit (.imm b listL)) := rfl

/-- The boxed binary tree `T = μX. 1 ⊕ (Ref X ⊗ Ref X)`. -/
def treeBody : VTy := .sum .unit (.tensor (.ref (.tvar 0)) (.ref (.tvar 0)))

def treeT : VTy := .mu treeBody

theorem treeT_closed : treeT.Cl 0 := ⟨trivial, Nat.zero_lt_one, Nat.zero_lt_one⟩

/-- `Imm̲ 'b` at the tree's unrolling: both children are borrows of trees. -/
theorem treeT_immReborrow_unroll (b : Lifetime.Life) :
    (VTy.inst treeT treeBody).immReborrow b = .sum .unit (.tensor (.imm b treeT) (.imm b treeT)) :=
  rfl

/-- A loaded tree view is a leaf or two child borrows, at the relation. -/
theorem vC_tree_immReborrow {c : Lifetime.Life} {b : Bool} {ls : List SRec} {δ : LSub} {v : Val}
    {ρ : WRes} : vC b (treeT.immReborrow c) ls δ v ρ ↔
      vC b (.sum .unit (.tensor (.imm c treeT) (.imm c treeT))) ls δ v ρ :=
  vC_immReborrow_mu_iff treeT_closed c b ls δ v ρ

end BoCa.Fig16.LogRel.Core

end
