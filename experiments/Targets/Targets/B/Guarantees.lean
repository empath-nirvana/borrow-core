import Targets.B.World
import Targets.Base.RunProps
import Targets.Base.Machine

/-!
# System B — BoLo's guarantees, given (RESTRUCTURE §2.2)

B states BoLo's guarantees as Props over a typing system `J : TypingJ` and a borrow world
`M : BWorld`, so that they can be asked of the composite, and proves each at BoLo by citation
(`Targets/B/BoLo.lean`).  Nothing is researched here.

| id | guarantee | Prop | printed |
|---|---|---|---|
| B0 | BoLo's programs stay typed | `ExtendsB J` | — |
| B1 | the fundamental property | `FL M J` | [TR] 6.151: "If ∆; Γ ⊢ e ∶ T then ∆; Γ ⊧ e ∶ T." |
| B2 | adequacy | `Adequate M` | [CONF] Thm 3.2 |
| B3, B4 | no use after free, no double free; leak freedom | `Sound J` | [CONF] 415:18, 415:23 |
| B4′ | B3, B4 with externs meeting their contracts | `SoundContracts J M` | — |
| B5 | release exactly once, location reuse included | `ReleasedOnceReuse J M` | — |
| B6 | exclusive mutable borrows | `ExclusiveB M` | [CONF] 415:21 |
| B7 | lifetimes respected | `LifetimeSound M J.out` | [TR] 6.60 |
| — | the bounds | `WBound M` | — |

Here: FL, adequacy, the bounds, the run-end laws, `LifetimeSound` (P9), `ExclusiveB`,
`SliceShapeB`, `WBound`, `BorrowRulesClosed`, `ExtendsB`, `ContractsW`, `SoundContracts`,
`ReleasedOnceReuse` (with content, finding #2) and `Guarantees`, each over `BWorld`.

B's statements are about Core's machine and Core's types, and both have effects: `Sound`, `Adequate`
and `SoundContracts` quantify over platforms and the rows they answer, `RelElim` covers `ν`, `FL`
covers every judgement of `J`.  That is because "nothing breaks the borrow calculus" is about every
program of the composite.  B contains no effect system, no stop condition, no share and nothing
held: those are the interaction's (`Targets/I`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core

mutual
/-- Every effect layer anywhere in the type is abortive: the operations a callback of this type can
perform are in `{fn, abort}` (answering effects are borrows, not rows; I4). -/
def VTy.AbortRows : VTy → Prop
  | .tensor A B | .sum A B => A.AbortRows ∧ B.AbortRows
  | .thunk C => C.AbortRows
  | .ref A | .imm _ A | .mut _ A | .box _ A | .bang A | .mu A | .fam A => A.AbortRows
  | .unit | .zero | .unk | .tvar _ | .int _ | .opq _ => True
/-- `VTy.AbortRows` at a computation type. -/
def CTy.AbortRows : CTy → Prop
  | .ret A => A.AbortRows
  | .arr A C => A.AbortRows ∧ C.AbortRows
  | .amp C D => C.AbortRows ∧ D.AbortRows
  | .top => True
  | .all _ _ C | .nu C => C.AbortRows
  | .eff _ _ q A B fin C => (B.isZero && q != .lin) = true ∧ A.AbortRows ∧ B.AbortRows ∧ C.AbortRows
end


end BoCa.Fig16.LogRel.Core

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- **The fundamental lemma at W**: every judgment of `J` holds in W's relation. -/
def FL (M : B.BWorld) (J : TypingJ) : Prop := ∀ Θ Δ Γ e j, J Θ Δ Γ e j → SemW M Θ Δ Γ e j

/-- Adequacy at a platform, for programs at a div-free answer. -/
def AdequateRetAt (M : B.BWorld) (P : Platform) : Prop :=
  ∀ (S : Row) (A : VTy) (e : Expr), DivFree S A → RowLe S P.ops →
    M.comp (CTy.effOf S A) ([], M.nil) LSub.empty e (PMap.empty : WRes) →
    SafeRuns (ℍ := ℍ) P A e ∧ Terminates (ℍ := ℍ) P A e

/-- Adequacy at a platform, for programs that return a loop whose body is positive.  `νX. C` is
well formed at a positive `C` (`CTy.NuOk`, decision D2); at a row with distinct keys that the
platform answers, every loop body is positive (`loopEffBody_nuOk_of_uniq`). -/
def AdequateDriveAt (M : B.BWorld) (P : Platform) : Prop :=
  ∀ (S : Row) (A B : VTy) (e : Expr), A.Data → RowLe S P.ops → (CTy.loopEffBody S A B).NuOk →
    M.comp (CTy.effOf S (.thunk (CTy.loopEff S A B))) ([], M.nil) LSub.empty e
      (PMap.empty : WRes) →
    SafeDrive (ℍ := ℍ) P A e

/-- Adequacy at a platform. -/
def AdequateAt (M : B.BWorld) (P : Platform) : Prop :=
  AdequateRetAt (ℍ := ℍ) M P ∧ AdequateDriveAt (ℍ := ℍ) M P

/-- **Adequacy**: at every platform that respects its protocol. -/
def Adequate (M : B.BWorld) : Prop := ∀ P : Platform, P.Respects → AdequateAt (ℍ := ℍ) M P

/-- The Kripke order is a preorder. -/
def ExtPre (M : B.BWorld) : Prop :=
  (∀ i ρ, M.Ext i i ρ) ∧ (∀ i i' i'' ρ, M.Ext i i' ρ → M.Ext i' i'' ρ → M.Ext i i'' ρ)

/-- The empty configuration is reached at the nil index. -/
def FamEmpty (M : B.BWorld) : Prop := M.Fam (PMap.empty : WRes) [] ([], M.nil)

/-- Data values are exactly data, and hold nothing. -/
def DataVals (M : B.BWorld) : Prop :=
  ∀ b A i δ v ρ, A.Data → (M.val b A i δ v ρ ↔ ρ = PMap.empty ∧ DataVal A v)

/-- The eliminations, at the same index.  None has an `M.Ext` quantifier, so each holds under
either option of OQ-8. -/
def RelElim (M : B.BWorld) : Prop :=
  (∀ C i δ v ρ, M.val true (.thunk C) i δ v ρ → M.comp C i δ (forceE C (.val v)) ρ) ∧
  (∀ A C i δ e ρ, M.comp (.arr A C) i δ e ρ →
     ∀ v, (M.val true A i δ v ─⋆ M.comp C i δ (.app e (.val v))) ρ) ∧
  (∀ C D i δ e ρ, M.comp (.amp C D) i δ e ρ →
     M.comp C i δ (.app e (.val (Val.inj₁ .unit))) ρ ∧
     M.comp D i δ (.app e (.val (Val.inj₂ .unit))) ρ) ∧
  (∀ x b C i δ e ρ, M.comp (.all x b C) i δ e ρ → ∀ α, LtLife δ b α →
     M.comp C i (δ.extend x α) (.app e (.val .unit)) ρ) ∧
  (∀ C i δ e ρ, C.NuOk → M.comp (.nu C) i δ e ρ → M.comp C.unroll i δ e ρ) ∧
  (∀ b A i δ v ρ, M.val b (.mu A) i δ v ρ → M.val b (VTy.inst (.mu A) A) i δ v ρ)

/-- **The shapes of values**, at the same index: `vCE`'s clauses with W's relation in place of
`vCE`'s recursive calls.  At `Imm` and `Mut` these are Core's `ptoImmS`/`ptoMutS` clauses at W's
index, with the coherence `CohE` and the payload in W's relation: the observable view at `Imm`, the
program's relation at `Mut`. -/
def RelShape (M : B.BWorld) : Prop :=
  (∀ b i δ v ρ, M.val b .unit i δ v ρ → v = .unit ∧ ρ = PMap.empty) ∧
  (∀ b i δ v ρ, ¬ M.val b .zero i δ v ρ) ∧
  (∀ b A B i δ v ρ, M.val b (.tensor A B) i δ v ρ →
     ∃ v₁ v₂, v = Val.pair v₁ v₂ ∧ (M.val b A i δ v₁ ⋆ M.val b B i δ v₂) ρ) ∧
  (∀ b A B i δ v ρ, M.val b (.sum A B) i δ v ρ →
     (∃ w, v = Val.inj₁ w ∧ M.val b A i δ w ρ) ∨ (∃ w, v = Val.inj₂ w ∧ M.val b B i δ w ρ)) ∧
  (∀ b A i δ v ρ, M.val b (.ref A) i δ v ρ →
     ∃ ℓ v', v = Val.loc ℓ ∧ (ptoOwn ℓ v' ⋆ M.val b A i δ v') ρ) ∧
  (∀ b A i δ v ρ, M.val b (.bang A) i δ v ρ → ρ = PMap.empty ∧ M.val true A i δ v ρ) ∧
  (∀ b a A i δ v ρ, M.val b (.box a A) i δ v ρ →
     atLife δ a (fun α => box α (M.val b A i δ v)) ρ) ∧
  (∀ b a A i δ v ρ, M.val b (.imm a A) i δ v ρ →
     atLife δ a (fun α => ex fun ℓ => ⌜v = Val.loc ℓ ∧ CohE (rsOf i.1) ℓ A δ⌝ ⋆
       ptoImmSW M ℓ α i (fun i₀ => M.val false A i₀ δ)) ρ) ∧
  (∀ b a A i δ v ρ, M.val b (.mut a A) i δ v ρ →
     atLife δ a (fun α => ex fun ℓ => ⌜v = Val.loc ℓ⌝ ⋆
       ptoMutSW M ℓ α i (fun i₀ => M.val true A i₀ δ)) ρ) ∧
  (∀ b L i δ v ρ, M.val b (.fam L) i δ v ρ → ∃ ℓ c, v = Val.arr ℓ c ∧ c.toNat < 2 ^ 31 ∧
     sepRange (fun m => M.val b L i δ (Val.loc m)) ℓ c.toNat ρ) ∧
  (∀ b i δ v ρ, M.val b .unk i δ v ρ → ρ = PMap.empty) ∧
  (∀ b w i δ v ρ, M.val b (.int w) i δ v ρ → v.IsInt w ∧ ρ = PMap.empty) ∧
  (∀ b k i δ v ρ, M.val b (.opq k) i δ v ρ → k.Holds v ∧ ρ = PMap.empty) ∧
  (∀ b n i δ v ρ, ¬ M.val b (.tvar n) i δ v ρ)

/-- The eliminations and the shapes. -/
def RelLaws (M : B.BWorld) : Prop := RelElim M ∧ RelShape M

/-- **6.48 then 6.49 at W**, as `wpG_bind` composes two runs (`Core/EffWp.lean:910-911`): a run
from `ρ` at `i` ending at `i₁` with `π₁ = ρ′₁ ● ρ⁺₁`, then a run from `ρ′₁` at `i₁` ending at `i₂`
with `π₂`, together end at `i₂` with `ρ⁺₁ ● π₂`. -/
def UpdSeq (M : B.BWorld) : Prop :=
  ∀ (i i₁ i₂ : Idx M.Stk) (ρ ρ'₁ ρp₁ π₁ ρ'₂ π₂ π : WRes),
    M.Upd i i₁ ρ ρ'₁ π₁ → ResU.CompS ρ'₁ ρp₁ π₁ → M.Upd i₁ i₂ ρ'₁ ρ'₂ π₂ →
    ResU.Hash ρp₁ π₂ → ResU.CompS ρp₁ π₂ π → M.Upd i i₂ ρ ρ'₂ π

/-- **Reclaim at W** (`reclaim`, at `theorem32D`'s end): a run from the empty resource at σ = []
whose postcondition holds nothing leaves nothing borrowed, whatever index it ends at. -/
def UpdReclaim (M : B.BWorld) : Prop :=
  ∀ (i' : Idx M.Stk) (π : WRes),
    M.Upd ([], M.nil) i' PMap.empty PMap.empty π → NoOwn π → π = PMap.empty

/-- **6.47 at W** (as `wpG_here` reads `ResU.updV_self_iff`, `Core/EffWp.lean:969`): from a
configuration W reaches, a run that changes no cell ends at its own index with its resource as the
post and no garbage. -/
def UpdRefl (M : B.BWorld) : Prop :=
  ∀ (i : Idx M.Stk) (ρf ρ fρ : WRes) (ps : List FrameRec),
    ResU.Hash ρf ρ → ResU.CompS ρf ρ fρ → M.Fam fρ ps i → M.Upd i i ρ ρ ρ

/-- **The own-cell step at W** (`updV_compS_own`, as the alloc and free rules read it,
`Core/Wp.lean:606, 634`): from a configuration W reaches, a run that adds an own cell the frame
does not hold, or removes one, ends at its own index with the result as the post. -/
def UpdOwn (M : B.BWorld) : Prop :=
  (∀ (i : Idx M.Stk) (ρf ρ fρ ρ₁ : WRes) (ps : List FrameRec) (l : Loc) (v : Val),
    ResU.Hash ρf ρ → ResU.CompS ρf ρ fρ → M.Fam fρ ps i →
    ResU.CompS ρ (ResU.single l (CellU.ownOf v)) ρ₁ → ResU.Hash ρf ρ₁ → M.Upd i i ρ ρ₁ ρ₁) ∧
  (∀ (i : Idx M.Stk) (ρf ρ ρ₁ fρ₁ : WRes) (ps : List FrameRec) (l : Loc) (v : Val),
    ResU.Hash ρf ρ₁ → ResU.CompS ρf ρ₁ fρ₁ → M.Fam fρ₁ ps i →
    ResU.CompS ρ (ResU.single l (CellU.ownOf v)) ρ₁ → M.Upd i i ρ₁ ρ ρ)

/-- **6.48 into the post at W** (`updV_frame`, as `wpG_ramify` reads it,
`Core/EffWp.lean:1001`): a resource `ρ₂` framed through a run from `ρ₁` that ends at
`π₁ = ρ′₁ ● ρ⁺` is in the post, at the same two indices. -/
def UpdFrame (M : B.BWorld) : Prop :=
  ∀ (i i' : Idx M.Stk) (ρ₁ ρ₂ ρ ρ'₁ π₁ ρ' π : WRes),
    M.Upd i i' ρ₁ ρ'₁ π₁ → ResU.CompS ρ₂ ρ₁ ρ → ResU.Hash ρ₂ ρ₁ →
    ResU.CompS ρ₂ π₁ π → ResU.Hash ρ₂ π₁ → ResU.CompS ρ'₁ ρ₂ ρ' → M.Upd i i' ρ ρ' π

/-- **6.50 at W** (`updV_outlives`, as `wpTS_box` reads it, `Core/Wp.lean:805`): a run from a
resource that outlives `α` ends at one that does. -/
def UpdOutlives (M : B.BWorld) : Prop :=
  ∀ (i i' : Idx M.Stk) (ρ ρ' π : WRes) (α : Life),
    BoLo.Outlives ρ α → M.Upd i i' ρ ρ' π → BoLo.Outlives π α

/-- **6.27 then 6.28 at W**, as `wpG_M_frameX` reads them (`Core/EffWp.lean:441, 525`): a run
from `ρb ● ℓ ↦ mut(α, v, ρv, P̂)`, `@ρb ⊐ α`, ends with the lend back at the top of `π`, as
`ℓ ↦ mut(α, v′, χ, P̂)`; and the run with the lend unfolded at both ends, from `ρb ● ρv ● ℓ ↦ own(v)`
to `π/ℓ ● χ ● ℓ ↦ own(v′)`, its post the callback's with the cell unfolded into it, ends at the
same indices. -/
def UpdMutBack (M : B.BWorld) : Prop :=
  ∀ (i i' : Idx M.Stk) (l : Loc) (α : Life) (v : Val) (ρv ρb BM ρ' π : WRes)
    (h : ρv.InStratum α) (P : Val → SPropS Loc Val α) (hw : P v ⟨ρv, h⟩),
    BoLo.Outlives ρb α → ResU.CompS ρb (ResU.single l (CellU.mutOf α v ρv h P hw)) BM →
    M.Upd i i' BM ρ' π →
    ∃ (v' : Val) (χ : WRes) (h' : χ.InStratum α) (hw' : P v' ⟨χ, h'⟩),
      ResU.CompS (π.del l) (ResU.single l (CellU.mutOf α v' χ h' P hw')) π ∧
      ∀ (W W' O O' ρ'' : WRes), ResU.CompS ρv (ResU.single l (CellU.ownOf v)) W →
        ResU.CompS χ (ResU.single l (CellU.ownOf v')) W' → ResU.CompS ρb W O →
        ResU.CompS (π.del l) W' O' → ResU.CompS ρ' W' ρ'' → ResU.Valid O → ResU.Valid O' →
        M.Upd i i' O ρ'' O'

/-- **6.29, 6.38 and 6.39 at W**, as `wpG_I_frameX` reads them (`Core/EffWp.lean:174-240`): a
run from `ρb ● ℓ ↦ imm({α}, v, ρv)`, `@ρb ⊐ α`, ending at `π = ρ′ ● ρ⁺` with `@ρ′ ⊐ α` and `ρ⁺`
own-free, ends with the lend at the top of `π` (6.29), `π/ℓ` compatible with `ρv ● ℓ ↦ own(v)`
(6.38), and the run with the lend unfolded at both ends ends at the same indices (6.39). -/
def UpdImmBack (M : B.BWorld) : Prop :=
  ∀ (i i' : Idx M.Stk) (l : Loc) (α : Life) (v : Val) (ρv ρb W BI ρ' ρp π : WRes)
    (h : ρv.InStratum (LSet.singleton α).join),
    ResU.CompS ρv (ResU.single l (CellU.ownOf v)) W → ResU.Hash ρb W →
    BoLo.Outlives ρb α → BoLo.Outlives ρ' α → ResU.Hash ρ' ρp → NoOwn ρp →
    ResU.CompS ρb (ResU.single l (CellU.immOf (LSet.singleton α) v ρv h)) BI →
    ResU.CompS ρ' ρp π → M.Upd i i' BI ρ' π →
    ResU.CompS (π.del l) (ResU.single l (CellU.immOf (LSet.singleton α) v ρv h)) π ∧
    ResU.Hash (π.del l) W ∧
    ∀ (O O' ρ'' : WRes), ResU.CompS ρb W O → ResU.CompS (π.del l) W O' →
      ResU.CompS ρ' W ρ'' → M.Upd i i' O ρ'' O'

/-- **The lend comes back**, for both frame rules. -/
def UpdLendBack (M : B.BWorld) : Prop := UpdMutBack M ∧ UpdImmBack M


end Targets

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- **P9**: 6.60 at W, at both of the typing system's outlives judgments, both modes, every
index. -/
def LifetimeSound (M : B.BWorld) (O : OutJ) : Prop :=
  (∀ Δ δ a α T b i v ρ, LifeCtx.Models Δ δ → Lifetime.Life.interp δ a = some α → O.lt Δ a T →
     M.val b T i δ v ρ → BoLo.Outlives ρ α) ∧
  (∀ Δ δ a α T b i v ρ, LifeCtx.Models Δ δ → Lifetime.Life.interp δ a = some α → O.le Δ a T →
     M.val b T i δ v ρ → OutlivesLe ρ α)


end Targets

namespace Targets.B
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont Alloc ARun performE raiseE opPayload cancelVal)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- **B6, exclusive mutable borrows**: every configuration the world reaches is a valid resource
([CONF] 415:21: "Conceptually, in a valid resource, every pair of aliases map to the same object and
each has an immutable ancestor"). -/
def ExclusiveB (M : BWorld) : Prop := ∀ fρ ps i, M.Fam fρ ps i → ResU.Valid fρ

/-- **The nil slice has Core's structure**: configurations, order, run-end relation and payload
stack (FIX-RUN-END §2.2, the borrow fields).  Its `→` halves constrain OQ-44 (AGREE 10). -/
def SliceShapeB (M : BWorld) : Prop :=
  (∀ fρ ps ls, M.Fam fρ ps (ls, M.nil) ↔ TW fρ ps (rsOf ls) ∧ Tagged fρ ps ls) ∧
  (∀ ls ls' ρ, M.Ext (ls, M.nil) (ls', M.nil) ρ ↔ Ext ls ls' ρ) ∧
  (∀ ls ls' ρ ρ' π, M.Upd (ls, M.nil) (ls', M.nil) ρ ρ' π ↔ ResU.UpdV ρ π) ∧
  (∀ b, M.payStk b M.nil = M.nil)

/-- **The bounds of a borrow world**: the relation has Core's shape at each type former, and the
nil slice is Core's. -/
def WBound (M : BWorld) : Prop :=
  SliceShapeB M ∧ ExtPre M ∧ FamEmpty M ∧ DataVals M ∧ RelShape M ∧ RelElim M

/-- `RulesClosed J Row.NU` without its six effect conjuncts (`RC_effSub`, `RC_effPerform`,
`RC_effRaise`, `RC_effLet`, `RC_effThen`, `RC_effHandle`).  The borrow constants with a callback
row (`withbor1U` …) are kept: at a pure callback they are BoLo's. -/
def BorrowRulesClosed (J : TypingJ) : Prop :=
  RC_tensorI J ∧ RC_sumI₁ J ∧ RC_sumI₂ J ∧ RC_thunkF J ∧ RC_thunkV J ∧ RC_ret J ∧ RC_bind J ∧ RC_lam J ∧ RC_app J ∧ RC_withI J ∧ RC_proj₁ J ∧ RC_proj₂ J ∧ RC_unitE J ∧ RC_tensorE J ∧ RC_sumE J ∧ RC_zeroE J ∧ RC_allI J ∧ RC_allE J ∧ RC_bangThunkF J ∧ RC_bangThunkV J ∧ RC_bangE J ∧ RC_boxI J ∧ RC_boxE J ∧ RC_immSub J ∧ RC_mutSub J ∧ RC_withbor1U J ∧ RC_withbor2U J ∧ RC_withbor3U J ∧ RC_sliceBorrowMU J ∧ RC_sliceBorrowIU J ∧ RC_lolliE J ∧ RC_allEV J ∧ RC_ofRet J ∧ RC_roll J ∧ RC_unroll J ∧ RC_nuIn J ∧ RC_nuOut J ∧ RC_withbor2 J ∧ RC_sliceBorrowM J ∧ RC_sliceBorrowI J ∧ RC_withloadU J ∧ RC_foldImm J

theorem borrowRulesClosed_of_rulesClosed {J : TypingJ} {R : Row → Prop} (h : RulesClosed J R) :
    BorrowRulesClosed J := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, -, -, -, -, -, -, h43, h44, h45, h46, h47⟩ := h
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h43, h44, h45, h46, h47⟩

/-- **B0, BoLo's programs stay typed**: `J` holds today's unr-free judgements and is closed under
every rule of `CDerives` but its six effect rules.  The effect-free part of `ExtendsNU J`, which
stays in `I.Pins` with its effect rules. -/
def ExtendsB (J : TypingJ) : Prop := Tier1SubNU J ∧ BorrowRulesClosed J

/-- **The externs' contracts** (finding #7): their values are in W's relation at their types, at
the nil index, holding nothing.  Externs and unsafe code are outside the proofs by design (the
brief §6), so the contract is an explicit hypothesis of B4′ and B5, at the composite's world. -/
def ContractsW (M : BWorld) (Γ : Ctx VTy) (γ : List Val) : Prop :=
  gDenW M ([], M.nil) LSub.empty Γ γ (PMap.empty : WRes)

/-- **B4′**: with externs meeting their contracts, every run of a typed program is safe and
terminates with the memory empty. -/
def SoundContracts (J : TypingJ) (M : BWorld) : Prop :=
  ∀ P : Platform, P.Respects → ∀ (Γ : Ctx VTy) (γ : List Val) (S : Row) (A : VTy) (e : Expr),
    DivFree S A → RowLe S P.ops → J.at LifeCtx.empty Γ e (.comp (CTy.effOf S A)) →
    ContractsW M Γ γ →
    SafeRuns (ℍ := ℍ) P A (substAll γ e) ∧ Terminates (ℍ := ℍ) P A (substAll γ e)

/-- **B5, exactly-once release, location reuse included** (finding #2): every complete run of a
typed program is, step for step, the image of a complete bump run.  At step `k` a map `g k`,
injective on the bump run's live heap, renames the bump run's term to the run's and pushes its heap
onto the run's.  The bump run releases each cell exactly once (`ReleasedOnce`, which on a run that
reuses nothing follows from the empty memory at both ends); so the run releases each allocation
once, and a release through a name of an earlier allocation (a stale release) would be a release,
in the bump run, of a cell already released, which has no step.  A permutation cannot state this:
a run may still name a reused location from its first allocation (a dangling copy through an `Imm`
view, `VTy.immReborrow`), so the direction is `fresh_run_image`'s (TwoRun). -/
def ReleasedOnceReuse (J : TypingJ) (M : BWorld) : Prop :=
  ∀ (P : Platform), P.Respects → ∀ (Γ : Ctx VTy) (γ : List Val) (S : Row) (A : VTy) (e : Expr),
    DivFree S A → RowLe S P.ops → J.at LifeCtx.empty Γ e (.comp (CTy.effOf S A)) →
    ContractsW M Γ γ →
    ∀ cs, PRun (ℍ := ℍ) P (init P (substAll γ e) :: cs) →
      (∀ c, (init P (substAll γ e) :: cs).getLast? = some c → Final P A c) →
      ∃ (cs' : List (Conf P)) (g : ℕ → Loc → Loc),
        cs'.length = cs.length ∧ PRun (ℍ := ℍ) P (init P (substAll γ e) :: cs') ∧
        Bump (init P (substAll γ e) :: cs') ∧ ReleasedOnce (init P (substAll γ e) :: cs') ∧
        (∀ c, (init P (substAll γ e) :: cs').getLast? = some c → Final P A c) ∧
        ∀ k (cA cB : Conf P), (init P (substAll γ e) :: cs)[k]? = some cA →
          (init P (substAll γ e) :: cs')[k]? = some cB → RelAt (g k) cA cB

/-- B5 at closed programs: it reads no world. -/
def ReleasedOnceReuse₀ (J : TypingJ) : Prop :=
  ∀ (P : Platform), P.Respects → ∀ (S : Row) (A : VTy) (e : Expr),
    DivFree S A → RowLe S P.ops → J.closed e (CTy.effOf S A) →
    ∀ cs, PRun (ℍ := ℍ) P (init P e :: cs) → (∀ c, (init P e :: cs).getLast? = some c → Final P A c) →
      ∃ (cs' : List (Conf P)) (g : ℕ → Loc → Loc),
        cs'.length = cs.length ∧ PRun (ℍ := ℍ) P (init P e :: cs') ∧ Bump (init P e :: cs') ∧
        ReleasedOnce (init P e :: cs') ∧ (∀ c, (init P e :: cs').getLast? = some c → Final P A c) ∧
        ∀ k (cA cB : Conf P), (init P e :: cs)[k]? = some cA → (init P e :: cs')[k]? = some cB →
          RelAt (g k) cA cB

/-- **BoLo's guarantees** for the typing system `J` at the borrow world `M`: B0 (BoLo's programs
stay typed), B1 (the fundamental property), B2 (adequacy), B3 and B4 (no use after free, no double
free, leak freedom), B4′ (the same with externs meeting their contracts), B5 (exactly-once release,
location reuse included), B6 (exclusive mutable borrows), B7 (lifetimes respected), and the bounds.
"Nothing breaks the borrow calculus" is that these hold in the composite. -/
def Guarantees (J : TypingJ) (M : BWorld) : Prop :=
  ExtendsB J ∧ FL M J ∧ Adequate (ℍ := ℍ) M ∧ Sound (ℍ := ℍ) J ∧ SoundContracts (ℍ := ℍ) J M ∧
    ReleasedOnceReuse (ℍ := ℍ) J M ∧ ExclusiveB M ∧ LifetimeSound M J.out ∧ WBound M


end Targets.B

end
