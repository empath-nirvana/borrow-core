import Targets.Defs.World
import Targets.Defs.Typing
import Targets.Defs.Runs

/-!
# Targets — the proof device: the fundamental lemma at W and the laws of W (DESIGN §4)

**World:** [W], at the end state's `M`.

* `FL M J`: every judgment of the typing system holds in W's relation, at every admissible
  instance ([TR] 6.151's shape).
* `Adequate M`: a closed computation in W's relation is safe and terminating under every platform
  (or safely driven).  Soundness is a corollary of FL and adequacy (`SoundnessOfFL`,
  `Statements/Composition.lean`).
* `WLaws M`: the laws every W satisfies.  Together they bound the relation from above by W's runs
  at every index and every type former: data values are exactly data (`DataVals`), a computation
  of `F_Σ A` at an unr-free row is exactly W's runs (`EffInterp`), every other former is bounded
  by its eliminations and its shape (`RelLaws`; at `Imm` and `Mut` by Core's own clauses, with W's
  relation for the payload), and every run from every configuration W reaches is safe
  (`AdequateEvery`).  W's runs end under `M.Upd`.

`SliceShape` pins the nil slice only structurally: the configurations, the order, the stop and the
run-end relation at σ = [] are Core's.  The `Upd` pin's `←` half puts Core's runs in W's
(`wpGW_of_wpG_nil`, `Restricted/CoreLaws.lean`).  Its `→` half bounds run ends from the nil slice
to the nil slice, and not W's runs: a run picks its end index, and one from σ = [] may end off the
nil slice.  `SliceShape` does not ask W's relation at σ = [] to equal Core's (DESIGN §4.2): the
embedding of Core's relation into W is `ConservativeWB` (`Statements/Conservativity.lean`).

**Beside `WLaws`, not in it.**  `AdequateOfLaws` (`Statements/Composition.lean`) asks two laws of
the run-end relation: `UpdSeq` (6.48 then 6.49, as `wpG_bind` composes two runs) and `UpdReclaim`
(`reclaim`, at `theorem32D`'s end).  FL's printed route reads `↭` through 6.47, the own-cell step,
6.48 into the post, 6.50, and the lend coming back (6.27–6.29, 6.38, 6.39); their forms at W,
stated at every pair of indices, are `UpdRefl`, `UpdOwn`, `UpdFrame`, `UpdOutlives`, `UpdMutBack`
and `UpdImmBack`.  Each holds where `Upd` is Core's at every index (`Restricted/CoreLaws.lean`).
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
  | .eff _ _ q A B C => (B.isZero && q != .lin) = true ∧ A.AbortRows ∧ B.AbortRows ∧ C.AbortRows
end

end BoCa.Fig16.LogRel.Core

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### FL and adequacy (DESIGN §4.1) -/

/-- **The fundamental lemma at W**: every judgment of `J` holds in W's relation. -/
def FL (M : SemWorld) (J : TypingJ) : Prop := ∀ Θ Δ Γ e j, J Θ Δ Γ e j → SemW M Θ Δ Γ e j

/-- Adequacy at a platform, for programs at a div-free answer. -/
def AdequateRetAt (M : SemWorld) (P : Platform) : Prop :=
  ∀ (S : Row) (A : VTy) (e : Expr), DivFree S A → RowLe S P.ops →
    M.comp (CTy.effOf S A) ([], M.nil) LSub.empty e (PMap.empty : WRes) →
    SafeRuns (ℍ := ℍ) P A e ∧ Terminates (ℍ := ℍ) P A e

/-- Adequacy at a platform, for programs that return a loop. -/
def AdequateDriveAt (M : SemWorld) (P : Platform) : Prop :=
  ∀ (S : Row) (A B : VTy) (e : Expr), A.Data → RowLe S P.ops →
    M.comp (CTy.effOf S (.thunk (CTy.loopEff S A B))) ([], M.nil) LSub.empty e
      (PMap.empty : WRes) →
    SafeDrive (ℍ := ℍ) P A e

/-- Adequacy at a platform. -/
def AdequateAt (M : SemWorld) (P : Platform) : Prop :=
  AdequateRetAt (ℍ := ℍ) M P ∧ AdequateDriveAt (ℍ := ℍ) M P

/-- **Adequacy**: at every platform that respects its protocol. -/
def Adequate (M : SemWorld) : Prop := ∀ P : Platform, P.Respects → AdequateAt (ℍ := ℍ) M P

/-! ### The laws every W satisfies (DESIGN §4.2) -/

/-- **The nil slice, structurally**: at σ = [] nothing is held, the configurations, the order, the
stop and the run-end relation are Core's, and a stored payload is read at σ = []. -/
def SliceShape (M : SemWorld) : Prop :=
  (∀ ls, M.held (ls, M.nil) = ([], [])) ∧
  (∀ fρ ps ls, M.Fam fρ ps (ls, M.nil) ↔ TW fρ ps (rsOf ls) ∧ Tagged fρ ps ls) ∧
  (∀ ls ls' ρ, M.Ext (ls, M.nil) (ls', M.nil) ρ ↔ Ext ls ls' ρ) ∧
  (∀ ps ls ps' ls' t, M.Stop (ps, (ls, M.nil)) (ps', (ls', M.nil)) t ↔
     (∀ p, p ∈ ps' ↔ p ∈ ps) ∧ (∀ x, x ∈ ls' ↔ x ∈ ls)) ∧
  (∀ ls ls' ρ ρ' π, M.Upd (ls, M.nil) (ls', M.nil) ρ ρ' π ↔ ResU.UpdV ρ π) ∧
  (∀ b, M.payStk b M.nil = M.nil)

/-- **Mono**: Kripke monotonicity of the value relation, in both modes. -/
def Mono (M : SemWorld) : Prop :=
  ∀ b A i i' δ v ρ, M.Ext i i' ρ → M.val b A i δ v ρ → M.val b A i' δ v ρ

/-- The Kripke order is a preorder. -/
def ExtPre (M : SemWorld) : Prop :=
  (∀ i ρ, M.Ext i i ρ) ∧ (∀ i i' i'' ρ, M.Ext i i' ρ → M.Ext i' i'' ρ → M.Ext i i'' ρ)

/-- **EffInterp**: an unr-free row is read through its protocol ("opTable is the
interpretation"). -/
def EffInterp (M : SemWorld) : Prop :=
  ∀ S R i δ e ρ, Row.NU S → (M.comp (CTy.effOf S R) i δ e ρ ↔
    ewpW (ℍ := ℍ) M i e (opTabW M (rowTabW M S δ)) (fun j v => M.val true R j δ v) ρ)

/-- The empty configuration is reached at the nil index. -/
def FamEmpty (M : SemWorld) : Prop := M.Fam (PMap.empty : WRes) [] ([], M.nil)

/-- Data values are exactly data, and hold nothing. -/
def DataVals (M : SemWorld) : Prop :=
  ∀ b A i δ v ρ, A.Data → (M.val b A i δ v ρ ↔ ρ = PMap.empty ∧ DataVal A v)

/-- The share is monotone in what it owes, at non-`unr` entries. -/
def ShareMono (M : SemWorld) : Prop :=
  ∀ T en n i K (Φ Φ' : Idx M.Stk → Expr → WProp) ρ, en.q ≠ .unr →
    (∀ i e ρ, Φ i e ρ → Φ' i e ρ) → M.share T en n i K Φ ρ → M.share T en n i K Φ' ρ

/-- The eliminations, at the same index.  None has an `M.Ext` quantifier, so each holds under
either option of OQ-8. -/
def RelElim (M : SemWorld) : Prop :=
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
def RelShape (M : SemWorld) : Prop :=
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
def RelLaws (M : SemWorld) : Prop := RelElim M ∧ RelShape M

/-- **Adequacy from every index**: from every configuration W reaches, every run of a computation
in W's relation at an unr-free row continues to a value or to a stop of the row. -/
def AdequateEvery (M : SemWorld) : Prop :=
  ∀ (i : Idx M.Stk) (fρ ρf ρ : WRes) (ps : List FrameRec) (μ : Heap) (S : Row) (A : VTy)
    (δ : LSub) (e : Expr), Row.NU S →
    M.Fam fρ ps i → ResU.Hash ρf ρ → ResU.CompS ρf ρ fρ → ResU.Lower fρ μ →
    M.comp (CTy.effOf S A) i δ e ρ →
    ∀ μ₁ e₁, Steps (ℍ := ℍ) μ e μ₁ e₁ →
      ∃ μ₂ e₂, Steps (ℍ := ℍ) μ₁ e₁ μ₂ e₂ ∧ (IsVal e₂ ∨ StopsIn S e₂)

/-- **The laws every W satisfies.** -/
def WLaws (M : SemWorld) : Prop :=
  SliceShape M ∧ Mono M ∧ ExtPre M ∧ EffInterp (ℍ := ℍ) M ∧ FamEmpty M ∧ DataVals M ∧
  ShareMono M ∧ RelLaws M ∧ AdequateEvery (ℍ := ℍ) M

/-- What `Mono` needs at `U` when the future-world quantifier sits at the binder clauses
(OQ-8). -/
def EwpMono (M : SemWorld) : Prop :=
  ∀ i i' e Tb Q ρ, TableI.Mono Tb → M.Ext i i' ρ → ewpW (ℍ := ℍ) M i e Tb Q ρ →
    ewpW (ℍ := ℍ) M i' e Tb Q ρ

/-! ### The run-end relation's laws, beside `WLaws` and not in it

`UpdSeq` and `UpdReclaim` are hypotheses of `AdequateOfLaws`.  The others are the W-level forms of
the `↭` lemmas FL's printed route reads, stated at every pair of indices in the shape Core's
proofs read them.  None is a conjunct of done. -/

/-- **6.48 then 6.49 at W**, as `wpG_bind` composes two runs (`Core/EffWp.lean:910-911`): a run
from `ρ` at `i` ending at `i₁` with `π₁ = ρ′₁ ● ρ⁺₁`, then a run from `ρ′₁` at `i₁` ending at `i₂`
with `π₂`, together end at `i₂` with `ρ⁺₁ ● π₂`. -/
def UpdSeq (M : SemWorld) : Prop :=
  ∀ (i i₁ i₂ : Idx M.Stk) (ρ ρ'₁ ρp₁ π₁ ρ'₂ π₂ π : WRes),
    M.Upd i i₁ ρ ρ'₁ π₁ → ResU.CompS ρ'₁ ρp₁ π₁ → M.Upd i₁ i₂ ρ'₁ ρ'₂ π₂ →
    ResU.Hash ρp₁ π₂ → ResU.CompS ρp₁ π₂ π → M.Upd i i₂ ρ ρ'₂ π

/-- **Reclaim at W** (`reclaim`, at `theorem32D`'s end): a run from the empty resource at σ = []
whose postcondition holds nothing leaves nothing borrowed, whatever index it ends at. -/
def UpdReclaim (M : SemWorld) : Prop :=
  ∀ (i' : Idx M.Stk) (π : WRes),
    M.Upd ([], M.nil) i' PMap.empty PMap.empty π → NoOwn π → π = PMap.empty

/-- **6.47 at W** (as `wpG_here` reads `ResU.updV_self_iff`, `Core/EffWp.lean:969`): from a
configuration W reaches, a run that changes no cell ends at its own index with its resource as the
post and no garbage. -/
def UpdRefl (M : SemWorld) : Prop :=
  ∀ (i : Idx M.Stk) (ρf ρ fρ : WRes) (ps : List FrameRec),
    ResU.Hash ρf ρ → ResU.CompS ρf ρ fρ → M.Fam fρ ps i → M.Upd i i ρ ρ ρ

/-- **The own-cell step at W** (`updV_compS_own`, as the alloc and free rules read it,
`Core/Wp.lean:606, 634`): from a configuration W reaches, a run that adds an own cell the frame
does not hold, or removes one, ends at its own index with the result as the post. -/
def UpdOwn (M : SemWorld) : Prop :=
  (∀ (i : Idx M.Stk) (ρf ρ fρ ρ₁ : WRes) (ps : List FrameRec) (l : Loc) (v : Val),
    ResU.Hash ρf ρ → ResU.CompS ρf ρ fρ → M.Fam fρ ps i →
    ResU.CompS ρ (ResU.single l (CellU.ownOf v)) ρ₁ → ResU.Hash ρf ρ₁ → M.Upd i i ρ ρ₁ ρ₁) ∧
  (∀ (i : Idx M.Stk) (ρf ρ ρ₁ fρ₁ : WRes) (ps : List FrameRec) (l : Loc) (v : Val),
    ResU.Hash ρf ρ₁ → ResU.CompS ρf ρ₁ fρ₁ → M.Fam fρ₁ ps i →
    ResU.CompS ρ (ResU.single l (CellU.ownOf v)) ρ₁ → M.Upd i i ρ₁ ρ ρ)

/-- **6.48 into the post at W** (`updV_frame`, as `wpG_ramify` reads it,
`Core/EffWp.lean:1001`): a resource `ρ₂` framed through a run from `ρ₁` that ends at
`π₁ = ρ′₁ ● ρ⁺` is in the post, at the same two indices. -/
def UpdFrame (M : SemWorld) : Prop :=
  ∀ (i i' : Idx M.Stk) (ρ₁ ρ₂ ρ ρ'₁ π₁ ρ' π : WRes),
    M.Upd i i' ρ₁ ρ'₁ π₁ → ResU.CompS ρ₂ ρ₁ ρ → ResU.Hash ρ₂ ρ₁ →
    ResU.CompS ρ₂ π₁ π → ResU.Hash ρ₂ π₁ → ResU.CompS ρ'₁ ρ₂ ρ' → M.Upd i i' ρ ρ' π

/-- **6.50 at W** (`updV_outlives`, as `wpTS_box` reads it, `Core/Wp.lean:805`): a run from a
resource that outlives `α` ends at one that does. -/
def UpdOutlives (M : SemWorld) : Prop :=
  ∀ (i i' : Idx M.Stk) (ρ ρ' π : WRes) (α : Life),
    BoLo.Outlives ρ α → M.Upd i i' ρ ρ' π → BoLo.Outlives π α

/-- **6.27 then 6.28 at W**, as `wpG_M_frameX` reads them (`Core/EffWp.lean:441, 525`): a run
from `ρb ● ℓ ↦ mut(α, v, ρv, P̂)`, `@ρb ⊐ α`, ends with the lend back at the top of `π`, as
`ℓ ↦ mut(α, v′, χ, P̂)`; and the run with the lend unfolded at both ends, from `ρb ● ρv ● ℓ ↦ own(v)`
to `π/ℓ ● χ ● ℓ ↦ own(v′)`, its post the callback's with the cell unfolded into it, ends at the
same indices. -/
def UpdMutBack (M : SemWorld) : Prop :=
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
def UpdImmBack (M : SemWorld) : Prop :=
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
def UpdLendBack (M : SemWorld) : Prop := UpdMutBack M ∧ UpdImmBack M

end Targets

end
